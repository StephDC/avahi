/***
  This file is part of avahi.

  avahi is free software; you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation; either version 2.1 of the
  License, or (at your option) any later version.

  avahi is distributed in the hope that it will be useful, but WITHOUT
  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
  or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
  Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with avahi; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
  USA.
***/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <locale.h>
#include <getopt.h>

/*** Includes for sshpass ***/
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <termios.h>

#define PASSWORD_PROMPT "assword"
enum program_return_codes {
    RETURN_NOERROR,
    RETURN_INVALID_ARGUMENTS,
    RETURN_CONFLICTING_ARGUMENTS,
    RETURN_RUNTIME_ERROR,
    RETURN_PARSE_ERRROR,
    RETURN_INCORRECT_PASSWORD,
    RETURN_HOST_KEY_UNKNOWN,
    RETURN_HOST_KEY_CHANGED,
    RETURN_HELP,
};
int sshpass(char *pwd, char *p, char *u, char*h);
void window_resize_handler(int signum);
void sigchld_handler(int signum);
void term_handler(int signum);
void term_child(int signum);
void reliable_write(int fd, const void *data, ssize_t size);
int match( const char *reference, const char *buffer, ssize_t bufsize, int state );
int handleoutput(int fd, char *pwd);
const char *runargv[8];

#include <gtk/gtk.h>

#include <avahi-client/client.h>
#include <avahi-common/strlst.h>
#include <avahi-common/malloc.h>
#include <avahi-common/domain.h>
#include <avahi-common/i18n.h>

#include "avahi-ui.h"

typedef enum {
    COMMAND_HELP,
    COMMAND_SSH,
    COMMAND_VNC,
    COMMAND_SHELL
} Command;

typedef struct Config {
    char *domain;
    Command command;
} Config;

static void help(FILE *f, const char *argv0) {
    fprintf(f,
            _("%s [options]\n\n"
              "    -h --help            Show this help\n"
              "    -s --ssh             Browse SSH servers\n"
              "    -v --vnc             Browse VNC servers\n"
              "    -S --shell           Browse both SSH and VNC\n"
              "    -d --domain=DOMAIN   The domain to browse in\n"),
            argv0);
}

static int parse_command_line(Config *c, int argc, char *argv[]) {
    int o;

    static const struct option long_options[] = {
        { "help",           no_argument,       NULL, 'h' },
        { "ssh",            no_argument,       NULL, 's' },
        { "vnc",            no_argument,       NULL, 'v' },
        { "shell",          no_argument,       NULL, 'S' },
        { "domain",         required_argument, NULL, 'd' },
        { NULL, 0, NULL, 0 }
    };

    while ((o = getopt_long(argc, argv, "hVd:svS", long_options, NULL)) >= 0) {

        switch(o) {
            case 'h':
                c->command = COMMAND_HELP;
                break;
            case 's':
                c->command = COMMAND_SSH;
                break;
            case 'v':
                c->command = COMMAND_VNC;
                break;
            case 'S':
                c->command = COMMAND_SHELL;
                break;
            case 'd':
                avahi_free(c->domain);
                c->domain = avahi_strdup(optarg);
                break;
            default:
                return -1;
        }
    }

    if (optind < argc) {
        fprintf(stderr, _("Too many arguments\n"));
        return -1;
    }

    return 0;
}

/* Logic from sshpass */
/* Global variables so that this information be shared with the signal handler */
static int ourtty; // Our own tty
static int masterpt;

int childpid;
int termsig;

int sshpass(char *pwd, char *p, char *u, char*h)
{
    struct winsize ttysize; // The size of our tty
    const char *name;
    int slavept;

    // We need to interrupt a select with a SIGCHLD. In order to do so, we need a SIGCHLD handler
    signal( SIGCHLD, sigchld_handler );

    // Create a pseudo terminal for our process
    masterpt=posix_openpt(O_RDWR);

    if( masterpt==-1 ) {
        perror("Failed to get a pseudo terminal");

        return RETURN_RUNTIME_ERROR;
    }

    fcntl(masterpt, F_SETFL, O_NONBLOCK);

    if( grantpt( masterpt )!=0 ) {
        perror("Failed to change pseudo terminal's permission");

        return RETURN_RUNTIME_ERROR;
    }
    if( unlockpt( masterpt )!=0 ) {
        perror("Failed to unlock pseudo terminal");

        return RETURN_RUNTIME_ERROR;
    }

    ourtty=open("/dev/tty", 0);
    if( ourtty!=-1 && ioctl( ourtty, TIOCGWINSZ, &ttysize )==0 ) {
        signal(SIGWINCH, window_resize_handler);

        ioctl( masterpt, TIOCSWINSZ, &ttysize );
    }
    name = ptsname(masterpt);
    /*
       Comment no. 3.14159

       This comment documents the history of code.

       We need to open the slavept inside the child process, after "setsid", so that it becomes the controlling
       TTY for the process. We do not, otherwise, need the file descriptor open. The original approach was to
       close the fd immediately after, as it is no longer needed.

       It turns out that (at least) the Linux kernel considers a master ptty fd that has no open slave fds
       to be unused, and causes "select" to return with "error on fd". The subsequent read would fail, causing us
       to go into an infinite loop. This is a bug in the kernel, as the fact that a master ptty fd has no slaves
       is not a permenant problem. As long as processes exist that have the slave end as their controlling TTYs,
       new slave fds can be created by opening /dev/tty, which is exactly what ssh is, in fact, doing.

       Our attempt at solving this problem, then, was to have the child process not close its end of the slave
       ptty fd. We do, essentially, leak this fd, but this was a small price to pay. This worked great up until
       openssh version 5.6.

       Openssh version 5.6 looks at all of its open file descriptors, and closes any that it does not know what
       they are for. While entirely within its prerogative, this breaks our fix, causing sshpass to either
       hang, or do the infinite loop again.

       Our solution is to keep the slave end open in both parent AND child, at least until the handshake is
       complete, at which point we no longer need to monitor the TTY anyways.
     */

    sigset_t sigmask, sigmask_select;

    // Set the signal mask during the select
    sigemptyset(&sigmask_select);

    // And during the regular run
    sigemptyset(&sigmask);
    sigaddset(&sigmask, SIGCHLD);
    sigaddset(&sigmask, SIGHUP);
    sigaddset(&sigmask, SIGTERM);
    sigaddset(&sigmask, SIGINT);
    sigaddset(&sigmask, SIGTSTP);

    sigprocmask( SIG_SETMASK, &sigmask, NULL );

    signal(SIGHUP, term_handler);
    signal(SIGTERM, term_handler);
    signal(SIGINT, term_handler);
    signal(SIGTSTP, term_handler);

    childpid=fork();
    if( childpid==0 ) {
        // Child

        // Re-enable all signals to child
        sigprocmask( SIG_SETMASK, &sigmask_select, NULL );

        // Detach us from the current TTY
        setsid();

        // Attach the process to a controlling TTY.
        slavept=open(name, O_RDWR | O_NOCTTY);
        // On some systems, an open(2) is insufficient to set the controlling tty (see the documentation for
        // TIOCSCTTY in tty(4)).
        if (ioctl(slavept, TIOCSCTTY, 0) == -1) {
            perror("sshpass: Failed to set controlling terminal in child (TIOCSCTTY)");
            exit(RETURN_RUNTIME_ERROR);
        }
        close( slavept ); // We don't need the controlling TTY actually open

        close( masterpt );

	execlp( "ssh", "ssh", "-o", "PreferredAuthentications=password", "-p", p, "-l", u, h, NULL);

        perror("SSHPASS: Failed to run command");

        exit(RETURN_RUNTIME_ERROR);
    } else if( childpid<0 ) {
        perror("SSHPASS: Failed to create child process");

        return RETURN_RUNTIME_ERROR;
    }

    // We are the parent
    slavept=open(name, O_RDWR|O_NOCTTY );

    int status=0;
    int terminate=0;
    pid_t wait_id;

    do {
        if( !terminate ) {
            fd_set readfd;

            FD_ZERO(&readfd);
            FD_SET(masterpt, &readfd);

            int selret=pselect( masterpt+1, &readfd, NULL, NULL, NULL, &sigmask_select );

            if( termsig!=0 ) {
                // Copying termsig isn't strictly necessary, as signals are masked at this point.
                int signum = termsig;
                termsig = 0;

                term_child(signum);

                continue;
            }

            if( selret>0 ) {
                if( FD_ISSET( masterpt, &readfd ) ) {
                    int ret;
                    if( (ret=handleoutput( masterpt, pwd )) ) {
                        // Authentication failed or any other error

                        // handleoutput returns positive error number in case of some error, and a negative value
                        // if all that happened is that the slave end of the pt is closed.
                        if( ret>0 ) {
                            close( masterpt ); // Signal ssh that it's controlling TTY is now closed
                            close(slavept);
                        }

                        terminate=ret;

                        if( terminate ) {
                            close( slavept );
                        }
                    }
                }
            }
            wait_id=waitpid( childpid, &status, WNOHANG );
        } else {
            wait_id=waitpid( childpid, &status, 0 );
        }
    } while( wait_id==0 || (!WIFEXITED( status ) && !WIFSIGNALED( status )) );

    if( terminate>0 )
        return terminate;
    else if( WIFEXITED( status ) )
        return WEXITSTATUS(status);
    else
        return 255;
}

int handleoutput( int fd, char *pwd )
{
    // We are looking for the string
    static int prevmatch=0; // If the "password" prompt is repeated, we have the wrong password.
    static int state0, state1, state2, state3;
    static int firsttime = 1;
    static const char compare0[]="passphrase for key";
    static const char *compare1=PASSWORD_PROMPT; // Asking for a password
    static const char compare2[]="The authenticity of host "; // Asks to authenticate host
    static const char compare3[] = "differs from the key for the IP address"; // Key changes
    // static const char compare3[]="WARNING: REMOTE HOST IDENTIFICATION HAS CHANGED!"; // Warns about man in the middle attack
    // The remote identification changed error is sent to stderr, not the tty, so we do not handle it.
    // This is not a problem, as ssh exists immediately in such a case
    char buffer[256];
    int ret=0;
    int numread;

    if( firsttime ) {
        firsttime=0;
        fprintf(stderr, "SSHPASS: searching for password prompt using match \"%s\"\n", compare1);
    }

    numread=read(fd, buffer, sizeof(buffer)-1 );
    buffer[numread] = '\0';

    state0=match( compare0, buffer, numread, state0 );

    if( compare0[state0]=='\0'){
	    fprintf(stderr, "SSHPASS: detected key prompt. Skipping.\n");
	    reliable_write( fd, "\n", 1 );
    }

    // Are we at a password prompt?
    state1=match( compare1, buffer, numread, state1 );

    if( compare1[state1]=='\0' ) {
        if( !prevmatch ) {
            fprintf(stderr, "SSHPASS: detected prompt. Sending password.\n");
	    reliable_write( fd, pwd, strlen( pwd ) );
	    reliable_write( fd, "\n", 1 );
            state1=0;
            prevmatch=1;
        } else {
            // Wrong password - terminate with proper error code
            fprintf(stderr, "SSHPASS: detected prompt, again. Wrong password. Terminating.\n");
            ret=RETURN_INCORRECT_PASSWORD;
        }
    }

    if( ret==0 ) {
        state2=match( compare2, buffer, numread, state2 );

        // Are we being prompted to authenticate the host?
        if( compare2[state2]=='\0' ) {
            fprintf(stderr, "SSHPASS: detected host authentication prompt. Exiting.\n");
            ret=RETURN_HOST_KEY_UNKNOWN;
        } else {
            state3 = match( compare3, buffer, numread, state3 );
            // Host key changed
            if ( compare3[state3]=='\0' ) {
                ret=RETURN_HOST_KEY_CHANGED;
            }
        }
    }

    return ret;
}

int match( const char *reference, const char *buffer, ssize_t bufsize, int state )
{
    // This is a highly simplisic implementation. It's good enough for matching "Password: ", though.
    int i;
    for( i=0;reference[state]!='\0' && i<bufsize; ++i ) {
        if( reference[state]==buffer[i] )
            state++;
        else {
            state=0;
            if( reference[state]==buffer[i] )
                state++;
        }
    }

    return state;
}

void window_resize_handler(int signum)
{
    struct winsize ttysize; // The size of our tty

    if( ioctl( ourtty, TIOCGWINSZ, &ttysize )==0 )
        ioctl( masterpt, TIOCSWINSZ, &ttysize );
}

// Do nothing handler - makes sure the select will terminate if the signal arrives, though.
void sigchld_handler(int signum)
{
}

void term_handler(int signum)
{
    // BUG: There is a potential race here if two signals arrive before the main code had a chance to handle them.
    // This seems low enough risk not to justify the extra code to correctly handle this.
    termsig = signum;
}

void term_child(int signum)
{
    fflush(stdout);
    switch(signum) {
    case SIGINT:
        reliable_write(masterpt, "\x03", 1);
        break;
    case SIGTSTP:
        reliable_write(masterpt, "\x1a", 1);
        break;
    default:
        if( childpid>0 ) {
            kill( childpid, signum );
        }
    }
}

void reliable_write( int fd, const void *data, ssize_t size )
{
    ssize_t result = write( fd, data, size );
    if( result!=size ) {
        if( result<0 ) {
            perror("SSHPASS: write failed");
        } else {
            fprintf(stderr, "SSHPASS: Short write. Tried to write %lu, only wrote %ld\n", size, result);
        }
    }
}

int main(int argc, char*argv[]) {
    GtkWidget *d;
    Config config;
    const char *argv0;

    avahi_init_i18n();
    setlocale(LC_ALL, "");

    if ((argv0 = strrchr(argv[0], '/')))
        argv0++;
    else
        argv0 = argv[0];

    if (g_str_has_suffix(argv[0], "bshell"))
        config.command = COMMAND_SHELL;
    else if (g_str_has_suffix(argv[0], "bvnc"))
        config.command = COMMAND_VNC;
    else
        config.command = COMMAND_SSH;

    /* defaults to local */
    config.domain = NULL;

    if (parse_command_line(&config, argc, argv) < 0) {
        help(stderr, argv0);
        return 1;
    }

    bindtextdomain (GETTEXT_PACKAGE, GNOMELOCALEDIR);
    bind_textdomain_codeset (GETTEXT_PACKAGE, "UTF-8");
    textdomain (GETTEXT_PACKAGE);

    gtk_init(&argc, &argv);

    switch (config.command) {
        case COMMAND_HELP:
            help(stdout, argv0);
            return 0;
            break;

        case COMMAND_SHELL:
            d = aui_service_dialog_new(_("Choose Shell Server"), NULL, _("_Cancel"), GTK_RESPONSE_CANCEL, _("C_onnect"), GTK_RESPONSE_ACCEPT, NULL);
            aui_service_dialog_set_browse_service_types(AUI_SERVICE_DIALOG(d), "_rfb._tcp", "_ssh._tcp", NULL);
            aui_service_dialog_set_service_type_name(AUI_SERVICE_DIALOG(d), "_rfb._tcp", _("Desktop"));
            aui_service_dialog_set_service_type_name(AUI_SERVICE_DIALOG(d), "_ssh._tcp", _("Terminal"));
            break;

        case COMMAND_VNC:
            d = aui_service_dialog_new(_("Choose VNC server"), NULL, _("_Cancel"), GTK_RESPONSE_CANCEL, _("C_onnect"), GTK_RESPONSE_ACCEPT, NULL);
            aui_service_dialog_set_browse_service_types(AUI_SERVICE_DIALOG(d), "_rfb._tcp", NULL);
            break;

        case COMMAND_SSH:
            d = aui_service_dialog_new(_("Choose SSH server"), NULL, _("_Cancel"), GTK_RESPONSE_CANCEL, _("C_onnect"), GTK_RESPONSE_ACCEPT, NULL);
            aui_service_dialog_set_browse_service_types(AUI_SERVICE_DIALOG(d), "_ssh._tcp", NULL);
            break;
    }

    aui_service_dialog_set_domain (AUI_SERVICE_DIALOG(d), config.domain);
    aui_service_dialog_set_resolve_service(AUI_SERVICE_DIALOG(d), TRUE);
    aui_service_dialog_set_resolve_host_name(AUI_SERVICE_DIALOG(d), !avahi_nss_support());

    gtk_window_present(GTK_WINDOW(d));

    if (gtk_dialog_run(GTK_DIALOG(d)) == GTK_RESPONSE_ACCEPT) {
        char a[AVAHI_ADDRESS_STR_MAX], *u = NULL, *n = NULL, *pwd = NULL;
        char *h = NULL, *t = NULL;
        const AvahiStringList *txt;

        t = g_strdup(aui_service_dialog_get_service_type(AUI_SERVICE_DIALOG(d)));
        n = g_strdup(aui_service_dialog_get_service_name(AUI_SERVICE_DIALOG(d)));

        if (avahi_nss_support())
            h = g_strdup(aui_service_dialog_get_host_name(AUI_SERVICE_DIALOG(d)));
        else
            h = g_strdup(avahi_address_snprint(a, sizeof(a), aui_service_dialog_get_address(AUI_SERVICE_DIALOG(d))));

        g_print(_("Connecting to '%s' ...\n"), n);

        if (avahi_domain_equal(t, "_rfb._tcp")) {
            char p[AVAHI_DOMAIN_NAME_MAX+16];
            snprintf(p, sizeof(p), "%s:%u", h, aui_service_dialog_get_port(AUI_SERVICE_DIALOG(d))-5900);

            gtk_widget_destroy(d);

            g_print("vncviewer %s\n", p);
            execlp("xvncviewer", "xvncviewer", p, NULL);
            execlp("vncviewer", "vncviewer", p, NULL);

        } else {
            char p[16];

            snprintf(p, sizeof(p), "%u", aui_service_dialog_get_port(AUI_SERVICE_DIALOG(d)));

            for (txt = aui_service_dialog_get_txt_data(AUI_SERVICE_DIALOG(d)); txt; txt = txt->next) {
                char *key, *value;

                if (avahi_string_list_get_pair((AvahiStringList*) txt, &key, &value, NULL) < 0)
                    break;

                if (strcmp(key, "u") == 0)
                    u = g_strdup(value);

		if (strcmp(key, "p") == 0)
			pwd = g_strdup(value);

                avahi_free(key);
                avahi_free(value);
            }

            gtk_widget_destroy(d);

            if (u) {
		    if (pwd){
			//g_print("sshpass -p %s ssh -p %s %s@%s\n", pwd, p, u, h);

			// Now call the sshpass segment of code...
			if (isatty(0) || !getenv("DISPLAY"))
				return sshpass(pwd,p,u,h);
			else{
                    execlp("x-terminal-emulator", "x-terminal-emulator", "-T", n, "-e", "sshpass", "-p", pwd, "ssh", "-p", p, "-l", u, h, NULL);
                    execlp("gnome-terminal", "gnome-terminal", "-t", n, "-x", "sshpass", "-p", pwd, "ssh", "-p", p, "-l", u, h, NULL);
                    execlp("xterm", "xterm", "-T", n, "-e", "sshpass", "-p", pwd, "ssh", "-p", p, "-l", u, h, NULL);
			}
		    } else {

                g_print("ssh -p %s -l %s %s\n", p, u, h);

                if (isatty(0) || !getenv("DISPLAY"))
                    execlp("ssh", "ssh", "-p", p, "-l", u, h, NULL);
                else {
                    execlp("x-terminal-emulator", "x-terminal-emulator", "-T", n, "-e", "ssh", "-p", p, "-l", u, h, NULL);
                    execlp("gnome-terminal", "gnome-terminal", "-t", n, "-x", "ssh", "-p", p, "-l", u, h, NULL);
                    execlp("xterm", "xterm", "-T", n, "-e", "ssh", "-p", p, "-l", u, h, NULL);
                }
		    }
            } else {
                g_print("ssh -p %s %s\n", p, h);

                if (isatty(0) || !getenv("DISPLAY"))
                    execlp("ssh", "ssh", "-p", p, h, NULL);
                else {
                    execlp("x-terminal-emulator", "x-terminal-emulator", "-T", n, "-e", "ssh", "-p", p, h, NULL);
                    execlp("gnome-terminal", "gnome-terminal", "-t", n, "-x", "ssh", "-p", p, h, NULL);
                    execlp("xterm", "xterm", "-T", n, "-e", "ssh", "-p", p, h, NULL);
                }
            }
        }

        g_warning(_("execlp() failed: %s\n"), strerror(errno));

        g_free(h);
        g_free(u);
        g_free(t);
        g_free(n);
	g_free(pwd);

    } else {
        gtk_widget_destroy(d);

        g_print(_("Canceled.\n"));
    }

    g_free(config.domain);

    return 1;
}

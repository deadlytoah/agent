------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            Outbox,         \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            RemoteArchived, \* Set of archived Emails
            RemoteInbox,    \* Set of Emails in Inbox
            Undeliverable   \* Set of failed Emails
vars == << Completed, Arrived, Outbox, Parsed, RemoteArchived, RemoteInbox, Undeliverable >>

TypeOK ==   /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Outbox \subseteq Emails
            /\ Parsed \subseteq Emails
            /\ RemoteArchived \subseteq Emails
            /\ RemoteInbox \subseteq Emails
            /\ Undeliverable \subseteq Emails

Invariants ==
    (***********************************************************************)
    (* We don't lose any e-mails.                                          *)
    (***********************************************************************)
    /\ RemoteInbox \cup Arrived \cup Completed \cup Parsed \cup Undeliverable = Emails
    (***********************************************************************)
    (* Don't parse e-mails more than once.                                 *)
    (***********************************************************************)
    /\ \A email \in Completed: email \notin Parsed => email \notin Arrived
-----------------------------------------------------------------------------
ReceiveEmailOK(email) ==
    (***********************************************************************)
    (* Enqueues an Email from Inbox to Arrived.                            *)
    (***********************************************************************)
    /\ Arrived' = Arrived \cup {email}
    /\ UNCHANGED << Completed, Outbox, Parsed, RemoteArchived, RemoteInbox, Undeliverable >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to RemoteArchived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Completed, Arrived, Outbox, Parsed, RemoteArchived, RemoteInbox >>

ReceiveEmail == /\ \E email \in RemoteInbox \ (Arrived \cup Completed \cup Parsed \cup Undeliverable):
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
ArchiveEmail ==
    (***********************************************************************)
    (* When enqueuing an email is successful, move it to RemoteArchived folder.  *)
    (* This is a low-priority operation and it does not block other        *)
    (* operations.                                                         *)
    (***********************************************************************)
    \E email \in (Arrived \cup Completed \cup Parsed) \ RemoteArchived:
        /\ RemoteInbox' = RemoteInbox \ {email}
        /\ RemoteArchived' = RemoteArchived \cup {email}
        /\ UNCHANGED << Completed, Arrived, Outbox, Parsed, Undeliverable >>
-----------------------------------------------------------------------------
ParseEmail1OK ==
    (***********************************************************************)
    (* The first step of parsing an e-mail response stores the parsed      *)
    (* content in the queue.                                               *)
    (***********************************************************************)
    \E email \in Arrived \ (Parsed \cup Undeliverable):
        /\ Parsed' = Parsed \cup {email}
        /\ UNCHANGED << Arrived, Completed, RemoteArchived, RemoteInbox, Outbox, Undeliverable >>

ParseEmail2OK ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    \E email \in (Arrived \cap Parsed) \ Undeliverable:
        /\ Arrived' = Arrived \ {email}
        /\ UNCHANGED << Completed, RemoteInbox, Outbox, Parsed, RemoteArchived, Undeliverable >>

ParseEmailOK ==
    (***********************************************************************)
    (* Parses an email.  The sub-operations occur over distributed settings*)
    (* and may fail.  Each sub-operation is atomic, and their order of     *)
    (* execution is important.                                             *)
    (***********************************************************************)
    \/ ParseEmail1OK
    \/ ParseEmail2OK

ParseEmailError ==
    (***********************************************************************)
    (* Fails parsing an email.                                             *)
    (***********************************************************************)
    \E email \in Arrived \ (Parsed \cup Undeliverable):
        /\ Undeliverable' = Undeliverable \cup {email}
        /\ UNCHANGED << Arrived, Completed, Outbox, Parsed, RemoteArchived, RemoteInbox >>

ParseEmail == ParseEmailOK \/ ParseEmailError
-----------------------------------------------------------------------------
CompleteMessage1OK ==
    \E email \in Parsed \ (Arrived \cup Completed \cup Undeliverable):
        /\ Completed' = Completed \cup {email}
        /\ UNCHANGED << Arrived, Outbox, Parsed, RemoteArchived, RemoteInbox, Undeliverable >>

CompleteMessage2OK ==
    \E email \in (Parsed \cap Completed) \ Undeliverable:
        /\ Parsed' = Parsed \ {email}
        /\ UNCHANGED << Arrived, Completed, Outbox, RemoteArchived, RemoteInbox, Undeliverable >>

CompleteMessageOK ==
    \/ CompleteMessage1OK
    \/ CompleteMessage2OK

CompleteMessageError ==
    \E email \in Parsed \ (Completed \cup Undeliverable):
        /\ Undeliverable' = Undeliverable \cup {email}
        /\ UNCHANGED << Arrived, Completed, Outbox, Parsed, RemoteArchived, RemoteInbox >>

CompleteMessage == CompleteMessageOK \/ CompleteMessageError
-----------------------------------------------------------------------------
AllEmailsCompletedOrUndeliverable ==
    /\ Completed \cup Undeliverable = Emails
    /\ Parsed \ Undeliverable = {}
    /\ UNCHANGED vars

Init == /\ Arrived = {}
        /\ Completed = {}
        /\ Outbox = {}
        /\ Parsed = {}
        /\ RemoteInbox = Emails
        /\ RemoteArchived = {}
        /\ Undeliverable = {}

Next == \/ ReceiveEmail
        \/ ArchiveEmail
        \/ ParseEmail
        \/ CompleteMessage
        \/ AllEmailsCompletedOrUndeliverable

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sun Apr 30 23:35:28 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

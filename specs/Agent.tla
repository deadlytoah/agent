------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Archived,       \* Set of archived Emails
            Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            Inbox,          \* Set of Emails in Inbox
            Outbox,         \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            Undeliverable   \* Set of failed Emails
vars == << Archived, Completed, Arrived, Inbox, Outbox, Parsed, Undeliverable >>

TypeOK ==   /\ Archived \subseteq Emails
            /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Inbox \subseteq Emails
            /\ Outbox \subseteq Emails
            /\ Parsed \subseteq Emails
            /\ Undeliverable \subseteq Emails

Invariants ==
    (***********************************************************************)
    (* We don't lose any e-mails.                                          *)
    (***********************************************************************)
    /\ Inbox \cup Arrived \cup Completed \cup Parsed \cup Undeliverable = Emails
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
    /\ UNCHANGED << Archived, Completed, Inbox, Outbox, Parsed, Undeliverable >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to Archived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Archived, Completed, Arrived, Inbox, Outbox, Parsed >>

ReceiveEmail == /\ \E email \in Inbox \ (Arrived \cup Completed \cup Parsed \cup Undeliverable):
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
ArchiveEmail ==
    (***********************************************************************)
    (* When enqueuing an email is successful, move it to Archived folder.  *)
    (* This is a low-priority operation and it does not block other        *)
    (* operations.                                                         *)
    (***********************************************************************)
    \E email \in (Arrived \cup Completed \cup Parsed) \ Archived:
        /\ Inbox' = Inbox \ {email}
        /\ Archived' = Archived \cup {email}
        /\ UNCHANGED << Completed, Arrived, Outbox, Parsed, Undeliverable >>
-----------------------------------------------------------------------------
ParseEmail1OK ==
    (***********************************************************************)
    (* The first step of parsing an e-mail response stores the parsed      *)
    (* content in the queue.                                               *)
    (***********************************************************************)
    \E email \in Arrived \ (Parsed \cup Undeliverable):
        /\ Parsed' = Parsed \cup {email}
        /\ UNCHANGED << Archived, Arrived, Completed, Inbox, Outbox, Undeliverable >>

ParseEmail2OK ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    \E email \in (Arrived \cap Parsed) \ Undeliverable:
        /\ Arrived' = Arrived \ {email}
        /\ UNCHANGED << Archived, Completed, Inbox, Outbox, Parsed, Undeliverable >>

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
        /\ UNCHANGED << Archived, Arrived, Completed, Inbox, Outbox, Parsed >>

ParseEmail == ParseEmailOK \/ ParseEmailError
-----------------------------------------------------------------------------
CompleteMessage1OK ==
    \E email \in Parsed \ (Arrived \cup Completed \cup Undeliverable):
        /\ Completed' = Completed \cup {email}
        /\ UNCHANGED << Archived, Arrived, Inbox, Outbox, Parsed, Undeliverable >>

CompleteMessage2OK ==
    \E email \in (Parsed \cap Completed) \ Undeliverable:
        /\ Parsed' = Parsed \ {email}
        /\ UNCHANGED << Archived, Arrived, Completed, Inbox, Outbox, Undeliverable >>

CompleteMessageOK ==
    \/ CompleteMessage1OK
    \/ CompleteMessage2OK

CompleteMessageError ==
    \E email \in Parsed \ (Completed \cup Undeliverable):
        /\ Undeliverable' = Undeliverable \cup {email}
        /\ UNCHANGED << Archived, Arrived, Completed, Inbox, Outbox, Parsed >>

CompleteMessage == CompleteMessageOK \/ CompleteMessageError
-----------------------------------------------------------------------------
AllEmailsCompletedOrUndeliverable ==
    /\ Completed \cup Undeliverable = Emails
    /\ Parsed \ Undeliverable = {}
    /\ UNCHANGED vars

Init == /\ Arrived = {}
        /\ Completed = {}
        /\ Inbox = Emails
        /\ Archived = {}
        /\ Outbox = {}
        /\ Parsed = {}
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

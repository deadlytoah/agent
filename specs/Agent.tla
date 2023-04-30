------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails,         \* Set of incoming Emails
            Completions     \* Set of completion responses

VARIABLES   Archived,       \* Set of archived Emails
            Arrived,        \* Queue of incoming Emails
            CompletionMsgq, \* Queue of completion responses
            Inbox,          \* Set of Emails in Inbox
            Outbox,         \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            Undeliverable   \* Set of failed Emails
vars == << Archived, CompletionMsgq, Arrived, Inbox, Outbox, Parsed, Undeliverable >>

TypeOK ==   /\ Archived \subseteq Emails
            /\ Arrived \subseteq Emails
            /\ CompletionMsgq \subseteq Completions
            /\ Inbox \subseteq Emails
            /\ Outbox \subseteq Completions
            /\ Parsed \subseteq Emails
            /\ Undeliverable \subseteq Emails

Invariants ==
    (***********************************************************************)
    (* We don't lose any e-mails.                                          *)
    (***********************************************************************)
    /\ Inbox \cup Arrived \cup Parsed \cup Undeliverable = Emails
-----------------------------------------------------------------------------
ReceiveEmailOK(email) ==
    (***********************************************************************)
    (* Enqueues an Email from Inbox to Arrived.                            *)
    (***********************************************************************)
    /\ Arrived' = Arrived \cup {email}
    /\ UNCHANGED << Archived, CompletionMsgq, Inbox, Outbox, Parsed, Undeliverable >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to Archived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Archived, CompletionMsgq, Arrived, Inbox, Outbox, Parsed >>

ReceiveEmail == /\ \E email \in Inbox \ (Arrived \cup Parsed \cup Undeliverable):
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
ArchiveEmail ==
    (***********************************************************************)
    (* When enqueuing an email is successful, move it to Archived folder.  *)
    (* This is a low-priority operation and it does not block other        *)
    (* operations.                                                         *)
    (***********************************************************************)
    \E email \in (Arrived \cup Parsed) \ Archived:
        /\ Inbox' = Inbox \ {email}
        /\ Archived' = Archived \cup {email}
        /\ UNCHANGED << CompletionMsgq, Arrived, Outbox, Parsed, Undeliverable >>
-----------------------------------------------------------------------------
ParseEmail1OK ==
    (***********************************************************************)
    (* The first step of parsing an e-mail response stores the parsed      *)
    (* content in the queue.                                               *)
    (***********************************************************************)
    \E email \in Arrived \ (Parsed \cup Undeliverable):
        /\ Parsed' = Parsed \cup {email}
        /\ UNCHANGED << Archived, Arrived, CompletionMsgq, Inbox, Outbox, Undeliverable >>

ParseEmail2OK ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    \E email \in (Arrived \cap Parsed) \ Undeliverable:
        /\ Arrived' = Arrived \ {email}
        /\ UNCHANGED << Archived, CompletionMsgq, Inbox, Outbox, Parsed, Undeliverable >>

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
        /\ UNCHANGED << Archived, Arrived, CompletionMsgq, Inbox, Outbox, Parsed >>

ParseEmail == ParseEmailOK \/ ParseEmailError
-----------------------------------------------------------------------------
Init == /\ Arrived = {}
        /\ CompletionMsgq = {}
        /\ Inbox = Emails
        /\ Archived = {}
        /\ Outbox = {}
        /\ Parsed = {}
        /\ Undeliverable = {}

Next == \/ ReceiveEmail
        \/ ArchiveEmail
        \/ ParseEmail
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sun Apr 30 11:14:27 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

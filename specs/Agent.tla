------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails,         \* Set of incoming Emails
            Completions     \* Set of completion responses

VARIABLES   EmailMsgq,      \* Queue of incoming Emails
            CompletionMsgq, \* Queue of completion responses
            Inbox,          \* Set of Emails in Inbox
            Archived,       \* Set of archived Emails
            Undeliverable,  \* Set of failed Emails
            Outbox          \* Set of outgoing Emails
vars == << Archived, CompletionMsgq, EmailMsgq, Inbox, Outbox, Undeliverable >>

TypeOK ==   /\ EmailMsgq \subseteq Emails
            /\ CompletionMsgq \subseteq Completions
            /\ Inbox \subseteq Emails
            /\ Archived \subseteq Emails
            /\ Outbox \subseteq Completions
-----------------------------------------------------------------------------
ReceiveEmailOK(email) ==
    (***********************************************************************)
    (* Enqueues an Email from Inbox to EmailMsgq.                          *)
    (***********************************************************************)
    /\ EmailMsgq' = EmailMsgq \cup {email}
    /\ UNCHANGED << Archived, CompletionMsgq, Inbox, Outbox, Undeliverable >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to Archived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Archived, CompletionMsgq, EmailMsgq, Inbox, Outbox >>

ReceiveEmail == /\ \E email \in Inbox \ (EmailMsgq \cup Undeliverable):
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
ArchiveEmail ==
    (***********************************************************************)
    (* When enqueuing an email is successful, move it to Archived folder.  *)
    (* This is a low-priority operation and it does not block other        *)
    (* operations.                                                         *)
    (***********************************************************************)
    \E email \in EmailMsgq \ Archived:
        /\ Inbox' = Inbox \ {email}
        /\ Archived' = Archived \cup {email}
        /\ UNCHANGED << CompletionMsgq, EmailMsgq, Outbox, Undeliverable >>
-----------------------------------------------------------------------------
Init == /\ EmailMsgq = {}
        /\ CompletionMsgq = {}
        /\ Inbox \in SUBSET(Emails) \ {{}}
        /\ Archived = {}
        /\ Outbox = {}
        /\ Undeliverable = {}

Next == \/ ReceiveEmail
        \/ ArchiveEmail
        \/ UNCHANGED vars

EventuallyEmptyInbox == []<>(Inbox = {})

Spec == Init /\ [][Next]_vars /\ EventuallyEmptyInbox
=============================================================================
\* Modification History
\* Last modified Sat Apr 29 22:27:37 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

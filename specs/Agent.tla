------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            Outbox,         \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            Undeliverable   \* Set of failed Emails
vars == << Arrived, Completed, Outbox, Parsed, Undeliverable >>
EmailsInQueue == Arrived \cup Completed \cup Parsed \cup Undeliverable

TypeOK ==   /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Outbox \subseteq Emails
            /\ Parsed \subseteq Emails
            /\ Undeliverable \subseteq Emails

Invariants ==
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
    /\ UNCHANGED << Completed, Outbox, Parsed, Undeliverable >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to RemoteArchived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Completed, Arrived, Outbox, Parsed >>

ReceiveEmail == /\ \E email \in Emails \ EmailsInQueue:
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
ParseEmail1OK(email) ==
    (***********************************************************************)
    (* The first step of parsing an e-mail response stores the parsed      *)
    (* content in the queue.                                               *)
    (***********************************************************************)
    /\ email \notin Parsed
    /\ Parsed' = Parsed \cup {email}
    /\ UNCHANGED << Arrived, Completed, Outbox, Undeliverable >>

ParseEmail2OK(email) ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    /\ email \in Parsed
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Completed, Outbox, Parsed, Undeliverable >>

ParseEmailOK(email) ==
    (***********************************************************************)
    (* Parses an email.  The sub-operations occur over distributed settings*)
    (* and may fail.  Each sub-operation is atomic, and their order of     *)
    (* execution is important.                                             *)
    (***********************************************************************)
    \/ ParseEmail1OK(email)
    \/ ParseEmail2OK(email)

ParseEmail1Error(email) ==
    (***********************************************************************)
    (* Fails parsing an email.                                             *)
    (***********************************************************************)
    /\ email \notin Parsed
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Arrived, Completed, Outbox, Parsed >>

ParseEmail ==
    \E email \in Arrived \ Undeliverable:
        \/ ParseEmailOK(email)
        \/ ParseEmail1Error(email)
-----------------------------------------------------------------------------
CompleteMessage1OK(email) ==
    /\ email \notin Completed
    /\ Completed' = Completed \cup {email}
    /\ UNCHANGED << Arrived, Outbox, Parsed, Undeliverable >>

CompleteMessage2OK(email) ==
    /\ email \in Completed
    /\ Parsed' = Parsed \ {email}
    /\ UNCHANGED << Arrived, Completed, Outbox, Undeliverable >>

CompleteMessageOK(email) ==
    \/ CompleteMessage1OK(email)
    \/ CompleteMessage2OK(email)

CompleteMessage1Error(email) ==
    /\ email \notin Completed
    /\ Undeliverable' = Undeliverable \cup {email}
    /\ UNCHANGED << Arrived, Completed, Outbox, Parsed >>

CompleteMessage ==
    \E email \in Parsed \ (Arrived \cup Undeliverable):
        \/ CompleteMessageOK(email)
        \/ CompleteMessage1Error(email)
-----------------------------------------------------------------------------
AllEmailsCompletedOrUndeliverable ==
    /\ Completed \cup Undeliverable = Emails
    /\ Parsed \ Undeliverable = {}
    /\ UNCHANGED vars

Init == /\ Arrived = {}
        /\ Completed = {}
        /\ Outbox = {}
        /\ Parsed = {}
        /\ Undeliverable = {}

Next == \/ ReceiveEmail
        \/ ParseEmail
        \/ CompleteMessage
        \/ AllEmailsCompletedOrUndeliverable

Spec == Init /\ [][Next]_vars

EventuallyCompletedOrUndeliverable == <>[](Completed \cup Undeliverable = Emails)
=============================================================================
\* Modification History
\* Last modified Mon May 01 14:13:08 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

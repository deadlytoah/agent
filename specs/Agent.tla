------------------------------- MODULE Agent -------------------------------
EXTENDS TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            Outbox,         \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            Abandoned       \* Set of failed Emails
vars == << Abandoned, Arrived, Completed, Outbox, Parsed >>
EmailsInQueue == Abandoned \cup Arrived \cup Completed \cup Parsed

TypeOK ==   /\ Abandoned \subseteq Emails
            /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Outbox \subseteq Emails
            /\ Parsed \subseteq Emails

Invariants ==
    (***********************************************************************)
    (* Don't parse e-mails more than once.                                 *)
    (***********************************************************************)
    /\ \A email \in Completed: email \notin Parsed => email \notin Arrived
    (***********************************************************************)
    (* Abandoned e-mails not to appear anywhere else, as Abandoned is a    *)
    (* general queue state separate from e-mail processing state.          *)
    (***********************************************************************)
    /\ \A email \in Abandoned: email \notin Arrived \cup Completed \cup Parsed
-----------------------------------------------------------------------------
ReceiveEmailOK(email) ==
    (***********************************************************************)
    (* Enqueues an Email from Inbox to Arrived.                            *)
    (***********************************************************************)
    /\ Arrived' = Arrived \cup {email}
    /\ UNCHANGED << Abandoned, Completed, Outbox, Parsed >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to RemoteArchived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Abandoned' = Abandoned \cup {email}
    /\ UNCHANGED << Arrived, Completed, Outbox, Parsed >>

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
    /\ UNCHANGED << Abandoned, Arrived, Completed, Outbox >>

ParseEmail2OK(email) ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    /\ email \in Parsed
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Abandoned, Completed, Outbox, Parsed >>

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
    /\ Abandoned' = Abandoned \cup {email}
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Completed, Outbox, Parsed >>

ParseEmail ==
    \E email \in Arrived \ Abandoned:
        \/ ParseEmailOK(email)
        \/ ParseEmail1Error(email)
-----------------------------------------------------------------------------
CompleteMessage1OK(email) ==
    /\ email \notin Completed
    /\ Completed' = Completed \cup {email}
    /\ UNCHANGED << Abandoned, Arrived, Outbox, Parsed >>

CompleteMessage2OK(email) ==
    /\ email \in Completed
    /\ Parsed' = Parsed \ {email}
    /\ UNCHANGED << Abandoned, Arrived, Completed, Outbox >>

CompleteMessageOK(email) ==
    \/ CompleteMessage1OK(email)
    \/ CompleteMessage2OK(email)

CompleteMessage1Error(email) ==
    /\ email \notin Completed
    /\ Abandoned' = Abandoned \cup {email}
    /\ Parsed' = Parsed \ {email}
    /\ UNCHANGED << Arrived, Completed, Outbox >>

CompleteMessage ==
    \E email \in Parsed \ (Arrived \cup Abandoned):
        \/ CompleteMessageOK(email)
        \/ CompleteMessage1Error(email)
-----------------------------------------------------------------------------
AllEmailsCompletedOrUndeliverable ==
    /\ Completed \cup Abandoned = Emails
    /\ Parsed \ Abandoned = {}
    /\ UNCHANGED vars

Init == /\ Abandoned = {}
        /\ Arrived = {}
        /\ Completed = {}
        /\ Outbox = {}
        /\ Parsed = {}

Next == \/ ReceiveEmail
        \/ ParseEmail
        \/ CompleteMessage
        \/ AllEmailsCompletedOrUndeliverable

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Invariants
=============================================================================
\* Modification History
\* Last modified Mon May 01 18:46:27 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

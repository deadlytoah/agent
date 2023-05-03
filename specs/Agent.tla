------------------------------- MODULE Agent -------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Archived,       \* Set of archived Emails
            Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            RemoteOutbox,   \* Set of outgoing Emails
            Parsed,         \* Set of parsed Emails
            Abandoned       \* Set of failed Emails
vars == << Abandoned, Archived, Arrived, Completed, Parsed, RemoteOutbox >>
EmailsInQueue == Abandoned \cup Archived \cup Arrived \cup Completed \cup Parsed

TypeOK ==   /\ Abandoned \subseteq Emails
            /\ Archived \subseteq Emails
            /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Parsed \subseteq Emails
            /\ RemoteOutbox \in Seq(Emails)

Range(S) == { S[n] : n \in DOMAIN S }

Invariants ==
    /\ \A email \in Completed: email \notin Parsed => email \notin Arrived
    (***********************************************************************)
    (* Don't parse e-mails more than once.                                 *)
    (***********************************************************************)
    /\ \A email \in Range(RemoteOutbox): email \notin Completed => email \notin Parsed
    (***********************************************************************)
    (* Don't complete e-mails more than once.                              *)
    (***********************************************************************)
    /\ \A email \in Abandoned: email \notin Arrived \cup Completed \cup Parsed
    (***********************************************************************)
    (* Abandoned e-mails not to appear anywhere else, as Abandoned is a    *)
    (* general queue state separate from e-mail processing state.          *)
    (***********************************************************************)
    /\ \A email \in Archived: email \notin Arrived \cup Completed \cup Parsed
    (***********************************************************************)
    (* Same with archived emails.                                          *)
    (***********************************************************************)
    /\ Len(RemoteOutbox) = Cardinality(Range(RemoteOutbox))
    (***********************************************************************)
    (* Don't send e-mails more than once.                                  *)
    (***********************************************************************)
-----------------------------------------------------------------------------
ReceiveEmailOK(email) ==
    (***********************************************************************)
    (* Enqueues an Email from Inbox to Arrived.                            *)
    (***********************************************************************)
    /\ Arrived' = Arrived \cup {email}
    /\ UNCHANGED << Abandoned, Archived, Completed, Parsed, RemoteOutbox >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to RemoteArchived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Abandoned' = Abandoned \cup {email}
    /\ UNCHANGED << Archived, Arrived, Completed, Parsed, RemoteOutbox >>

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
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, RemoteOutbox >>

ParseEmail2OK(email) ==
    (***********************************************************************)
    (* The second step of parsing removes the e-mail response from the     *)
    (* queue only after the parsing is successful.  This ensures we don't  *)
    (* lose any e-mails in case of a failure.                              *)
    (***********************************************************************)
    /\ email \in Parsed
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Abandoned, Archived, Completed, Parsed, RemoteOutbox >>

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
    /\ UNCHANGED << Archived, Completed, Parsed, RemoteOutbox >>

ParseEmail ==
    \E email \in Arrived \ Abandoned:
        \/ ParseEmailOK(email)
        \/ ParseEmail1Error(email)
-----------------------------------------------------------------------------
CompleteMessage1OK(email) ==
    /\ email \notin Completed
    /\ Completed' = Completed \cup {email}
    /\ UNCHANGED << Abandoned, Archived, Arrived, Parsed, RemoteOutbox >>

CompleteMessage2OK(email) ==
    /\ email \in Completed
    /\ Parsed' = Parsed \ {email}
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, RemoteOutbox >>

CompleteMessageOK(email) ==
    \/ CompleteMessage1OK(email)
    \/ CompleteMessage2OK(email)

CompleteMessage1Error(email) ==
    /\ email \notin Completed
    /\ Abandoned' = Abandoned \cup {email}
    /\ Parsed' = Parsed \ {email}
    /\ UNCHANGED << Archived, Arrived, Completed, RemoteOutbox >>

CompleteMessage ==
    \E email \in Parsed \ (Arrived \cup Abandoned):
        \/ CompleteMessageOK(email)
        \/ CompleteMessage1Error(email)
-----------------------------------------------------------------------------
SendOutCompletion1OK(email) ==
    (***********************************************************************)
    (* Sends out a completion response e-mail.                             *)
    (***********************************************************************)
    /\ email \notin Range(RemoteOutbox)     \* We haven't already sent this e-mail
    /\ RemoteOutbox' = Append(RemoteOutbox, email)
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, Parsed >>

SendOutCompletion2OK(email) ==
    (***********************************************************************)
    (* Marks an email as sent.                                             *)
    (***********************************************************************)
    /\ email \in Range(RemoteOutbox)    \* Previous step to send this e-mail succeeded.
    /\ Archived' = Archived \cup {email}
    /\ Completed' = Completed \ {email}
    /\ UNCHANGED << Abandoned, Arrived, Parsed, RemoteOutbox >>

SendOutCompletion1Error(email) ==
    (***********************************************************************)
    (* Fails sending the e-mail.                                           *)
    (***********************************************************************)
    /\ email \notin Range(RemoteOutbox)     \* We haven't already sent this e-mail
    /\ Abandoned' = Abandoned \cup {email}
    /\ Completed' = Completed \ {email}
    /\ UNCHANGED << Archived, Arrived, Parsed, RemoteOutbox >>

SendOutCompletion ==
    \E email \in Completed \ (Abandoned \cup Parsed):
        \/ SendOutCompletion1OK(email)
        \/ SendOutCompletion2OK(email)
        \/ SendOutCompletion1Error(email)
-----------------------------------------------------------------------------
AllDone ==
    (***********************************************************************)
    (* All done and system comes to equilibrium.                           *)
    (***********************************************************************)
    /\ Archived \cup Abandoned = Emails
    /\ Parsed \ Abandoned = {}
    /\ UNCHANGED vars

Init == /\ Abandoned = {}
        /\ Archived = {}
        /\ Arrived = {}
        /\ Completed = {}
        /\ Parsed = {}
        /\ RemoteOutbox = <<>>

Next == \/ ReceiveEmail
        \/ ParseEmail
        \/ CompleteMessage
        \/ SendOutCompletion
        \/ AllDone

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
(*****************************************************************************)
(* Temporal properties for verification                                      *)
(*****************************************************************************)

NoLostEmails ==
    (*************************************************************************)
    (* No e-mails should be lost.  This is a safety property.                *)
    (*************************************************************************)
    \A email \in Emails:
        [] (email \in EmailsInQueue => <>[] (email \in Abandoned \cup Range(RemoteOutbox)))
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Invariants
THEOREM Spec => NoLostEmails
=============================================================================
\* Modification History
\* Last modified Wed May 03 16:27:57 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

------------------------------- MODULE Agent -------------------------------
(**************************************************************************)
(* Reliable Interface to GPT via Gmail                                    *)
(*                                                                        *)
(* Copyright (C) 2023  Hee Shin                                           *)
(*                                                                        *)
(* This program is free software: you can redistribute it and/or modify   *)
(* it under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or      *)
(* (at your option) any later version.                                    *)
(*                                                                        *)
(* This program is distributed in the hope that it will be useful,        *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of         *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          *)
(* GNU General Public License for more details.                           *)
(*                                                                        *)
(* You should have received a copy of the GNU General Public License      *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>. *)
(**************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS   Emails          \* Set of incoming Emails

VARIABLES   Archived,       \* Set of archived Emails
            Arrived,        \* Queue of incoming Emails
            Completed,      \* Queue of completion responses
            RemoteOutbox,   \* Set of outgoing Emails
            Queued,         \* Set of parsed Emails
            Abandoned       \* Set of failed Emails
vars == << Abandoned, Archived, Arrived, Completed, Queued, RemoteOutbox >>
EmailsInQueue == Abandoned \cup Archived \cup Arrived \cup Completed \cup Queued

TypeOK ==   /\ Abandoned \subseteq Emails
            /\ Archived \subseteq Emails
            /\ Arrived \subseteq Emails
            /\ Completed \subseteq Emails
            /\ Queued \subseteq Emails
            /\ RemoteOutbox \in Seq(Emails)

Range(S) == { S[n] : n \in DOMAIN S }

Invariants ==
    /\ \A email \in Completed: email \notin Queued => email \notin Arrived
    (***********************************************************************)
    (* Don't parse e-mails more than once.                                 *)
    (***********************************************************************)
    /\ \A email \in Range(RemoteOutbox): email \notin Completed => email \notin Queued
    (***********************************************************************)
    (* Don't complete e-mails more than once.                              *)
    (***********************************************************************)
    /\ \A email \in Abandoned: email \notin Arrived \cup Completed \cup Queued
    (***********************************************************************)
    (* Abandoned e-mails not to appear anywhere else, as Abandoned is a    *)
    (* general queue state separate from e-mail processing state.          *)
    (***********************************************************************)
    /\ \A email \in Archived: email \notin Arrived \cup Completed \cup Queued
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
    /\ UNCHANGED << Abandoned, Archived, Completed, Queued, RemoteOutbox >>

ReceiveEmailError(email) ==
    (***********************************************************************)
    (* Fails reading an email from Inbox.  Logs it, marks it and moves it  *)
    (* to RemoteArchived folder.  Support engineer can move the email back to    *)
    (* Inbox after addressing the issue.                                   *)
    (***********************************************************************)
    /\ Abandoned' = Abandoned \cup {email}
    /\ UNCHANGED << Archived, Arrived, Completed, Queued, RemoteOutbox >>

ReceiveEmail == /\ \E email \in Emails \ EmailsInQueue:
                    \/ ReceiveEmailOK(email)
                    \/ ReceiveEmailError(email)
-----------------------------------------------------------------------------
PrepareEmail1OK(email) ==
    (***********************************************************************)
    (* The first step of preparing an e-mail for completion is to parse    *)
    (* the e-mail and update its status as Queued.  It then places the     *)
    (* parsed message in the queue.  Thus there are two forms of the same  *)
    (* e-mail in the queue at this point. This is an atomic operation.     *)
    (***********************************************************************)
    /\ email \notin Queued
    /\ Queued' = Queued \cup {email}
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, RemoteOutbox >>

PrepareEmail2OK(email) ==
    (***********************************************************************)
    (* The second step of preparing removes the e-mail response from the   *)
    (* Arrival queue only after the parsing is successful.  This ensures   *)
    (* we don't lose any e-mails in case of a failure.                     *)
    (***********************************************************************)
    /\ email \in Queued
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Abandoned, Archived, Completed, Queued, RemoteOutbox >>

PrepareEmailOK(email) ==
    (***********************************************************************)
    (* Prepares an email for completion.  The sub-operations occur over    *)
    (* distributed settings and may fail.  Each sub-operation is atomic,   *)
    (* and their order of execution is important.                          *)
    (***********************************************************************)
    \/ PrepareEmail1OK(email)
    \/ PrepareEmail2OK(email)

PrepareEmail1Error(email) ==
    (***********************************************************************)
    (* Fails preparing an email.                                           *)
    (***********************************************************************)
    /\ email \notin Queued
    /\ Abandoned' = Abandoned \cup {email}
    /\ Arrived' = Arrived \ {email}
    /\ UNCHANGED << Archived, Completed, Queued, RemoteOutbox >>

PrepareEmail ==
    \E email \in Arrived \ Abandoned:
        \/ PrepareEmailOK(email)
        \/ PrepareEmail1Error(email)
-----------------------------------------------------------------------------
CompleteMessage1OK(email) ==
    /\ email \notin Completed
    /\ Completed' = Completed \cup {email}
    /\ UNCHANGED << Abandoned, Archived, Arrived, Queued, RemoteOutbox >>

CompleteMessage2OK(email) ==
    /\ email \in Completed
    /\ Queued' = Queued \ {email}
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, RemoteOutbox >>

CompleteMessageOK(email) ==
    \/ CompleteMessage1OK(email)
    \/ CompleteMessage2OK(email)

CompleteMessage1Error(email) ==
    /\ email \notin Completed
    /\ Abandoned' = Abandoned \cup {email}
    /\ Queued' = Queued \ {email}
    /\ UNCHANGED << Archived, Arrived, Completed, RemoteOutbox >>

CompleteMessage ==
    \E email \in Queued \ (Arrived \cup Abandoned):
        \/ CompleteMessageOK(email)
        \/ CompleteMessage1Error(email)
-----------------------------------------------------------------------------
SendOutCompletion1OK(email) ==
    (***********************************************************************)
    (* Sends out a completion response e-mail.                             *)
    (***********************************************************************)
    /\ email \notin Range(RemoteOutbox)     \* We haven't already sent this e-mail
    /\ RemoteOutbox' = Append(RemoteOutbox, email)
    /\ UNCHANGED << Abandoned, Archived, Arrived, Completed, Queued >>

SendOutCompletion2OK(email) ==
    (***********************************************************************)
    (* Marks an email as sent.                                             *)
    (***********************************************************************)
    /\ email \in Range(RemoteOutbox)    \* Previous step to send this e-mail succeeded.
    /\ Archived' = Archived \cup {email}
    /\ Completed' = Completed \ {email}
    /\ UNCHANGED << Abandoned, Arrived, Queued, RemoteOutbox >>

SendOutCompletion1Error(email) ==
    (***********************************************************************)
    (* Fails sending the e-mail.                                           *)
    (***********************************************************************)
    /\ email \notin Range(RemoteOutbox)     \* We haven't already sent this e-mail
    /\ Abandoned' = Abandoned \cup {email}
    /\ Completed' = Completed \ {email}
    /\ UNCHANGED << Archived, Arrived, Queued, RemoteOutbox >>

SendOutCompletion ==
    \E email \in Completed \ (Abandoned \cup Queued):
        \/ SendOutCompletion1OK(email)
        \/ SendOutCompletion2OK(email)
        \/ SendOutCompletion1Error(email)
-----------------------------------------------------------------------------
AllDone ==
    (***********************************************************************)
    (* All done and system comes to equilibrium.                           *)
    (***********************************************************************)
    /\ Archived \cup Abandoned = Emails
    /\ Queued \ Abandoned = {}
    /\ UNCHANGED vars

Init == /\ Abandoned = {}
        /\ Archived = {}
        /\ Arrived = {}
        /\ Completed = {}
        /\ Queued = {}
        /\ RemoteOutbox = <<>>

Next == \/ ReceiveEmail
        \/ PrepareEmail
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
\* Last modified Wed May 10 14:00:01 KST 2023 by hcs
\* Created Fri Apr 28 13:04:37 KST 2023 by hcs

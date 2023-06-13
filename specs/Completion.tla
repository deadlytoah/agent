----------------------------- MODULE Completion -----------------------------
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

(**************************************************************************)
(* This specification models the coordination between the task that       *)
(* retrieves e-mails and the completion task.                             *)
(**************************************************************************)

CONSTANTS Signals,          \* the set of signals notifying the completion task
          Emails            \* the set of incoming e-mails

VARIABLES Channel,          \* the synchronisation channel between the tasks
          CompletionQueue,  \* the queue of completed e-mails
          EmailQueue,       \* the queue of incoming e-mails
          QueueChanged      \* whether EmailQueue has changed by the EnqueueEmail action
vars == << Channel, CompletionQueue, EmailQueue, QueueChanged >>

AllQueues == CompletionQueue \cup EmailQueue
(**************************************************************************)
(* Set of Emails found in any queue.                                      *)
(**************************************************************************)
UnqueuedEmails == Emails \ AllQueues
(**************************************************************************)
(* Set of Emails not found in any queue.                                  *)
(**************************************************************************)

TypeOK == /\ Channel \in SUBSET Signals
          /\ CompletionQueue \in SUBSET Emails
          /\ EmailQueue \in SUBSET Emails
          /\ QueueChanged \in BOOLEAN

AllEmailsDelivered == <>[](Emails = CompletionQueue)
(**************************************************************************)
(* Temporal property that all e-mails are eventually delivered.           *)
(**************************************************************************)

SendSignal == Channel' = Channel \cup {CHOOSE signal \in Signals: signal \notin Channel}
(**************************************************************************)
(* Inserts a signal in the channel to signal the completion task of an    *)
(* incoming email.                                                        *)
(**************************************************************************)

ReceiveSignal == Channel' = Channel \ {CHOOSE signal \in Channel: TRUE}
(**************************************************************************)
(* Removes a signal from the channel.                                     *)
(**************************************************************************)
-----------------------------------------------------------------------------
EnqueueEmail ==
(**************************************************************************)
(* Enqueues an incoming e-mail in the EmailQueue.                         *)
(**************************************************************************)
    /\ QueueChanged = FALSE
    /\ \E email \in UnqueuedEmails:
        /\ EmailQueue' = EmailQueue \cup {email}
        /\ QueueChanged' = TRUE
    /\ UNCHANGED << Channel, CompletionQueue >>

SignalCompletionTask ==
(**************************************************************************)
(* Signals the completion task of an incoming e-mail.                     *)
(**************************************************************************)
    /\ QueueChanged = TRUE
    /\ QueueChanged' = FALSE
    /\ SendSignal
    /\ UNCHANGED << CompletionQueue, EmailQueue >>

CompleteEmail ==
(**************************************************************************)
(* Have an e-mail in EmailQueue completed when signaled.                  *)
(**************************************************************************)
    /\ Channel # {}         \* EmailQueue has signaled the completion task.
    /\ \E email \in EmailQueue:
        /\ CompletionQueue' = CompletionQueue \cup {email}
        /\ EmailQueue' = EmailQueue \ {email}
        /\ ReceiveSignal
    /\ UNCHANGED << QueueChanged >>
-----------------------------------------------------------------------------
Init == /\ Channel = {}
        /\ CompletionQueue = {}
        /\ EmailQueue = {}
        /\ QueueChanged = FALSE

Next == \/ EnqueueEmail
        \/ SignalCompletionTask
        \/ CompleteEmail
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK /\ AllEmailsDelivered
=============================================================================
\* Modification History
\* Last modified Mon May 15 14:52:30 KST 2023 by hcs
\* Created Sun May 14 11:53:48 KST 2023 by hcs

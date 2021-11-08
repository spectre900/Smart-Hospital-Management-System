-------------------------------- MODULE UML2 --------------------------------
EXTENDS Naturals
VARIABLES checkup, rfidScan, testResults, examined, disease, prescribe, addToDB

TypeOK ==
    /\ checkup \in {"done", "notDone"}
    /\ rfidScan \in {"pending", "successful", "unsuccessful"}
    /\ testResults \in {"undetermined", "available", "unavailable"}
    /\ examined \in {"done", "notDone"}
    /\ disease \in {"undetermined", "found", "notFound"}
    /\ prescribe \in {"done", "notDone"}
    /\ addToDB \in {"done", "notDone"}

Init ==
    /\ checkup = "notDone"
    /\ rfidScan = "pending"
    /\ testResults = "undetermined"
    /\ examined = "notDone"
    /\ disease = "undetermined"
    /\ addToDB = "notDone"
    /\ prescribe = "notDone"
    
Var == <<checkup, rfidScan, testResults, examined, disease, prescribe, addToDB>>

GetResults == 
    \/  /\ checkup = "notDone"
        /\ checkup' = "done"
        /\ UNCHANGED <<rfidScan, testResults>>
    \/  /\ checkup = "done"
        /\ rfidScan = "pending"
        /\ rfidScan' \in {"successful", "unsuccessful"}
        /\ UNCHANGED <<checkup, testResults>>
    \/  /\ checkup = "done"
        /\ rfidScan = "successful"
        /\ testResults = "undetermined"
        /\ testResults' \in {"available", "unavailable"}
        /\ UNCHANGED <<checkup, rfidScan>>
    \/  /\ checkup = "done"
        /\ rfidScan = "successful"
        /\ testResults \in {"available", "unavailable"}
        /\ UNCHANGED <<checkup, rfidScan, testResults>>
    \/  /\ checkup = "done"
        /\ rfidScan = "unsuccessful"
        /\ UNCHANGED <<checkup, rfidScan, testResults>>

Diagnosis == 
    \/  /\ testResults = "available"
        /\ examined = "notDone"
        /\ examined' = "done"
        /\ UNCHANGED <<disease>>
    \/  /\ testResults = "available"
        /\ examined = "done"
        /\ disease = "undetermined"
        /\ disease' \in {"found", "notFound"}
        /\ UNCHANGED <<examined>>
    \/  /\ testResults = "available"
        /\ examined = "done"
        /\ disease \in {"found", "notFound"}
        /\ UNCHANGED <<examined, disease>>
    \/  /\ testResults \in {"undetermined", "unavailable"}
        /\ UNCHANGED <<examined, disease>>

Prescription == 
    \/  /\ disease = "found"
        /\ prescribe = "notDone"
        /\ prescribe' = "done"
        /\ UNCHANGED <<addToDB>>
    \/  /\ disease = "found"
        /\ prescribe = "done"
        /\ addToDB = "notDone"
        /\ addToDB' \in {"done", "notDone"}
        /\ UNCHANGED <<prescribe>>
    \/  /\ disease = "found"
        /\ prescribe = "done"
        /\ addToDB = "done"
        /\ UNCHANGED <<addToDB, prescribe>>
    \/  /\ disease \in {"undetermined", "notFound"}
        /\ UNCHANGED <<addToDB, prescribe>>

Next ==
    /\ GetResults
    /\ Diagnosis
    /\ Prescription
    /\ TypeOK
    
Spec == Init /\ [][Next]_Var
=============================================================================
\* Modification History
\* Last modified Tue Sep 28 17:44:41 IST 2021 by ubuntu
\* Created Tue Sep 28 17:44:31 IST 2021 by ubuntu

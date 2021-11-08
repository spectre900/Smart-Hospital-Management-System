-------------------------------- MODULE UML1 --------------------------------
EXTENDS Naturals
VARIABLES credentials, loggedIn, attempt ,rfidScan, patientInfo, symptomsChecked , testNeeded , addedToDB

TypeOK ==
    /\ loggedIn \in {"yes", "no"}
    /\ credentials \in {"correct", "incorrect"}
    /\ attempt \in (1..3)
    /\ rfidScan \in {"done", "notDone"}
    /\ patientInfo \in {"retrieved", "notRetrieved", "error"}
    /\ symptomsChecked \in {"yes", "no"}
    /\ testNeeded \in {"undetermined", "yes", "no"}
    /\ addedToDB \in {"yes","no"}

Init ==
    /\ loggedIn = "no"
    /\ credentials \in {"correct", "incorrect"}
    /\ attempt = 1
    /\ rfidScan = "notDone"
    /\ patientInfo = "notRetrieved"
    /\ symptomsChecked = "no"
    /\ testNeeded = "undetermined"
    /\ addedToDB = "no"
    
Var == <<loggedIn, credentials, attempt, rfidScan, patientInfo, symptomsChecked, testNeeded, addedToDB>>

Login == 
    \/  /\ loggedIn = "yes"
        /\ UNCHANGED <<loggedIn, credentials, attempt>>
    \/  /\ loggedIn = "no"
        /\ credentials = "correct"
        /\ loggedIn' = "yes"
        /\ UNCHANGED <<credentials, attempt>>
    \/  /\ loggedIn = "no"
        /\ credentials = "incorrect"
        /\ credentials' \in {"correct","incorrect"}
        /\ attempt < 3
        /\ attempt' = attempt + 1
        /\ UNCHANGED <<loggedIn>>















Scan == 
    \/  /\ loggedIn = "yes"
        /\ rfidScan = "notDone"
        /\ rfidScan' = "done"
        /\ UNCHANGED <<patientInfo>>
    \/  /\ loggedIn = "yes"
        /\ rfidScan = "done"
        /\ patientInfo = "notRetrieved"
        /\ patientInfo' \in {"retrieved", "error"}
        /\ UNCHANGED <<rfidScan>>
    \/  /\ loggedIn = "yes"
        /\ rfidScan = "done"
        /\ patientInfo \in {"retrieved", "error"}
        /\ UNCHANGED <<rfidScan, patientInfo>>
    \/  /\ loggedIn = "no"
        /\ UNCHANGED <<rfidScan, patientInfo>>













































Diagnosis == 
    \/  /\ patientInfo = "retrieved"
        /\ symptomsChecked = "no"
        /\ symptomsChecked' = "yes"
        /\ UNCHANGED <<testNeeded, addedToDB>>
    \/  /\ patientInfo = "retrieved"
        /\ symptomsChecked = "yes"
        /\ testNeeded = "undetermined"
        /\ testNeeded' \in {"yes", "no"}
        /\ UNCHANGED <<symptomsChecked, addedToDB>>
    \/  /\ patientInfo = "retrieved"
        /\ symptomsChecked = "yes"
        /\ testNeeded = "yes"
        /\ addedToDB = "no"
        /\ addedToDB' = "yes"
        /\ UNCHANGED <<symptomsChecked, testNeeded>>
    \/  /\ patientInfo = "retrieved"
        /\ symptomsChecked = "yes"
        /\ testNeeded = "yes"
        /\ addedToDB = "yes"
        /\ addedToDB' = "no"
        /\ testNeeded' \in {"yes", "no"}
        /\ UNCHANGED <<symptomsChecked>>
    \/  /\ patientInfo = "retrieved"
        /\ symptomsChecked = "yes"
        /\ testNeeded = "no"
        /\ UNCHANGED <<symptomsChecked, testNeeded>>
        /\ UNCHANGED <<addedToDB>>
    \/  /\ patientInfo = "notRetrieved"
        /\ UNCHANGED <<symptomsChecked, testNeeded>>
        /\ UNCHANGED <<addedToDB>>
        
        
        

Next ==
    /\ Login
    /\ Scan
    /\ Diagnosis
    /\ TypeOK
    
Spec == Init /\ [][Next]_Var
=============================================================================
\* Modification History
\* Last modified Tue Oct 05 00:26:14 IST 2021 by ubuntu
\* Created Fri Sep 17 19:51:02 IST 2021 by ubuntu

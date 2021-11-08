-------------------------------- MODULE UML5 --------------------------------
EXTENDS Naturals
VARIABLES broadcastInfo, forwardToDB, updateInfoInDB, tagStatus, alertTag, alertReader, currentBattery, readerStatus, contactInactiveReaders, ack

TypeOK ==
    /\ broadcastInfo \in {"done", "notDone"}
    /\ forwardToDB \in {"done", "notDone"}
    /\ updateInfoInDB \in {"done", "notDone"}
    /\ tagStatus \in {"active", "inactive"}
    /\ alertTag \in {"required", "notRequired"}
    /\ alertReader \in {"required", "notRequired"}
    /\ currentBattery \in (1..100)
    /\ readerStatus \in {"active", "inactive"}
    /\ contactInactiveReaders \in {"required", "notRequired"}
    /\ ack \in {"received", "notReceived", "notRequired"}
 
Init ==
    /\ broadcastInfo = "notDone"
    /\ forwardToDB = "notDone"
    /\ updateInfoInDB = "notDone"
    /\ tagStatus = "active"
    /\ alertTag = "notRequired"
    /\ alertReader = "notRequired"
    /\ currentBattery \in (1..100)
    /\ readerStatus = "active"
    /\ contactInactiveReaders = "notRequired"
    /\ ack = "notRequired"

Var == <<broadcastInfo, forwardToDB, updateInfoInDB, tagStatus, alertTag, alertReader, currentBattery, readerStatus, contactInactiveReaders, ack>>

UpdateStatus == 
    \/  /\ broadcastInfo = "notDone"
        /\ broadcastInfo' = "done"
        /\ UNCHANGED <<forwardToDB, updateInfoInDB, tagStatus, currentBattery, readerStatus>>
    \/  /\ broadcastInfo = "done"
        /\ forwardToDB = "notDone"
        /\ forwardToDB' = "done"
        /\ UNCHANGED <<broadcastInfo, updateInfoInDB, tagStatus, currentBattery, readerStatus>>
    \/  /\ broadcastInfo = "done"
        /\ forwardToDB = "done"
        /\ updateInfoInDB = "notDone"
        /\ updateInfoInDB' = "done"
        /\ tagStatus' \in {"active", "inactive"}
        /\ currentBattery' \in (1..100)
        /\ readerStatus' \in {"active", "inactive"}
        /\ UNCHANGED <<broadcastInfo, forwardToDB>>
    \/  /\ broadcastInfo = "done"
        /\ forwardToDB = "done"
        /\ updateInfoInDB = "done"
        /\ UNCHANGED <<broadcastInfo, forwardToDB, updateInfoInDB>>

CheckTagStatus == 
    \/  /\ updateInfoInDB = "done"
        /\ tagStatus = "inactive"
        /\ currentBattery >= 10
        /\ alertTag' = "required"
        /\ tagStatus' = "active"
        /\ UNCHANGED <<currentBattery>>
    \/  /\ updateInfoInDB = "done"
        /\ tagStatus = "active"
        /\ currentBattery < 10
        /\ alertTag' = "required"
        /\ currentBattery' \in (10..100)
        /\ UNCHANGED <<tagStatus>>
    \/  /\ updateInfoInDB = "done"
        /\ tagStatus = "inactive"
        /\ currentBattery < 10
        /\ alertTag' = "required"
        /\ tagStatus' = "active"
        /\ currentBattery' \in (10..100)
    \/  /\ updateInfoInDB = "done"
        /\ currentBattery >= 10
        /\ tagStatus = "active"
        /\ UNCHANGED <<alertTag, tagStatus, currentBattery>>
    \/  /\ updateInfoInDB = "notDone"
        /\ UNCHANGED <<alertTag>>
        
CheckReaderStatus == 
    \/  /\ updateInfoInDB = "done"
        /\ readerStatus = "inactive"
        /\ contactInactiveReaders = "notRequired"
        /\ contactInactiveReaders' = "required"
        /\ UNCHANGED<<ack, readerStatus, alertReader>>
    \/  /\ updateInfoInDB = "done"
        /\ contactInactiveReaders = "required"
        /\ ack = "notRequired"
        /\ ack' \in  {"received", "notReceived"}
        /\ UNCHANGED<<contactInactiveReaders, readerStatus, alertReader>>
    \/  /\ updateInfoInDB = "done"
        /\ contactInactiveReaders = "required"
        /\ ack = "received"
        /\ contactInactiveReaders' = "notRequired"
        /\ ack' = "notRequired"
        /\ readerStatus' = "active"
        /\ UNCHANGED<<alertReader>> 
    \/  /\ updateInfoInDB = "done"
        /\ contactInactiveReaders = "required"
        /\ ack = "notReceived"
        /\ alertReader' = "required"
        /\ contactInactiveReaders' = "notRequired"
        /\ ack' = "notRequired"
        /\ readerStatus' = "active" 
    \/  /\ updateInfoInDB = "done"
        /\ readerStatus = "active"
        /\ UNCHANGED<<contactInactiveReaders, ack, readerStatus, alertReader>> 
    \/  /\ updateInfoInDB = "notDone"
        /\ UNCHANGED <<alertReader, ack, contactInactiveReaders>>
    
Next ==
    /\ UpdateStatus
    /\ CheckTagStatus
    /\ CheckReaderStatus
    /\ TypeOK

    
Spec == Init /\ [][Next]_Var


=============================================================================
\* Modification History
\* Last modified Mon Nov 08 18:43:27 IST 2021 by ubuntu
\* Created Mon Nov 08 18:42:17 IST 2021 by ubuntu

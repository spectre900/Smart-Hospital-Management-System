-------------------------------- MODULE UML4 --------------------------------
EXTENDS Naturals
VARIABLES rfidScan, medicineList, medicineCount, available, purchaseList, purchaseCount, bill, payment, logTransaction

TypeOK ==
    /\ rfidScan \in {"done", "notDone"}
    /\ medicineList \in {"received", "notReceived"}
    /\ medicineCount \in (0..20)
    /\ available \in {"yes", "no", "undetermined"}
    /\ purchaseList \in {"finalized", "notFinalized"}
    /\ purchaseCount \in (0..20)
    /\ bill \in {"required", "notRequired", "prepared", "undetermined"}
    /\ payment \in {"done", "notDone"}
    /\ logTransaction \in {"done", "notDone"}
 
Init ==
    /\ rfidScan = "notDone"
    /\ medicineList = "notReceived"
    /\ medicineCount = 0
    /\ available = "undetermined"
    /\ purchaseList = "notFinalized"
    /\ purchaseCount = 0
    /\ bill = "undetermined"
    /\ payment = "notDone"
    /\ logTransaction = "notDone"

Var == <<rfidScan, medicineList, medicineCount, available, purchaseList, purchaseCount, bill, payment, logTransaction>>

GetList ==
    \/  /\ rfidScan = "notDone"
        /\ rfidScan' = "done"
        /\ UNCHANGED <<medicineList, medicineCount>>
    \/  /\ rfidScan = "done"
        /\ medicineList = "notReceived"
        /\ medicineList' = "received"
        /\ medicineCount' \in (0..20)
        /\ UNCHANGED <<rfidScan>>
    \/  /\ rfidScan = "done"
        /\ medicineList = "received"
        /\ UNCHANGED <<rfidScan, medicineList>>

MedicineAvailability ==
    \/  /\ medicineList = "received"
        /\ available = "undetermined"
        /\ medicineCount = 0
        /\ purchaseList' = "finalized"
        /\ UNCHANGED <<available, medicineCount, purchaseCount>>
    \/  /\ medicineList = "received"
        /\ available = "undetermined"
        /\ medicineCount \in (1..20)
        /\ available' \in {"yes", "no"}
        /\ UNCHANGED <<medicineCount, purchaseList, purchaseCount>>
    \/  /\ medicineList = "received"
        /\ available = "yes"
        /\ medicineCount' = medicineCount - 1
        /\ purchaseCount' = purchaseCount + 1
        /\ available' = "undetermined"
        /\ UNCHANGED<<purchaseList>>
    \/  /\ medicineList = "received"
        /\ available = "no"
        /\ medicineCount' = medicineCount - 1
        /\ available' = "undetermined"
        /\ UNCHANGED <<purchaseList, purchaseCount>>
    \/  /\ medicineList = "notReceived"
        /\ UNCHANGED <<available, purchaseList, purchaseCount>>

BillCheckout == 
    \/  /\ purchaseList = "notFinalized"
        /\ UNCHANGED <<bill, payment, logTransaction>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "undetermined"
        /\ purchaseCount = 0
        /\ bill' = "notRequired"
        /\ UNCHANGED <<payment, logTransaction>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "undetermined"
        /\ purchaseCount \in (1..20)
        /\ bill' = "required"
        /\ UNCHANGED <<payment, logTransaction>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "notRequired"
        /\ payment' = "done"
        /\ logTransaction' = "done"
        /\ UNCHANGED <<bill>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "required"
        /\ bill' = "prepared"
        /\ UNCHANGED <<payment, logTransaction>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "prepared"
        /\ payment = "notDone"
        /\ payment' = "done"
        /\ logTransaction' = "done"
        /\ UNCHANGED <<bill>>
    \/  /\ purchaseList = "finalized"
        /\ bill = "prepared"
        /\ payment = "done"
        /\ UNCHANGED <<bill, payment, logTransaction>>

Next ==
    /\ GetList
    /\ MedicineAvailability
    /\ BillCheckout
    /\ TypeOK

    
Spec == Init /\ [][Next]_Var


=============================================================================
\* Modification History
\* Last modified Mon Nov 08 18:40:38 IST 2021 by ubuntu
\* Created Mon Nov 08 18:39:09 IST 2021 by ubuntu

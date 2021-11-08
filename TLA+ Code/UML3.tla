-------------------------------- MODULE UML3 --------------------------------
EXTENDS Naturals
VARIABLES temperature, pulse, bp, oxygenLevel, vitals, location, time

temperatureNormal == (36..38)
pulseNormal == (60..100)
bpNormal == (90..120)
oxygenLevelNormal == (75..100)
medicineTime == {x \in 1..12 : x % 3 = 0}

TypeOK ==
    /\ temperature \in (35..42)
    /\ pulse \in (50..130)
    /\ bp \in (60..150)
    /\ oxygenLevel \in (60..110)
    /\ vitals \in {"normal", "abnormal"}
    /\ location \in {"inside", "outside"}
    /\ time \in (1..12)

Init ==
    /\ temperature \in (35..42)
    /\ pulse \in (50..130)
    /\ bp \in (60..150)
    /\ oxygenLevel \in (60..110)
    /\ vitals = "normal"
    /\ location \in {"inside", "outside"}
    /\ time \in (1..12) 
    
Var == <<temperature, pulse, bp, oxygenLevel, vitals, location, time>>

CheckVitals ==
    \/  /\ temperature \notin temperatureNormal
        /\ vitals' = "abnormal"
        /\ UNCHANGED <<temperature, pulse, bp, oxygenLevel>>
    \/  /\ pulse \notin pulseNormal
        /\ vitals' = "abnormal"
        /\ UNCHANGED <<temperature, pulse, bp, oxygenLevel>>
    \/  /\ bp \notin bpNormal
        /\ vitals' = "abnormal"
        /\ UNCHANGED <<temperature, pulse, bp, oxygenLevel>>
    \/  /\ oxygenLevel \notin oxygenLevelNormal
        /\ vitals' = "abnormal"
        /\ UNCHANGED <<temperature, pulse, bp, oxygenLevel>>
    \/  /\ temperature \in temperatureNormal
        /\ pulse \in pulseNormal
        /\ bp \in bpNormal
        /\ oxygenLevel \in oxygenLevelNormal
        /\ vitals' = "normal"
        /\ UNCHANGED <<temperature, pulse, bp, oxygenLevel>>

RingAlarm == TRUE

Alarm == 
    \/  /\ vitals = "abnormal"
        /\ RingAlarm
        /\ vitals' = "normal"
        /\ UNCHANGED <<location>>
    \/  /\ location = "outside"
        /\ RingAlarm
        /\ UNCHANGED <<location>>
    \/  /\ vitals = "normal"
        /\ location = "inside"
        /\ UNCHANGED <<location>>

MedicineTime == 
    \/  /\ time \in medicineTime
        /\ RingAlarm
        /\ time' = (time + 1) % 12
    \/  /\ time \notin medicineTime
        /\ time' = (time + 1) % 12

Next ==
    /\ CheckVitals
    /\ MedicineTime
    /\ Alarm
    /\ TypeOK
    
    
Spec == Init /\ [][Next]_Var
=============================================================================
\* Modification History
\* Last modified Tue Sep 28 17:39:41 IST 2021 by ubuntu
\* Created Sat Sep 25 23:49:24 IST 2021 by ubuntu


# Smart Hospital Management System

## Overview

Smart Hospitals are gradually becoming necessities in the present world due to the massive advancements in technology happening all over the world. Such systems not only provide better clinical care to each and every patient but also ensure a smooth and systematic interaction between the doctors and patients. Further, existing hospital management systems sometimes have serious limitations as they are often operated manually without proper testing and can have undetected loopholes, which may pose serious threats later on. These threats are handled in Smart Hospital Management System. In this paper, we propose a Smart Hospital Management System which utilizes RFID tags as the core of the system to ensure seamless communication between different entities. This system has been developed using UML. NFA has been used to understand the working of the system. The formal specification of the system has been done using TLA+ language and then verification is done using TLC model checker to ensure that there are no loopholes present in the system.

## Project Structure

Inside the project directory:

a. Activity Diagrams --> Directory containing the UML activity diagram of each subsystem.  
	--> checkup.png - Activity diagram of subsystem 1: 'Initial Check-up and Test Recommendation'  
	--> diagnosis.png - Activity diagram of subsystem 2: 'Disease Diagnosis and Medicine Prescription'  
	--> monitoring.png - Activity diagram of subsystem 3: 'Patient Monitoring system'  
	--> dispensing.png - Activity diagram of subsystem 4: 'Medicine Dispensing system'  
	--> rfid-monitoring.png  - Activity diagram of subsystem 5: 'RFID Monitoring system'  

b. TLA+ Code --> Directory containing the formal specification of each subsystem as TLA+ file and pretty printed format (PDF file)  
	--> UML1.tla, UML1.pdf - Formal specification of subsystem 1 (TLA+ file, pretty printed pdf file)  
	--> UML2.tla, UML2.pdf - Formal specification of subsystem 2 (TLA+ file, pretty printed pdf file)  
	--> UML3.tla, UML3.pdf - Formal specification of subsystem 3 (TLA+ file, pretty printed pdf file)  
	--> UML4.tla, UML4.pdf - Formal specification of subsystem 4 (TLA+ file, pretty printed pdf file)  
	--> UML5.tla, UML5.pdf - Formal specification of subsystem 5 (TLA+ file, pretty printed pdf file)  

c. NFA and Fault Tree --> Directory containing fault tree, nfa and transition table.  
	--> fault-tree.png - Fault tree of hospital management system  
	--> nfa.png - NFA diagram for subsystem 1  
	--> transition-table.png - Transition function table for subsystem 1  

d. TLC Model Checker results --> Directory containing the the results obtained from TLC Model Checker after verifying and validating the TLA+ formal specification of each subsystem.  
	--> 1.png - Results for subsystem 1  
	--> 2.png - Results for subsystem 2  
	--> 3.png - Results for subsystem 3  
	--> 4.png - Results for subsystem 4  
	--> 5.png - Results for subsystem 5  

## Instructions  

Steps to run the TLA+ code:  

--> Download TLA+ Toolbox  

1) Go to https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1  
2) Download the .deb file, extract and install the application  

--> Executing .tla files  

1) Go to Project --> TLA+ Code folder in our project folder.  
2) Double click on any .tla file you wish to open. The TLA+ toolbox will automatically open.  
3) A pop-up appears stating "New TLA+ Specification". Click on Finish.  
4) Create a new model by clicking on 'TLC Model Checker'->'New Model' in the toolbar.  
5) Click on the small green button (run symbol) which runs TLC on the model.   
6) The TLC model checker will verify the model and display the final results.  

## Purpose  

The project 'Smart Hospital Management System' has been created as a mini project for the course IT303- Software Engineering.  

## Contributors  

- Pratham Nayak (191IT241)  
- Aprameya Dash (191IT209)  
- Suyash Chintawar (191IT109)  
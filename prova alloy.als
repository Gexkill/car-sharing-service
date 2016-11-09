////////////////////////////////ENUMS///////////////////////////////////////////


enum CarStatus {
	AVAILABLE,
	UNAVAILABLE
}
enum LotStatus {
	EMPTY,
	USED
}

enum ReservationStatus{
EXPIRED,
ACTIVE
}


////////////////////////////////PREDICATES///////////////////////////////////////////


sig ValidString{}


sig  Supervisor {
	//SupervisorID : Int,
	manages:  set Car
	}{
}

sig RegisteredUser {
	name:  one ValidString,
	//books : lone Reservation,
	creditCard: one Int,
	position: one Position
}{
	#creditCard>0
}

sig ReservationDB{
	contains: set Reservation
}

sig Reservation  {
	reservationID : Int,
	bookedBy: one RegisteredUser,
	relatedBy: one Car,
	reservationStatus: one ReservationStatus
	}{
	reservationID>0
}

sig Position {
	position_x: one Int,
	position_y: one Int
}

sig Car {
	carID: Int,
	parkedInto: lone ParkingLot,
	position: one Position,
	carStatus: one CarStatus,
	}{
	carID>=0
}

sig SafeArea {       //*********GAB
	contains: set ParkingLot
}
{
#contains > 0
}

sig ParkingLot {
	//	lotNumber : Int , *********GAB
	safeArea : one SafeArea, 
	position : one Position,  //********* GAB
	status: one LotStatus
	}

sig CHParkingLot extends ParkingLot{

}


////////////////////////////////FACTS///////////////////////////////////////////



// There aren't duplicated Cars
fact noDuplicatedCar {
	no car1 , car2 : Car |(car1!=car2)&&( car1.carID = car2.carID)
}

/*Two parking lot with the same number must be in different Safe Areas  *****************GAB
fact noClonedParkingLot {
	no parkingLoot1 , parkingLoot2 : ParkingLot |(parkingLoot1!=parkingLoot2)&&( parkingLoot1.lotNumber = parkingLoot2.lotNumber)&&
	( parkingLoot1.safeArea = parkingLoot2.safeArea)
}*/

// Two car can't be parked at the same ParkingLot
fact noAbusedParkingLot {
	no  car1,car2 : Car |(car1!=car2)&&( car1.parkedInto=car2.parkedInto)
}

//Check for correct Pl's statuses
fact PLStatusesconsistency{
	all pl :  ParkingLot | (no c: Car | (c.parkedInto=pl))=>(pl.status!=USED) else (pl.status=USED) 
}

// A parked car must have the same position of a parkingLot
fact carAndLotInTheSameZone{
	all c : Car |#c.parkedInto>0 => (  c.position=c.parkedInto.position)   //**********GAB
}
fact carNotParkedHasNoSamePositionOfPL {
	all c : Car, pl: ParkingLot |#c.parkedInto=0 => (  c.position != pl.position)   //**********GAB
}

// No cloned reservations
fact noClonedReservations {
	no reservation1 , reservation2 : Reservation |(reservation1!=reservation2)&&( reservation1.reservationID = reservation2.reservationID)
}

// There's at least a Safe Area in the world
fact atLeastASafeArea{
	#SafeArea>0
}

// There's at least a car in the world *********GAB
fact atLeastACar{
	#Car>0
}

/* And no SafeAreas are without a ParkingLot*********GAB
fact atLeastAPLInSafeArea{
all s: SafeArea | some pl : ParkingLot | (pl.safeArea=s)
}*/

//containment relation must be bidirectional ********** GAB
fact bidirectional1{
	all s: SafeArea, pl: s.contains | pl.safeArea = s
}
fact bidirectional2{
	all pl: ParkingLot, s: pl.safeArea | pl in s.contains
}

// different parkinglot must have different positions***********GAB
fact PLUnity{
no pl1, pl2 : ParkingLot |(pl1!=pl2) && (pl1.position = pl2.position)
}

// different car must have different positions***********GAB
fact CarNotSovrapposed{
no c1, c2 : Car |(c1!=c2) && (c1.position = c2.position)
}

//There's only a Supervisor
fact thereIsOnlyASupervisor{
	#Supervisor=1
}

//Every car is managed by the Supervisor
fact everyCarIsManaged{
	all c : Car | c in Supervisor.manages
}

//Every reservation is stored, even the Expired ones
fact theReservationDBContainsAllTheReservations{
	all r: Reservation | one rDB: ReservationDB | r in rDB.contains
}

// A user can't have two "Active" reservations
fact{
	no r1, r2: Reservation |(  (r1!=r2)&&(r1.reservationStatus=ACTIVE)&& (r2.reservationStatus=ACTIVE))&&(r1.bookedBy=r2.bookedBy)
}

//A car should be "Active" for just one reservation at a time
fact{
	no r1, r2: Reservation |(  (r1!=r2)&&(r1.reservationStatus=ACTIVE)&& (r2.reservationStatus=ACTIVE))&&(r1.relatedBy=r2.relatedBy)
}

//If a car is being used, should be "Unavailable"
// we don't say the opposite, because a car could be Unavailable for other reasons, unrelated to the Reservation (e.g. battery)
fact {
	all r : Reservation |(r.reservationStatus=ACTIVE)=>(r.relatedBy.carStatus=UNAVAILABLE)
}


////////////////////////////////ASSERTIONS///////////////////////////////////////////


pred show{}

//A Car Should Be in the same zone of his parkingLot
assert zoneConsistency{
	all c : Car ,  zone1 : c.parkedInto , zone2 :  c.parkedInto |(zone1=zone2)
}
//check zoneConsistency for 10


//A Car parked in a ParkingLot, marks it as USED			*******GAB
assert plConsistency{
	no c: Car | (#c.parkedInto>0 && c.parkedInto.status=EMPTY)
}
//check plConsistency for 5

assert plConsistency3{							//***********GAB
	no c: Car, pl: ParkingLot | (c.position=pl.position && pl.status=EMPTY)
}
//check plConsistency3 for 5

//An empty PL should be empty			???????????????????????????????????????????????????????????? non va 
assert plConsistency2{
	all c: Car | all pl: ParkingLot  | ((#c.parkedInto>0)&&(c.parkedInto!=pl))=>(pl.status!=USED)
}
//check plConsistency2 






/*assert reservationConsistency{
//	no r1,r2 : Reservation |(r1!=r2)&&( r1.relatedBy =  r2.relatedBy)&&(r1.reservationStatus=ACTIVATED)&&(r2.reservationStatus=ACTIVATED)
}*/


assert noReservationActive{
	 	no r1, r2, r3: Reservation |(r1!=r2)&&(r2!=r3)&&(r1!=r3)&&(r1.reservationStatus=ACTIVE)&&(r2.reservationStatus=ACTIVE)&&(r3.reservationStatus=ACTIVE)
}
check noReservationActive for 5



///////////////////////////////////////////////////////////////////////////////////


run show for 10

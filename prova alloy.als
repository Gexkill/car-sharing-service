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
	manages:  set Car
	}{
}

sig RegisteredUser {
	name:  one ValidString,
	creditCard: one Int,
	position: one Position
}{
	#creditCard>0
}

sig ReservationDB{
	contains: set Reservation
}{
#ReservationDB=1
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

sig SafeArea {      
	contains: set ParkingLot
}
{
#contains > 0
}

sig ParkingLot {
	safeArea : one SafeArea, 
	position : one Position, 
	status: one LotStatus
	}

sig CHParkingLot extends ParkingLot{

}


////////////////////////////////FACTS///////////////////////////////////////////


// There's at least a Safe Area in the world
fact atLeastASafeArea{
	#SafeArea>0
}

// There's at least a car in the world
fact atLeastACar{
	#Car>0
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

// There aren't duplicated Cars
fact noDuplicatedCar {
	no car1 , car2 : Car |(car1!=car2)&&( car1.carID = car2.carID)
}

// No cloned reservations
fact noClonedReservations {
	no reservation1 , reservation2 : Reservation |(reservation1!=reservation2)&&( reservation1.reservationID = reservation2.reservationID)
}

// different parkinglot must have different positions
fact PLUnity{
no pl1, pl2 : ParkingLot |(pl1!=pl2) && (pl1.position = pl2.position)
}

// different car must have different positions
fact CarNotSovrapposed{
no c1, c2 : Car |(c1!=c2) && (c1.position = c2.position)
}

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
	all c : Car |#c.parkedInto>0 => (  c.position=c.parkedInto.position)  
}
fact carNotParkedHasNoSamePositionOfPL {
	all c : Car, pl: ParkingLot |#c.parkedInto=0 => (  c.position != pl.position)  
}

//containment relation must be bidirectional 
fact bidirectional1{
	all s: SafeArea, pl: s.contains | pl.safeArea = s
}
fact bidirectional2{
	all pl: ParkingLot, s: pl.safeArea | pl in s.contains
}

// A user can't have two "Active" reservations
fact{
	no r1, r2: Reservation |(  (r1!=r2)&&(r1.reservationStatus=ACTIVE)&& (r2.reservationStatus=ACTIVE))&&(r1.bookedBy=r2.bookedBy)
}

//A car should be related for just one "ACTIVE" reservation at a time
fact{
	no r1, r2: Reservation |(  (r1!=r2)&&(r1.reservationStatus=ACTIVE)&& (r2.reservationStatus=ACTIVE))&&(r1.relatedBy=r2.relatedBy)
}

//A car should be "Available" only if it's parked in a safe area
fact CarAvailableOnlyIfInSafeArea{
no c: Car | c.parkedInto = none && c.carStatus=AVAILABLE
}

//If a car is being used, should be "Unavailable"
// we don't say the opposite, because a car could be Unavailable for other reasons, unrelated to the Reservation (e.g. battery)
fact {
	all r : Reservation |(r.reservationStatus=ACTIVE)=>(r.relatedBy.carStatus=UNAVAILABLE)
}


////////////////////////////////ASSERTIONS///////////////////////////////////////////


pred show{}

// A parking lot whose position coincides with the position of a car, should not be marked as empty
assert plConsistency{						
	no c: Car, pl: ParkingLot | (c.position=pl.position && pl.status=EMPTY)
}
check plConsistency for 5

//A car whose position does not coincide with any parking lot's position should be UNAVAILABLE
assert carOutsidePLUnavailable{
	no c: Car | c.position&ParkingLot.position = none && c.carStatus= AVAILABLE
}
check carOutsidePLUnavailable for 5

// active reservations should refers to different cars and different users
assert differencesBetweenActiveRes{
no r1, r2: Reservation| (r1!=r2)&&(r1.reservationStatus=ACTIVE)&&(r2.reservationStatus=ACTIVE)&&((r1.bookedBy=r2.bookedBy)||(r1.relatedBy=r2.relatedBy))
}
check differencesBetweenActiveRes for 5

assert noReservationActive{
	 	no r1, r2, r3: Reservation |(r1!=r2)&&(r2!=r3)&&(r1!=r3)&&(r1.reservationStatus=ACTIVE)&&(r2.reservationStatus=ACTIVE)&&(r3.reservationStatus=ACTIVE)
}
check noReservationActive for 5

assert noCarAvailable{
	 	no r1, r2, r3: Car|(r1!=r2)&&(r2!=r3)&&(r1!=r3)&&(r1.carStatus=AVAILABLE)&&(r2.carStatus=AVAILABLE)&&(r3.carStatus=AVAILABLE)
}
check noCarAvailable for 5



///////////////////////////////////////////////////////////////////////////////////


run show for 10 but 3 RegisteredUser

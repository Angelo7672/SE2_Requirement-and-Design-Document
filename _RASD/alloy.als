sig Name{}
sig Surname{}
sig Email{}
sig RMPHandle{}
sig RMPRepo{}
abstract sig User {
    name: one Name,
    surname: one Surname,
    email: one Email,
}
sig Team{
    students: some Student,
    tournament: one Tournament
}
one sig Platform{
    students: set Student,
    educators: set Educator,
    tournaments: set Tournament
}
sig Battle{
    repo: one RMPRepo
}
sig Tournament{
    battles: set Battle,
    badges: set Badge,
    educators: some Educator
}
sig RMP{}

sig Educator extends User{}
sig Student extends User{
    rmpHandle: one RMPHandle,
    badges: set Badge
}
sig Description{}

sig Badge{
    educator: one Educator,
    name: one Name,
    description: one Description
}
sig Score{}


fact AllConnectedToPlatform {
    all s: Student | s in Platform.students
    all e: Educator | e in Platform.educators
    all t: Tournament | t in Platform.tournaments
}

fact descriptionUniqueForBadge{
    all b1: Badge, b2: Badge | b1!=b2 <=> (b1.description != b2.description)
}

fact emailUnique{
    all u1: User, u2: User | u1!=u2 <=> (u1.email != u2.email)
}

fact eachUserHasCredentials{
    no u:User | (u.name = none) and (u.surname = none) and (u.email = none)
}

fact peopleNameNoObjectName{
    all u:User, b:Badge | u.name != b.name
}

/*tutti i team che contengono uno student devono essere di Tournament diversi*/

/*non esistono due team con lo stesso student che siano nello stesso tournament*/
/*due team sono nello tournament se e solo se i loro student sono diversi*/
/*fact teamWithSameStudentDifferentTournament{
    all t1,t2:Team |  (t1.tournament = t2.tournament) <=> (t1.students != t2.students)
}*/
/*fact allStudentsInPlatform{
    all s: Student, p: Platform |
        p.students = s
}

fact allEducatorsInPlatform{
    all e: Educator, p: Platform |
        p.educators = e
}

fact allTournamentsInPlatform{
    all t: Tournament, p: Platform |
        p.tournaments = t
}


fact noPlatformNoEntities{
    all  s: Student, e: Educator, t: Tournament, b: Battle, n: Name, su: Surname, em: Email, rh: RMPHandle, r: RMP |
    (no Platform implies (#s = 0 and #e = 0 and #t = 0 and #b = 0 and #n = 0 and #su = 0 and #em = 0 and #rh = 0 and #r = 0))
}

fact allRefersToPlatform{
   all  s: Student, e: Educator, t: Tournament |
   (#Platform.students = 0 implies no s) and (#Platform.educators = 0 implies no e) and (#Platform.tournaments = 0 implies no t)
   and (#s > 0 implies #Platform.students > 0) and (#e > 0 implies #Platform.educators > 0) and (#t > 0 implies #Platform.tournaments > 0)
}
*/

pred show{}

/*pred show[p: Platform]{
   // #p.students > 1
    //#p.educators > 1
    #p.tournaments > 1
}*/


run show for 5 //but 5 Student, 5 Educator, 5 Tournament
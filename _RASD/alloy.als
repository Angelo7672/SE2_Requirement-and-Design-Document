sig Name{}
sig Surname{}
sig Email{}
sig RMPHandle{}
sig RMPRepo{}
abstract sig User {
    name: one Name,
    surname: one Surname,
    email: one Email,
    rmpHandle: one RMPHandle
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
    badges: set Badge
}
sig Description{}

sig Badge{
    educator: one Educator,
    name: one Name,
    description: one Description
}
sig Score{}

fact SurnameBelongsToUser{
    all s: Surname | s in User.surname
}

fact EmailBelongsToUser{
    all e: Email | e in User.email
}

fact AllConnectedToPlatform {
    all s: Student | s in Platform.students
    all e: Educator | e in Platform.educators
    all t: Tournament | t in Platform.tournaments
}

fact battlesHaveDifferentRMPRepos{
    all disj b1: Battle, b2: Battle | b1.repo = b2.repo iff b1 = b2
}

fact battleIsPartOfOneTournament{
    all b1: Battle | one t1: Tournament | b1 in t1.battles
}

fact tournamentHasAtLeastOneBattle{
    all t: Tournament | #t.battles > 1
}

fact RMPRepoIsPartOfOnlyOneBattle{
    all r: RMPRepo | one b1: Battle | b1.repo = r
}

assert noBattlesHaveSameRepo{
    no b1: Battle, b2: Battle | b1.repo = b2.repo
}

check noBattlesHaveSameRepo

fact battlesHaveDifferentRMPRepos{
    all disj b1: Battle, b2: Battle | b1.repo = b2.repo iff b1 = b2
}

fact battleIsPartOfOneTournament{
    all b1: Battle | one t1: Tournament | b1 in t1.battles
}

fact tournamentHasAtLeastOneBattle{
    all t: Tournament | #t.battles > 1
}

fact RMPRepoIsPartOfOnlyOneBattle{
    all r: RMPRepo | one b1: Battle | b1.repo = r
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
fact DifferentStudentsInSameTournament {
    all disj t1, t2: Team | all s:Student | (t1.tournament = t2.tournament) <=> !(s in t1.students and s in t2.students)
}

fact RMPHandleBelongsToUser {
    all r: RMPHandle | r in User.rmpHandle
}

fact RMPHandleIsPersonal{
    all disj u1, u2: User | u1.rmpHandle != u2.rmpHandle
}


//pred show{}

pred show[p: Platform]{
    //#p.students > 1
    //#p.educators > 1
    //#p.tournaments > 1
    #Team > 1
}


run show for 5
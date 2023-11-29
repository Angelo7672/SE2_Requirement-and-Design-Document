sig Name{}
sig Surname{}
sig Email{}
sig RMPHandle{}
abstract sig User {
    name: one Name,
    surname: one Surname,
    email: one Email,
}
sig Team{
    students: some Student
}
one sig Platform{
    students: set Student,
    educators: set Educator,
    tournaments: set Tournament
}
sig Battle{
    teams: some Team
}
sig Tournament{
    battles: set Battle
}
sig RMP{}

sig Educator extends User{}
sig Student extends User{
    rmpHandle: one RMPHandle
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
pred show{}

run show for 2
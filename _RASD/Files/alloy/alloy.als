sig Name{}
sig Surname{}
sig Email{}
sig RMPHandle{
    rmp: one RMP,
}
sig RMPRepo{
    rmp: one RMP
}
abstract sig User {
    name: one Name,
    surname: one Surname,
    email: disj one Email,
    rmpHandle: disj one RMPHandle
}
sig Team{
    students: some Student,
    tournamentScore: one TournamentScore,
    battleScore: set BattleScore,
    repos: some RMPRepo
}
one sig Platform{
    students: set Student,
    educators: set Educator,
    tournaments: set Tournament
}
sig Battle{
    repo: disj one RMPRepo,
    scores: some BattleScore
}
sig Tournament{
    battles: set Battle,
    badges: set Badge,
    educators: some Educator,
    teams: some Team,
    scores: some TournamentScore
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
    description: disj one Description
}
abstract sig Score{
    points: one Int
}{
    points >= 0
}

sig BattleScore extends Score{}
sig TournamentScore extends Score{}

--------------------------------------------------
//Facts
// User facts
fact SurnameBelongsToUser{
    all s: Surname | s in User.surname
}

fact EmailBelongsToUser{
    all e: Email | e in User.email
}

fact RMPHandleBelongsToUser{
    all e: RMPHandle | e in User.rmpHandle
}

fact RMPHandleIsPersonal{
    all disj u1, u2: User | u1.rmpHandle != u2.rmpHandle
}

fact AllConnectedToPlatform {
    all s: Student | s in Platform.students
    all e: Educator | e in Platform.educators
    all t: Tournament | t in Platform.tournaments
}

fact peopleNameNoObjectName{
    all u:User, b:Badge | u.name != b.name
}

// Tournament facts

fact tournamentHasAtLeastOneBattle{
    all t: Tournament | #t.battles > 0
}

fact NoStudentIsInTwoTeamsInSameTournament {
    all to: Tournament | all disj t1, t2 :to.teams | all s1 : t1.students | all s2 : t2.students | s1 != s2
}

fact TeamIsPartOfOneTournament{
    all t: Team | one to: Tournament | t in to.teams
}

fun allReposFromTournament[t: Tournament]: set RMPRepo{
    {r: RMPRepo | r in t.battles.repo} + {r: RMPRepo | r in t.teams.repos}
}

fun allRmpHandlesFromTournament[t: Tournament]: set RMPHandle{
    {r: RMPHandle | r in t.educators.rmpHandle} + {r: RMPHandle | r in t.teams.students.rmpHandle}
}

fact uniqueRMPinATournament{
    all to: Tournament | all r :allReposFromTournament[to]| all h :allRmpHandlesFromTournament[to]| r.rmp = h.rmp and one r.rmp
}

fact allTeamsDontShareRepos{
    all disj t1, t2 :Team | all r1: t1.repos | all r2: t2.repos | r1 != r2
}

fact allTeamsDontShareRepos{
    all disj t1, t2 :Team | all r1: t1.repos | all r2: t2.repos | r1 != r2
}

fact noTeamWorksOnBattleRepo{
    all t: Team | all b: Battle | all r: t.repos | r != b.repo
}

// Battle facts

fact battleIsPartOfOneTournament{
    all b1: Battle | one t1: Tournament | b1 in t1.battles
}

fact TeamTournamentScoreIsUnique{
    all t: TournamentScore | t in Team.tournamentScore
    all disj t1, t2: Team | t1.tournamentScore != t2.tournamentScore
}

fact noAloneDescriptions{
    some b:Badge | all d:Description | d in b.description
}

fact noAloneNames{
    some b:Badge | some u:User | all n:Name | (n in b.name) or (n in u.name)
}

fact allBattlescoreBelongstoOneTeam{
    all bs:BattleScore | one t:Team | bs in t.battleScore
}

fact allBattlescoreBelongstoOneBattle{
    all bs:BattleScore | one b:Battle | bs in b.scores
}

fact allBattlescoreBelongstoOneTeamAndOneBattle{
    all bs:BattleScore | one to: Tournament | one t:to.teams | one b:to.battles | bs in t.battleScore and bs in b.scores
}

fact allTournamentscoreBelongstoOneTeam{
    all ts:TournamentScore | one t:Team | ts in t.tournamentScore
}

fact allTournamentscoreBelongstoOneBattle{
    all ts:TournamentScore | one to:Tournament | ts in to.scores
}

fact allTournamentscoreBelongstoOneTeamAndOneBattle{
    all ts:TournamentScore | one to: Tournament | one t:to.teams | ts in t.tournamentScore and ts in to.scores
}

fact allTeamsHaveATournamentScore{
    all t:Team | one ts:TournamentScore | ts in t.tournamentScore
}

fact allBattleTeamCoupleHaveABattleScore{
    all to: Tournament | all t:to.teams | all b:to.battles | one bs:BattleScore| bs in t.battleScore and bs in b.scores
}

/*fact tournamentScoreAreSumOfBattleScores{
    all ts: TournamentScore | all t: Team | (ts.points in t.tournamentScore.points) <=> (ts.points = sum(t.battleScore.points))
}*/

--------------------------------------------------
//Assertions

//GP2: Allow Educators to create tournaments
assert newTournament{
    no t:Tournament | t not in Platform.tournaments
}
check newTournament for 10  //VALID
//GP4: Allow Educators to create battles 
assert newBattle{
    no b:Battle | all t:Tournament | b not in t.battles
}
check newBattle for 6 //VALID
//GP5: Allow Educators to create badges
assert newBadge{
    (no b:Badge | all t:Tournament | b not in t.badges) or (all b: Badge | one e: Educator | e = b.educator)
}
check newBadge for 6
//GS2: Allow Students to be rewarded for special achievement 
assert studentReceivesSpecialAchievements{
    all s: Student | #s.badges >= 0
}
check studentReceivesSpecialAchievements for 6 //VALID

//GS4: Allow Students to have work evaluated
assert haveWorkEvaluated{
    all to: Tournament | all t: to.teams | #t.tournamentScore = 1 and #t.battleScore = #to.battles
}
check haveWorkEvaluated for 6 //VALID

assert noBattlesHaveSameRepo{
    all disj b1, b2: Battle | b1.repo != b2.repo
}

check noBattlesHaveSameRepo
--------------------------------------------------
//Predicates
pred show{
    //#Platform.tournaments = 1
    #Tournament = 2
    #Team = 6
    #Battle = 6
}

run show for 20
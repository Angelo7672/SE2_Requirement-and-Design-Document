// ---- SIGNATURES ----


sig Name{}

sig Surname{}

sig Email{}

sig RMPHandle{
    rmp: one RMP,
}

abstract sig User {
    name: one Name,
    surname: one Surname,
    email: disj one Email,
    rmpHandle: disj one RMPHandle
}

sig Educator extends User{}

sig Student extends User{
    badges: set Badge
}

one sig Platform{   //the platform is unique
    students: set Student,
    educators: set Educator,
    tournaments: set Tournament
}

sig Team{
    students: some Student,
    tournamentScore: one TournamentScore,
    battleScore: set BattleScore,
    repos: some RMPRepo
}

abstract sig Score{
    points: one Int
}{
    points >= 0     //the score is positive
}

sig BattleScore extends Score{}

sig TournamentScore extends Score{}

sig RMPRepo{
    rmp: one RMP
}

sig Battle{
    repo: disj one RMPRepo,
    scores: some BattleScore
}

sig Rules{}

sig Badge{
    educator: one Educator,
    name: one Name,
    rules: disj one Rules
}

sig Tournament{
    battles: set Battle,
    badges: set Badge,
    educators: some Educator,
    teams: some Team,
    scores: some TournamentScore
}

sig RMP{}

//--------------------------------------------------------------------------------

// ---- FACTS ----


// User facts

//a surname always has a user
fact SurnameBelongsToUser{
    all s: Surname | s in User.surname
}

//an email always has a user
fact EmailBelongsToUser{
    all e: Email | e in User.email
}

//a RMP handle always has a user
fact RMPHandleBelongsToUser{
    all e: RMPHandle | e in User.rmpHandle
}

//there cannot exist a rmp handle shared between to users
fact RMPHandleIsPersonal{
    all disj u1, u2: User | u1.rmpHandle != u2.rmpHandle
}

//all the students, educators and tournaments belongs to the platform
fact AllConnectedToPlatform {
    all s: Student | s in Platform.students
    all e: Educator | e in Platform.educators
    all t: Tournament | t in Platform.tournaments
}

//there cannot exists a badge with the same name of a user
fact peopleNameNoObjectName{
    all u:User, b:Badge | u.name != b.name
}

// Tournament facts

//all tournaments have at least one battle
fact tournamentHasAtLeastOneBattle{ 
    all t: Tournament | #t.battles > 0
}

//there cannot exists a student in two different teams in the same tournament
fact NoStudentIsInTwoTeamsInSameTournament {
    all to: Tournament | all disj t1, t2 :to.teams | all s1 : t1.students | all s2 : t2.students | s1 != s2
}

//a team can exists only in the context of a tournament
fact TeamIsPartOfOneTournament{
    all t: Team | one to: Tournament | t in to.teams
}

//get all RMP repos present in the context of a tournament, the team ones and Battle ones
fun allReposFromTournament[t: Tournament]: set RMPRepo{
    {r: RMPRepo | r in t.battles.repo} + {r: RMPRepo | r in t.teams.repos}
}

//get all RMP handles present in the context of a tournament, the student ones and educator ones
fun allRmpHandlesFromTournament[t: Tournament]: set RMPHandle{
    {r: RMPHandle | r in t.educators.rmpHandle} + {r: RMPHandle | r in t.teams.students.rmpHandle}
}

// all tournament repos and rmp handles are in the same rmp 
fact uniqueRMPinATournament{
    all to: Tournament | all r :allReposFromTournament[to]| all h :allRmpHandlesFromTournament[to]| r.rmp = h.rmp
}

//a RMP repo belongs to only a team
fact allTeamsDontShareRepos{
    all disj t1, t2 :Team | all r1: t1.repos | all r2: t2.repos | r1 != r2
}

//the RMP repo of the battle isn't use from the teams
fact noTeamWorksOnBattleRepo{
    all t: Team | all b: Battle | all r: t.repos | r != b.repo
}

//a RMP repo belongs to a Team or to a Battle
fact noRepoAlone{
    all r: RMPRepo | (r in Team.repos) or (r in Battle.repo)
}

// Battle facts

//there cannot exists a battle that isn't part of a tournament
fact battleIsPartOfOneTournament{
    all b1: Battle | one t1: Tournament | b1 in t1.battles
}

// Score facts

//a tournament score is associated uniquely to a team 
fact TeamTournamentScoreIsUnique{
    all t: TournamentScore | t in Team.tournamentScore
    all disj t1, t2: Team | t1.tournamentScore != t2.tournamentScore
}

//there cannot exists a battle score without a team
fact allBattlescoreBelongstoOneTeam{
    all bs:BattleScore | one t:Team | bs in t.battleScore
}

//there cannot exists a battle score without a battle
fact allBattlescoreBelongstoOneBattle{
    all bs:BattleScore | one b:Battle | bs in b.scores
}

//a battle score is uniquely associated to only one battle and only one team
fact allBattlescoreBelongstoOneTeamAndOneBattle{
    all bs:BattleScore | one to: Tournament | one t:to.teams | one b:to.battles | bs in t.battleScore and bs in b.scores
}

//there cannot exists a tournament score without a team
fact allTournamentscoreBelongstoOneTeam{
    all ts:TournamentScore | one t:Team | ts in t.tournamentScore
}

//there cannot exists a tournament score without a battle
fact allTournamentscoreBelongstoOneBattle{
    all ts:TournamentScore | one to:Tournament | ts in to.scores
}

//a tournament score is uniquely associated to only one tournament and only one team
fact allTournamentscoreBelongstoOneTeamAndOneBattle{
    all ts:TournamentScore | one to: Tournament | one t:to.teams | ts in t.tournamentScore and ts in to.scores
}

//there cannot exists a team without a tournament score
fact allTeamsHaveATournamentScore{
    all t:Team | one ts:TournamentScore | ts in t.tournamentScore
}

//each team in a tournament has a battle score for each battle in the same tournament
fact allBattleTeamCoupleHaveABattleScore{ 
    all to: Tournament | all t:to.teams | all b:to.battles | one bs:BattleScore| bs in t.battleScore and bs in b.scores
}

//the tournament score of a team is equal to the sum of all the battle score of that team
fact tournamentScoreIsSumOfBattleScores{
    all to: Tournament | all t:to.teams | all ts: t.tournamentScore | ts.points = sum[t.battleScore.points]
}

// Badge facts

//there cannot exists a set of rules without a badge connected
fact noAloneDescriptions{
    all r: Rules | r in Badge.rules
}

//there cannot exists a name without a badge or user
fact noAloneNames{
    all n: Name | (n in User.name) or (n in Badge.name)
}

//all the badge belongs to tournaments
fact noBadgeWithoutTournament{
    all b: Badge | b in Tournament.badges
}

//--------------------------------------------------------------------------------------------------------------------

// ---- Assertions ----


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
check newBadge for 6 //VALID

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
check noBattlesHaveSameRepo for 6 //VALID

//-------------------------------------------------------------------------------------------------------------------

// ---- Predicates ----

// simple world to easily see relationships between entities
pred world1{
    #Platform.students = 1
    #Platform.educators = 1
    #Platform.tournaments = 1
    #Tournament = 1
    #Tournament.educators = 1
    #Team = 1
    #Battle = 1
    #Educator = 1
    #Student = 1
    #Student.badges = 1
    #Badge = 1
    #RMP = 1
}

run world1 for 13

// complexer world to see how one tournament behaves with more entities
pred world2{
    #Tournament = 1
    #Tournament.educators > 1
    #Team = 3
    #Battle = 3
    #Educator = 3
    #Student = 5
    #Student.badges = 1
    #Badge = 2
    #RMP = 1
}

run world2 for 13

// more complex world to see how multiple tournaments behave with more entities
pred world3{
    #Tournament = 4
    #Team = 5
    #Battle = 5
    #Educator = 3
    #Student = 7
    #Badge = 3
}

run world3 for 20

pred show{
    #Tournament = 3
    #Team = 6
    #Battle = 6
    #Educator = 4
    #Student = 3
    #Badge > 1
}

// testing world hidden from the reader
run show for 20
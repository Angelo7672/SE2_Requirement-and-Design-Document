sig Name{}
sig Surname{}
sig Email{}
sig RMPHandle{
    repo: RMPRepo
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
    battleScore: set BattleScore
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

// Battle facts

fact battleIsPartOfOneTournament{
    all b1: Battle | one t1: Tournament | b1 in t1.battles
}

/*fact RMPRepoIsPartOfOnlyOneBattle{
    all r: RMPRepo | one b1: Battle | b1.repo = r
}*/

/*fact descriptionUniqueForBadge{
    all disj b1: Badge, b2: Badge | b1.description != b2.description
    //all b1: Badge, b2: Badge | b1!=b2 <=> (b1.description != b2.description)
}*/

/*tutti i team che contengono uno student devono essere di Tournament diversi*/

/*non esistono due team con lo stesso student che siano nello stesso tournament*/
/*due team sono nello tournament se e solo se i loro student sono diversi*/
fact DifferentStudentsInSameTournament {
    all disj to: Tournament | all s:Student | all  disj t1,t2:Team | (t1 in to.teams and t2 in to.teams) <=> !(s in t1.students and s in t2.students)
}

fact TeamHasOnlyOneTournament{
    all t: Team | t in Tournament.teams
    all disj t1, t2: Tournament | all te1: Team | no te2: Team | t1.teams = te1 and t2.teams = te2 and te1 = te2
}

fact TeamIsPartOfOneTournament{
    all t: Team | one to: Tournament | t in to.teams
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


/*fact allBattleScoreBelongsOneABattle{  //+ battleScores ad una Battle, ma una battlescore non a + battle
    all bs: BattleScore | all disj b1, b2:Battle | (bs in b1.scores) <=> (bs not in b2.scores)
    //all bs: BattleScore | all disj b1, b2:Battle | (bs in b1.scores) <=> (bs not in b2.scores)
}

fact aBattleScoreBelongsJustToATeam{
    all bs:BattleScore | all disj t1, t2: Team | (bs in t1.battleScore) <=> (bs not in t2.battleScore)
}

fact battleScoreAlwaysToATeamAndToABattle{
    all bs:BattleScore | one t:Team | one b:Battle | (bs in t.battleScore) and (bs in b.scores)
}

fact tournamentScoreAreSumOfBattleScores{
    all ts: TournamentScore | all t: Team | (ts.points in t.tournamentScore.points) <=> (ts.points = sum(t.battleScore.points))
}
/*fact repoTeamLinkedRepoBattle{

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
    some to: Tournament | some t:Team | (t in to.teams) <=> (t.tournamentScore.points >= 0)
}
check haveWorkEvaluated for 6 //VALID

assert noBattlesHaveSameRepo{
    no disj b1: Battle, b2: Battle | b1.repo = b2.repo
}

check noBattlesHaveSameRepo
--------------------------------------------------
//Predicates
pred show{
    //#Platform.tournaments = 1
    #Tournament = 6
    #Team = 6
}

run show for 10
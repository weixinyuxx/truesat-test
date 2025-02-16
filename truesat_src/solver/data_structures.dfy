include "utils.dfy"
include "../int32.dfy"

trait DataStructures { 
  var variablesCount : Int32.t;
  var clauses : seq<seq<Int32.t>>;
  var clausesCount : Int32.t;
  var clauseLength : array<Int32.t>;

  var truthAssignment : array<Int32.t>; // from 0 to variablesCount - 1, values: -1, 0, 1

  var trueLiteralsCount : array<Int32.t>; // from 0 to |clauses| - 1
  var falseLiteralsCount : array<Int32.t>; // from 0 to |clauses| - 1

  var positiveLiteralsToClauses : array<seq<Int32.t>>; // from 0 to variablesCount - 1
  var negativeLiteralsToClauses : array<seq<Int32.t>>; // frm 0 to variablesCount - 1

  var decisionLevel : Int32.t;

  var traceVariable : array<Int32.t>;
  var traceValue : array<bool>;

  var traceDLStart : array<Int32.t>;
  var traceDLEnd : array<Int32.t>;

  ghost var assignmentsTrace : set<(Int32.t, bool)>;

  predicate validVariablesCount() 
    reads `variablesCount;
  {
    0 < variablesCount < Int32.max
  }

  predicate validLiteral(literal : Int32.t) 
    requires validVariablesCount();
    reads `variablesCount;
  {
    if literal == 0 then false
    else if -variablesCount <= literal && literal <= variablesCount then true
    else false
  }

  predicate validClause(clause : seq<Int32.t>) 
    requires validVariablesCount();
    reads `variablesCount;
  {
    |clause| < Int32.max as int &&
    (forall x, y :: 0 <= x < y < |clause| ==>
      clause[x] != clause[y])
    &&
    (forall literal :: (literal in clause) ==>
      validLiteral(literal))
  }

  predicate validClauses() 
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
  {
    0 < |clauses| == clausesCount as int <= Int32.max as int 
    
    && 

    clauseLength.Length == clausesCount as int 
    
    &&

    (forall i :: 0 <= i < clausesCount ==>
      0 < clauseLength[i] as int == |clauses[i]| < Int32.max as int) 
    
    &&

    forall clause :: (clause in clauses) ==>
      validClause(clause)
  }

  predicate validVariable(variable : Int32.t)
    reads `variablesCount;
    requires validVariablesCount();
  {
    0 <= variable < variablesCount
  }

  predicate validAssignmentTrace()
    reads `variablesCount, `decisionLevel, `traceDLStart, 
          `traceDLEnd, `traceVariable, `traceValue, 
          traceDLStart, traceDLEnd, traceVariable,
          traceValue, `assignmentsTrace;
    requires validVariablesCount();
  {
    validAssignmentTraceBasic() &&
    validTraceDL() &&
    validTraceVariable() &&
    validAssignmentTraceGhost()
  }

  predicate validAssignmentTraceBasic()
    reads `variablesCount, `decisionLevel, `traceDLStart, 
          `traceDLEnd, `traceVariable, `traceValue, 
          traceDLStart, traceDLEnd, traceVariable,
          traceValue;
    requires validVariablesCount();
  {
    0 < variablesCount < Int32.max &&
    -1 <= decisionLevel < variablesCount &&
    
    traceVariable.Length == variablesCount as int &&
    traceValue.Length == variablesCount as int &&
    traceDLStart.Length == variablesCount as int &&
    traceDLEnd.Length == variablesCount as int &&

    traceVariable != traceDLStart &&
    traceVariable != traceDLEnd &&

    traceDLStart != traceDLEnd
  }

  predicate validTraceDL()
    reads `variablesCount, `decisionLevel, `traceDLStart, 
          `traceDLEnd, `traceVariable, `traceValue, 
          traceDLStart, traceDLEnd, traceVariable,
          traceValue;
    requires validVariablesCount();
    requires validAssignmentTraceBasic();
  {
    (forall dl :: 0 <= dl < decisionLevel ==>
      0 <= traceDLStart[dl] < traceDLEnd[dl] <= variablesCount)

    &&

    (decisionLevel >= 0 ==> (
      traceDLStart[0] == 0

      && 

      (0 <= traceDLStart[decisionLevel] <= traceDLEnd[decisionLevel] <= variablesCount)
    ))

    &&

    (forall dl :: 0 < dl <= decisionLevel ==>
      traceDLStart[dl] == traceDLEnd[dl-1])
  }

  predicate validTraceVariable()
    reads `variablesCount, `decisionLevel, `traceDLStart, 
          `traceDLEnd, `traceVariable, `traceValue, 
          traceDLStart, traceDLEnd, traceVariable,
          traceValue;
    requires validVariablesCount();
    requires validAssignmentTraceBasic();
    requires validTraceDL();
  {
    decisionLevel >= 0 ==> (
      (forall i :: 0 <= i < traceDLEnd[decisionLevel] ==> 
        validVariable(traceVariable[i]))

      &&

      (forall i :: 0 <= i < traceDLEnd[decisionLevel] ==> 
        forall j :: 0 <= j < traceDLEnd[decisionLevel] && i != j ==>
          traceVariable[i] != traceVariable[j])
    )
  }

  predicate validAssignmentTraceGhost()
    reads `variablesCount, `decisionLevel, `traceDLStart, 
          `traceDLEnd, `traceVariable, `traceValue, 
          traceDLStart, traceDLEnd, traceVariable,
          traceValue, `assignmentsTrace;
    requires validVariablesCount();
    requires validAssignmentTraceBasic();
    requires validTraceDL();
    requires validTraceVariable(); 
  {
    (decisionLevel == -1 ==> assignmentsTrace == {})

    &&

    (decisionLevel >= 0 ==> (
      (forall i :: 0 <= i < traceDLEnd[decisionLevel] ==> 
        (traceVariable[i], traceValue[i]) in assignmentsTrace)

      &&

      (forall x :: x in assignmentsTrace ==> (
        exists i :: 0 <= i < traceDLEnd[decisionLevel] && 
          (traceVariable[i], traceValue[i]) == x))
    ))
  }

  function convertIntToBool(x : Int32.t) : bool
  {
    if x == 0 then false
    else true
  }

  predicate validValuesTruthAssignment(truthAssignment : seq<Int32.t>)
    reads `variablesCount;
    requires validVariablesCount();
  {
    |truthAssignment| == variablesCount as int &&
    |truthAssignment| <= Int32.max as int &&
    (forall i :: 0 <= i < |truthAssignment| ==>
      -1 <= truthAssignment[i] <= 1) 
  }

  predicate validTruthAssignment()
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd,
          truthAssignment;
    requires validVariablesCount();
    requires validAssignmentTrace();
  {
    validValuesTruthAssignment(truthAssignment[..])
      
    &&

    (forall i  :: 0 <= i < variablesCount &&
                           truthAssignment[i] != -1 ==>
      (i, convertIntToBool(truthAssignment[i])) in assignmentsTrace)

    &&

    (forall i :: 0 <= i < variablesCount &&
                          truthAssignment[i] == -1 ==>
      (i, false) !in assignmentsTrace && (i, true) !in assignmentsTrace)
  }

  function getLiteralValue(truthAssignment : seq<Int32.t>, literal : Int32.t) : Int32.t
    reads `variablesCount;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validLiteral(literal);
  {
    var variable := Utils.abs(literal)-1;

    if (truthAssignment[variable] == -1) then -1
    else if literal < 0 then 1-truthAssignment[variable]
    else truthAssignment[variable]
  }

  predicate isClauseSatisfied(truthAssignment : seq<Int32.t>, clauseIndex : Int32.t) 
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires 0 <= clauseIndex as int < |clauses|;
  {
    assert validClause(clauses[clauseIndex]);
    exists literal :: (literal in clauses[clauseIndex]) &&
      getLiteralValue(truthAssignment, literal) == 1
  }

  function method getVariableFromLiteral(literal : Int32.t) : Int32.t 
    reads this;
    requires validVariablesCount();
    requires validLiteral(literal);
    ensures validVariable(getVariableFromLiteral(literal));
  {
    Utils.abs(literal)-1
  }

  function method convertLVtoVI(literal : Int32.t, value : bool) : (Int32.t, Int32.t) 
    reads this; 
    requires validVariablesCount();
    requires validLiteral(literal);

    ensures validVariable(convertLVtoVI(literal, value).0);
    ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal);
    ensures convertLVtoVI(literal, value).1 in [0,1];
  {
    var variable := getVariableFromLiteral(literal);
    var v := if value then 1 else 0;
    var val := if literal < 0 then 1-v else v;
    
    (variable, val)
  }

  predicate validTrueLiteralsCount(truthAssignment : seq<Int32.t>)
    reads `variablesCount, `clauses, `trueLiteralsCount, `clauseLength, 
          `clausesCount, trueLiteralsCount, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
    trueLiteralsCount.Length == |clauses| &&
    forall i :: 0 <= i < |clauses| ==>
      0 <= trueLiteralsCount[i] == countTrueLiterals(truthAssignment, clauses[i])
  }

  function countUnsetVariables(truthAssignment : seq<Int32.t>) : Int32.t
    requires |truthAssignment| <= Int32.max as int;
    ensures 0 <= countUnsetVariables(truthAssignment) as int <= |truthAssignment| <= Int32.max as int;
  {
    if |truthAssignment| == 0 then 0
    else (
      var ok := if truthAssignment[0] == -1 then 1 else 0;
      ok + countUnsetVariables(truthAssignment[1..])
    )
  }

  function countTrueLiterals(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>) : Int32.t
    reads `variablesCount, `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    ensures 0 <= countTrueLiterals(truthAssignment, clause) as int <= |clause|;
  {
    if |clause| == 0 then 0
    else 
      var ok := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0;
      ok + countTrueLiterals(truthAssignment, clause[1..])
  }

  lemma prop_countTrueLiterals_initialTruthAssignment(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>)
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires forall j :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1;

    ensures countTrueLiterals(truthAssignment, clause) == 0;
  {
    assert forall literal :: literal in clause ==>
      getLiteralValue(truthAssignment, literal) == -1;
    if (|clause| > 0) {
      assert clause[0] in clause;
      assert getLiteralValue(truthAssignment, clause[0]) == -1;
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment, clause[1..]);
    }
  }

  lemma countTrueLiterals0_noLiteralsTrue(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>) 
    requires validVariablesCount();
    requires validClause(clause);
    requires validValuesTruthAssignment(truthAssignment);
    requires countTrueLiterals(truthAssignment, clause) == 0;
    ensures forall literal :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1;
  {
      var k := 0;

      while (k < |clause|) 
        invariant -1 <= k <= |clause|;
        invariant forall k' :: 0 <= k' < k ==> 
          getLiteralValue(truthAssignment, clause[k']) != 1;
        invariant countTrueLiterals(truthAssignment, clause[k..]) == 0;
        decreases |clause| - k;
      {
        k := k + 1;
      }
  }

  lemma countTrueLiteralsX_existsTrueLiteral(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>) 
    requires validVariablesCount();
    requires validClause(clause);
    requires validValuesTruthAssignment(truthAssignment);
    requires countTrueLiterals(truthAssignment, clause) > 0;

    ensures exists literal :: literal in clause && 
              getLiteralValue(truthAssignment, literal) == 1;
  {
    if (countTrueLiterals(truthAssignment, clause) == 0) {
      countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);
      assert forall literal :: literal in clause ==> 
        getLiteralValue(truthAssignment, literal) != 1;
    } else {
      if (getLiteralValue(truthAssignment, clause[0]) != 1) {
        countTrueLiteralsX_existsTrueLiteral(truthAssignment, clause[1..]);  
      } else {
      }
    }
  }

  predicate validFalseLiteralsCount(truthAssignment : seq<Int32.t>)
    reads `variablesCount, `clauses, `falseLiteralsCount, `clauseLength, 
          `clausesCount, falseLiteralsCount, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
    falseLiteralsCount.Length == |clauses| &&
    forall i :: 0 <= i < |clauses| ==>
      0 <= falseLiteralsCount[i] == countFalseLiterals(truthAssignment, clauses[i])
  }

  function countFalseLiterals(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>) : Int32.t
    reads `variablesCount, `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    ensures 0 <= countFalseLiterals(truthAssignment, clause) as int <= |clause|;
  {
    if |clause| == 0 then 0
    else 
      var ok := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0;
      ok + countFalseLiterals(truthAssignment, clause[1..])
  }

  lemma prop_countFalseLiterals_initialTruthAssignment(truthAssignment : seq<Int32.t>, clause : seq<Int32.t>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires forall j :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1;

    ensures countFalseLiterals(truthAssignment, clause) == 0;
  {
    assert forall literal :: literal in clause ==>
              getLiteralValue(truthAssignment, literal) == -1;
    if (|clause| > 0) {
      assert clause[0] in clause;
      assert getLiteralValue(truthAssignment, clause[0]) == -1;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment, clause[1..]);
    }
  }

  predicate validPositiveLiteralsToClauses()
    reads this, positiveLiteralsToClauses, clauseLength;

    requires validVariablesCount();
    requires validClauses();
  {
    positiveLiteralsToClauses.Length == variablesCount as int
    
    &&

    (forall variable : Int32.t :: 0 <= variable as int < positiveLiteralsToClauses.Length ==> 
      validPositiveLiteralToClause(variable, positiveLiteralsToClauses[variable]))

    &&

    (forall variable : Int32.t :: 0 <= variable as int < positiveLiteralsToClauses.Length ==> 
      |positiveLiteralsToClauses[variable]| <= clausesCount as int)
  }

  predicate validPositiveLiteralToClause(variable : Int32.t, s : seq<Int32.t>) 
    reads this, clauseLength; 

    requires validVariablesCount();
    requires validClauses();
    requires 0 <= variable < variablesCount;
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&

    Utils.orderedAsc(s) &&

    (forall clauseIndex :: clauseIndex in s ==>
      variable+1 in clauses[clauseIndex]) &&

    (forall clauseIndex :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in s ==>
      variable+1 !in clauses[clauseIndex])
  }

  predicate validNegativeLiteralsToClauses()
    reads this, negativeLiteralsToClauses, clauseLength;

    requires validVariablesCount();
    requires validClauses();
  {
    negativeLiteralsToClauses.Length == variablesCount as int &&

    forall v :: 0 <= v as int < negativeLiteralsToClauses.Length ==>
      validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])

    &&

    (forall variable : Int32.t :: 0 <= variable as int < negativeLiteralsToClauses.Length ==> 
      |negativeLiteralsToClauses[variable]| <= clausesCount as int)
  }

  predicate validNegativeLiteralsToClause(variable : Int32.t, s : seq<Int32.t>)
    reads this, clauseLength;

    requires validVariablesCount();
    requires validClauses();
    requires 0 <= variable < variablesCount;
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&

    Utils.orderedAsc(s) &&

    (forall clauseIndex :: clauseIndex in s ==>
      -variable-1 in clauses[clauseIndex]) &&

    (forall clauseIndex : Int32.t :: 0 <= clauseIndex as int < |clauses| && 
                                     clauseIndex !in s ==>
      -variable-1 !in clauses[clauseIndex])
  }

  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount,
          positiveLiteralsToClauses, negativeLiteralsToClauses, clauseLength;
  {
    (truthAssignment != trueLiteralsCount) &&
    (truthAssignment != falseLiteralsCount) &&
    (truthAssignment != clauseLength) &&
    (truthAssignment != traceVariable) &&
    (truthAssignment != traceDLStart) &&
    (truthAssignment != traceDLEnd) &&
    (trueLiteralsCount != falseLiteralsCount) &&
    (trueLiteralsCount != clauseLength) &&
    (trueLiteralsCount != traceVariable) &&
    (trueLiteralsCount != traceDLStart) &&
    (trueLiteralsCount != traceDLEnd) &&
    (falseLiteralsCount != clauseLength) &&
    (falseLiteralsCount != traceVariable) &&
    (falseLiteralsCount != traceDLStart) &&
    (falseLiteralsCount != traceDLEnd) &&
    (clauseLength != traceVariable) &&
    (clauseLength != traceDLStart) &&
    (clauseLength != traceDLEnd) &&
    (positiveLiteralsToClauses != negativeLiteralsToClauses)
  }

  predicate valid() 
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, 
          truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, clauseLength,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
  {
    validReferences() &&
    validVariablesCount() && 
    validClauses() &&
    countLiterals(clausesCount) < Int32.max as int &&
    validAssignmentTrace() &&
    validTruthAssignment() &&

    validTrueLiteralsCount(truthAssignment[..]) &&
    validFalseLiteralsCount(truthAssignment[..]) &&

    validPositiveLiteralsToClauses() &&
    validNegativeLiteralsToClauses()
  }

  function countLiterals(clauseIndex : Int32.t) : int
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires 0 <= clauseIndex <= clausesCount;
  {
    if clauseIndex == 0 then 0
    else |clauses[clauseIndex-1]| + countLiterals(clauseIndex-1)
  }

  lemma countLiterals_monotone(cI : Int32.t)
    requires validVariablesCount();
    requires validClauses();
    requires countLiterals(clausesCount) < Int32.max as int;
    requires 0 <= cI <= clausesCount;
    ensures 0 <= cI < clausesCount ==> 
      countLiterals(cI) < countLiterals(cI+1) < Int32.max as int;
    decreases clausesCount - cI;
  {
    if (cI == clausesCount) {
    } else {
      calc < {
        countLiterals(cI); 
        { assert countLiterals(cI + 1) == countLiterals(cI) + clauseLength[cI] as int;
          assert clauseLength[cI] > 0; }
        countLiterals(cI+1); { countLiterals_monotone(cI+1); }
      }
    }
  }

  lemma clausesNotImpacted_TFArraysSame(
    oldTau : seq<Int32.t>, 
    newTau : seq<Int32.t>, 
    variable : Int32.t, 
    impactedClauses : seq<Int32.t>, 
    impactedClauses' : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validClauses();
    requires validTrueLiteralsCount(oldTau);
    requires validFalseLiteralsCount(oldTau);
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex]);
    requires validVariable(variable);
    requires newTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses);
    requires newTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses');
    requires newTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses');
    requires newTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses);
    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];

    ensures forall clauseIndex : Int32.t :: 0 <= clauseIndex as int < |clauses|
      && clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex]) ==
          countTrueLiterals(newTau, clauses[clauseIndex]);
    ensures forall clauseIndex : Int32.t :: 0 <= clauseIndex as int < |clauses|
      && clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex]) ==
          countFalseLiterals(newTau, clauses[clauseIndex]);
  {
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;

    forall clauseIndex : Int32.t | 0 <= clauseIndex as int < |clauses|
      ensures clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex])
          == countTrueLiterals(newTau, clauses[clauseIndex]);
      ensures clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex])
          == countFalseLiterals(newTau, clauses[clauseIndex]);
    {
      var clause := clauses[clauseIndex];
      var k := |clause|-1;

      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant clauseIndex !in impactedClauses ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 1 <==>
              getLiteralValue(oldTau, clause[j]) == 1);
        invariant clauseIndex !in impactedClauses ==> forall j :: k < j <= |clause| ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);

        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 0 <==>
              getLiteralValue(oldTau, clause[j]) == 0);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j <= |clause| ==>
            countFalseLiterals(oldTau, clause[j..])
              == countFalseLiterals(newTau, clause[j..]);

        decreases k;
      {
        if (clauseIndex !in impactedClauses) {
          assert clause[k] != trueLiteral;
          if (clause[k] == falseLiteral) {
            assert getLiteralValue(newTau, clause[k]) == 0;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 1 <==>
              getLiteralValue(oldTau, clause[k]) == 1;
          }
        } else if (clauseIndex !in impactedClauses') {
          assert clause[k] != falseLiteral;
          if (clause[k] == trueLiteral) {
            assert getLiteralValue(newTau, clause[k]) == 1;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 0 <==>
              getLiteralValue(oldTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }

  lemma setVariable_countTrueLiteralsIncreasesWithOne(
    oldTau : seq<Int32.t>, 
    newTau : seq<Int32.t>, 
    variable : Int32.t, 
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires newTau[variable] == 1 ==> variable+1 in clause;
    requires newTau[variable] == 0 ==> -variable-1 in clause;
    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    requires countTrueLiterals(oldTau, clause) as int < |clause|;

    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) + 1;
  {
    var k := |clause|-1;

    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;

    while (k >= 0 && clause[k] != trueLiteral)
      invariant -1 <= k < |clause|;
      invariant trueLiteral in clause[0..k+1];
      invariant countTrueLiterals(oldTau, clause[k+1..])
        == countTrueLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != falseLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    assert clause[k] == trueLiteral;
    assert countTrueLiterals(oldTau, clause[k..]) + 1
      == countTrueLiterals(newTau, clause[k..]);
    k := k - 1;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant countTrueLiterals(oldTau, clause[k+1..]) + 1
        == countTrueLiterals(newTau, clause[k+1..]);
    {
      if (clause[k] != falseLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma setVariable_countFalseLiteralsIncreasesWithOne(
    oldTau : seq<Int32.t>, 
    newTau : seq<Int32.t>, 
    variable : Int32.t, 
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires newTau[variable] == 1 ==> -variable-1 in clause;
    requires newTau[variable] == 0 ==> variable+1 in clause;
    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    requires countFalseLiterals(oldTau, clause) as int < |clause|;

    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) + 1;
  {
    var k := |clause|-1;

    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;

    assert falseLiteral in clause;
    assert falseLiteral in clause[0..k+1];
    while (k >= 0 && clause[k] != falseLiteral)
      invariant -1 <= k < |clause|;
      invariant falseLiteral in clause[0..k+1];
      invariant countFalseLiterals(oldTau, clause[k+1..]) ==
              countFalseLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != trueLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    assert clause[k] == falseLiteral;
    assert countFalseLiterals(oldTau, clause[k..]) + 1
      == countFalseLiterals(newTau, clause[k..]);
    k := k - 1;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant countFalseLiterals(oldTau, clause[k+1..]) + 1
        == countFalseLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != trueLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma literalTrue_countTrueLiteralsAtLeastOne (
    oldTau : seq<Int32.t>,
    variable : Int32.t,
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires oldTau[variable] == 1 ==> variable+1 in clause;
    requires oldTau[variable] == 0 ==> -variable-1 in clause;

    requires oldTau[variable] in [0, 1];

    ensures 0 < countTrueLiterals(oldTau, clause);
  {
    var literal : Int32.t := variable + 1;
    if (oldTau[variable] == 0) {
      literal := -variable-1;
    }
    var k := |clause| - 1;

    while (k >= 0 && clause[k] != literal)
      invariant -1 <= k < |clause|;
      invariant literal in clause[..k+1];
      invariant countTrueLiterals(oldTau, clause[k+1..]) >= 0;
      decreases k;
    {
      k := k - 1;
    }

    assert clause[k] == literal;
    assert getLiteralValue(oldTau, clause[k]) == 1;
    assert countTrueLiterals(oldTau, clause[k..]) > 0;
    k := k-1;

    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant countTrueLiterals(oldTau, clause[k+1..]) > 0;
      decreases k;
    {
      k := k - 1;
    }
  }

  lemma unsetVariable_countTrueLiteralsDecreasesWithOne(
    oldTau : seq<Int32.t>,
    newTau : seq<Int32.t>,
    variable : Int32.t,
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires oldTau[variable] == 1 ==> variable+1 in clause;
    requires oldTau[variable] == 0 ==> -variable-1 in clause;

    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];

    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;

    ensures countTrueLiterals(newTau, clause) 
      == countTrueLiterals(oldTau, clause) - 1;
  {
    literalTrue_countTrueLiteralsAtLeastOne(oldTau, variable, clause);
    var k := |clause|-1;

    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;

    while (k >= 0 && clause[k] != trueLiteral)
      invariant -1 <= k < |clause|;
      invariant trueLiteral in clause[0..k+1];
      invariant countTrueLiterals(oldTau, clause[k+1..])
              == countTrueLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != falseLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }

      k := k - 1;
    }

    assert clause[k] == trueLiteral;
    assert countTrueLiterals(oldTau, clause[k..]) - 1
      == countTrueLiterals(newTau, clause[k..]);
    k := k - 1;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant countTrueLiterals(oldTau, clause[k+1..])-1
              == countTrueLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != falseLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }

      k := k - 1;
    }
  }

  lemma unsetVariable_countFalseLiteralsDecreasesWithOne(
    oldTau : seq<Int32.t>,
    newTau : seq<Int32.t>,
    variable : Int32.t,
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires oldTau[variable] == 1 ==> -variable-1 in clause;
    requires oldTau[variable] == 0 ==> variable+1 in clause;

    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];

    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;

    ensures countFalseLiterals(newTau, clause)
              == countFalseLiterals(oldTau, clause) - 1;
  {
    var k := |clause|-1;

    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;

    while (k >= 0 && clause[k] != falseLiteral)
      invariant -1 <= k < |clause|;
      invariant falseLiteral in clause[0..k+1];
      invariant countFalseLiterals(oldTau, clause[k+1..]) ==
              countFalseLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != trueLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }

      k := k - 1;
    }

    assert clause[k] == falseLiteral;
    assert countFalseLiterals(oldTau, clause[k..]) - 1
      == countFalseLiterals(newTau, clause[k..]);
    k := k - 1;

    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant countFalseLiterals(oldTau, clause[k+1..])-1 ==
              countFalseLiterals(newTau, clause[k+1..]);
      decreases k;
    {
      if (clause[k] != trueLiteral) {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma undoImpactedClauses_TFSArraysModified(
    oldTau : seq<Int32.t>,
    newTau : seq<Int32.t>,
    variable : Int32.t,
    impactedClauses : seq<Int32.t>,
    impactedClauses' : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validClauses();
    requires validTrueLiteralsCount(oldTau);
    requires validFalseLiteralsCount(oldTau);
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      validClause(clauses[clauseIndex]);
    requires validVariable(variable);
    requires oldTau[variable] == 1 ==>
      validPositiveLiteralToClause(variable, impactedClauses);
    requires oldTau[variable] == 1 ==>
      validNegativeLiteralsToClause(variable, impactedClauses');
    requires oldTau[variable] == 0 ==>
      validPositiveLiteralToClause(variable, impactedClauses');
    requires oldTau[variable] == 0 ==>
      validNegativeLiteralsToClause(variable, impactedClauses);
    requires forall x : Int32.t :: 0 <= x as int < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];

    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      countTrueLiterals(oldTau, clauses[clauseIndex]) ==
        trueLiteralsCount[clauseIndex];

    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      countFalseLiterals(oldTau, clauses[clauseIndex]) ==
        falseLiteralsCount[clauseIndex];

    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;

    ensures forall clauseIndex : Int32.t :: 0 <= clauseIndex as int < |clauses|
      && clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex]) ==
          countTrueLiterals(newTau, clauses[clauseIndex]);

    ensures forall clauseIndex : Int32.t :: 0 <= clauseIndex as int < |clauses|
      && clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex]) ==
          countFalseLiterals(newTau, clauses[clauseIndex]);
  {
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;

    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;

    forall clauseIndex : Int32.t | 0 <= clauseIndex as int < |clauses|
      ensures clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex])
          == countTrueLiterals(newTau, clauses[clauseIndex]);
      ensures clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex])
          == countFalseLiterals(newTau, clauses[clauseIndex]);
    {
      var clause := clauses[clauseIndex];
      var k := |clause|-1;

      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant clauseIndex !in impactedClauses ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 1 <==>
              getLiteralValue(oldTau, clause[j]) == 1);
        invariant clauseIndex !in impactedClauses ==> forall j :: k < j <= |clause| ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);

        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 0 <==>
              getLiteralValue(oldTau, clause[j]) == 0);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j <= |clause| ==>
            countFalseLiterals(oldTau, clause[j..])
              == countFalseLiterals(newTau, clause[j..]);
        decreases k;
      {
        if (clauseIndex !in impactedClauses) {
          assert clause[k] != trueLiteral;
          if (clause[k] == falseLiteral) {
            assert getLiteralValue(oldTau, clause[k]) == 0;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 1 <==>
              getLiteralValue(newTau, clause[k]) == 1;
          }
        } else if (clauseIndex !in impactedClauses') {
          assert clause[k] != falseLiteral;
          if (clause[k] == trueLiteral) {
            assert getLiteralValue(oldTau, clause[k]) == 1;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 0 <==>
              getLiteralValue(newTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }

  lemma notDone_literalsToSet(i : Int32.t)
    requires valid();
    requires 0 <= i as int < |clauses|;
    requires falseLiteralsCount[i] as int < |clauses[i]|;
    requires trueLiteralsCount[i] == 0;
    requires validClause(clauses[i]);
    requires forall literal :: literal in clauses[i] ==> validLiteral(literal);

    ensures exists literal :: literal in clauses[i]
                        && truthAssignment[getVariableFromLiteral(literal)] == -1;
  {
    assert forall literal :: validLiteral(literal) ==>
      -1 <= getLiteralValue(truthAssignment[..], literal) <= 1;

    var clause := clauses[i];

    countTrueLiterals0_noLiteralsTrue(truthAssignment[..], clause);

    if forall literal :: literal in clause ==> getLiteralValue(truthAssignment[..], literal) == 0 {
      var k := |clause|-1;

      while (k > 0)
        invariant 0 <= k < |clause| == |clauses[i]|;
        invariant countFalseLiterals(truthAssignment[..], clause[k..]) as int == (|clause| - k);
        decreases k;
      {
        assert getLiteralValue(truthAssignment[..], clause[k]) == 0;
        k := k - 1;
      }

      assert countFalseLiterals(truthAssignment[..], clause) as int == |clauses[i]|;
      assert false;
    }
  }

  lemma setVariable_unsetVariablesDecreasesWithOne(
    oldTau : seq<Int32.t>,
    newTau : seq<Int32.t>,
    variable : Int32.t
  )
    requires validVariablesCount();
    requires validVariable(variable);
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires |oldTau| == |newTau|;

    requires forall i : Int32.t :: 0 <= i as int < |oldTau| && i != variable ==>
                oldTau[i] == newTau[i];

    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    requires countUnsetVariables(newTau) as int < |newTau|;

    ensures countUnsetVariables(newTau) + 1 == countUnsetVariables(oldTau);
  {
    var k := |newTau|-1;

    while (k > 0)
      invariant 0 <= k < |newTau|;
      invariant variable as int < k < |newTau| ==> 
        countUnsetVariables(newTau[k..]) == countUnsetVariables(oldTau[k..]);
      invariant 0 <= k <= variable as int ==>
        countUnsetVariables(newTau[k..])+1 == countUnsetVariables(oldTau[k..]);
    {
      k := k - 1;
    }
  }

  predicate isVariableSet(truthAssignment : seq<Int32.t>, variable : Int32.t)
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validVariable(variable);
  {
    truthAssignment[variable] != -1
  }

  predicate isSatisfied(truthAssignment: seq<Int32.t>)
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
      forall cI : Int32.t :: 0 <= cI as int < |clauses| ==>
        isClauseSatisfied(truthAssignment, cI)
  }

  predicate isExtendingTau(tau : seq<Int32.t>, tau' : seq<Int32.t>)
    reads `variablesCount;
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validValuesTruthAssignment(tau');
  {
    forall i :: 0 <= i < |tau| && tau[i] != -1 ==>
            tau[i] == tau'[i]
  }

  predicate isTauComplete(tau : seq<Int32.t>)
    reads `variablesCount;
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
  {
    forall i :: 0 <= i < |tau| ==> tau[i] != -1
  }

  function getExtendedCompleteTau(tau : seq<Int32.t>) : seq<Int32.t>
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires isSatisfiableExtend(tau);

    ensures (
      var tau' := getExtendedCompleteTau(tau);

      validValuesTruthAssignment(tau')
        && isTauComplete(tau')
        && isExtendingTau(tau, tau')
        && isSatisfied(tau')
    );
  {
    var tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau')
        && isExtendingTau(tau, tau')
        && isSatisfied(tau');

    tau'
  }

  predicate isSatisfiableExtend(tau : seq<Int32.t>)
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
  {
    exists tau' :: validValuesTruthAssignment(tau')
                && isTauComplete(tau')
                && isExtendingTau(tau, tau')
                && isSatisfied(tau')
  }

  predicate isSatisfiableTruthAssignment(tau : seq<Int32.t>, tau':seq<Int32.t>)
    reads `variablesCount, `clauses, `clausesCount,
          `clauseLength, clauseLength;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
  {
    validValuesTruthAssignment(tau')
                && isExtendingTau(tau, tau')
                && isSatisfied(tau')
  }


  function method isUnitClause(index : Int32.t) : bool
    reads this, traceVariable, traceValue, traceDLStart, 
          traceDLEnd, truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength;
    
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires validTruthAssignment();
    requires validClauses();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);

    requires 0 <= index < clausesCount;
  {
    trueLiteralsCount[index] == 0 &&
    clauseLength[index] - falseLiteralsCount[index] == 1
  }

  function method isEmptyClause(index : Int32.t) : bool
    reads this, traceVariable, traceValue, traceDLStart, 
          traceDLEnd, truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength;
    
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires validTruthAssignment();
    requires validClauses();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);

    requires 0 <= index < clausesCount;
  {
    clauseLength[index] == falseLiteralsCount[index]
  }

}


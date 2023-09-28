include "formula.dfy"
include "../int32.dfy"

datatype SAT_UNSAT = SAT(tau:seq<Int32.t>) | UNSAT

class SATSolver {
  var formula : Formula;

  constructor(f' : Formula)
    requires f'.valid();
    ensures formula == f';
    ensures formula.valid();
  {
    formula := f';
  }

  method step(literal : Int32.t, value : bool) returns (result : SAT_UNSAT)
    requires formula.valid();
    requires formula.decisionLevel < formula.variablesCount - 1; // not full
    requires formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];
    requires !formula.hasEmptyClause();
    requires !formula.isEmpty();
    requires formula.validLiteral(literal);
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1;

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
            formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
            formula`assignmentsTrace, formula.trueLiteralsCount,
            formula.falseLiteralsCount;

    ensures formula.valid();
    ensures !formula.hasEmptyClause();
    ensures old(formula.decisionLevel) == formula.decisionLevel;
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace;
    ensures forall i :: 0 <= i <= formula.decisionLevel ==>
      old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i);
    ensures formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];
    ensures !formula.isEmpty();

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> (
      var (variable, val) := formula.convertLVtoVI(literal, value);
      formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val]));
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)

    ensures result.UNSAT? ==> (
      var (variable, val) := formula.convertLVtoVI(literal, value);
      !formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val]));

    ensures formula.countUnsetVariables(formula.truthAssignment[..]) ==
      formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 0;
  {
    formula.increaseDecisionLevel();
    formula.setLiteral(literal, value);
    result := solve();
    formula.revertLastDecisionLevel();

    if (formula.truthAssignment[..] != old(formula.truthAssignment[..])) {
      ghost var i : Int32.t :| 0 <= i as int < formula.truthAssignment.Length &&
              formula.truthAssignment[i] != old(formula.truthAssignment[i]);

      ghost var y : (Int32.t, bool) := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
      assert false;
    }

    return result;
  }

  method solve() returns (result : SAT_UNSAT)
    requires formula.valid();
    requires formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
             formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
             formula`assignmentsTrace, formula.trueLiteralsCount,
             formula.falseLiteralsCount;

    ensures formula.valid();
    ensures old(formula.decisionLevel) == formula.decisionLevel;
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace;
    ensures forall i :: 0 <= i <= formula.decisionLevel ==>
      old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i);
    ensures formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) ==
      formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 1;
  {
    var hasEmptyClause : bool := formula.getHasEmptyClause();
    if (hasEmptyClause) {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }

    var isEmpty : bool := formula.getIsEmpty();
    if (isEmpty) {
      formula.isEmpty_sastisfied();
      // assert formula.isSatisfiableExtend(formula.truthAssignment[..]);
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }

    var literal := formula.chooseLiteral();

    formula.notEmptyNoEmptyClauses_traceNotFull();
    result := step(literal, true);

    if (result.SAT?) {
      return result;
    }

    result := step(literal, false);

    if (result.UNSAT?) {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(
        formula.truthAssignment[..],
        variable
      );
    }

    return result;
  }

  /** in a way it is weird that solve does not know in any way about the
  level0unitPropagation. **/
  method start() returns (result : SAT_UNSAT) // tau may be arbitrary truth assignment
    requires formula.valid();
    requires formula.decisionLevel == -1;

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
            formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
            formula`assignmentsTrace, formula.trueLiteralsCount,
            formula.falseLiteralsCount;

    ensures formula.valid();
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
    // this is the added postcondition
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
  {
    formula.level0UnitPropagation();
    result := solve();
  }
  

  method start_counterexample_new() returns (result : SAT_UNSAT) // tau may be arbitrary truth assignment
    // specification of input
    requires formula.variablesCount == 2
    requires formula.clauses == [[1]]
    requires formula.decisionLevel == -1
    requires formula.valid()
    // export output
    ensures result == SAT([-1,-1])
    // preconditions
    ensures old(formula.valid())
    ensures old(formula.decisionLevel) == -1
    // modifies
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
            formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
            formula`assignmentsTrace, formula.trueLiteralsCount,
            formula.falseLiteralsCount;
    // postconditions
    ensures formula.valid();
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
  {
    result := SAT([-1,-1]);
    assert formula.validValuesTruthAssignment([1,1]);
    assert formula.isTauComplete([1,1]);
    assert formula.isExtendingTau([-1,-1], [1,1]);
    assert formula.getLiteralValue([1,1], 1) == 1;
    assert 1 in formula.clauses[0];

    assert formula.isSatisfied([1,1]);

    assert formula.validVariablesCount();
    assert formula.validClauses();
    assert formula.validValuesTruthAssignment(formula.truthAssignment[..]);
  }

  lemma start_counterexample_non_executable_style(f:Formula, f':Formula, result:SAT_UNSAT)
    // specification of input
    requires f.variablesCount == 2
    requires f.clauses == [[1]]
    requires f.clausesCount == 1
    requires f.clauseLength.Length == 1
    requires f.clauseLength[0] == 1
    requires f.truthAssignment.Length == 2
    requires f.truthAssignment[0] == -1
    requires f.truthAssignment[1] == -1
    requires f.trueLiteralsCount.Length == 1
    requires f.trueLiteralsCount[0] == 0
    requires f.falseLiteralsCount.Length == 1
    requires f.falseLiteralsCount[0] == 0
    requires f.positiveLiteralsToClauses.Length == 2
    requires f.negativeLiteralsToClauses.Length == 2
    requires f.positiveLiteralsToClauses[0] == [0]
    requires f.positiveLiteralsToClauses[1] == []
    requires f.negativeLiteralsToClauses[0] == []
    requires f.negativeLiteralsToClauses[1] == []
    requires f.decisionLevel == -1
    requires f.traceVariable.Length == 2
    requires f.traceVariable[0] == f.traceVariable[1] == 0
    requires f.traceValue.Length == 2
    requires f.traceValue[0] == f.traceValue[1] == false
    requires f.traceDLStart.Length == 2
    requires f.traceDLStart[0] == f.traceDLStart[1] == 0
    requires f.traceDLEnd.Length == 2
    requires f.traceDLEnd[0] == f.traceDLEnd[1] == 0
    requires f.assignmentsTrace == {}
    // specification of new f'
    requires f'.variablesCount == 2
    requires f'.clauses == [[1]]
    requires f'.clausesCount == 1
    requires f'.clauseLength.Length == 1
    requires f'.clauseLength[0] == 1
    requires f'.truthAssignment.Length == 2
    requires f'.truthAssignment[0] == -1
    requires f'.truthAssignment[1] == -1
    requires f'.trueLiteralsCount.Length == 1
    requires f'.trueLiteralsCount[0] == 0
    requires f'.falseLiteralsCount.Length == 1
    requires f'.falseLiteralsCount[0] == 0
    requires f'.positiveLiteralsToClauses.Length == 2
    requires f'.negativeLiteralsToClauses.Length == 2
    requires f'.positiveLiteralsToClauses[0] == [0]
    requires f'.positiveLiteralsToClauses[1] == []
    requires f'.negativeLiteralsToClauses[0] == []
    requires f'.negativeLiteralsToClauses[1] == []
    requires f'.decisionLevel == -1
    requires f'.traceVariable.Length == 2
    requires f'.traceVariable[0] == f'.traceVariable[1] == 0
    requires f'.traceValue.Length == 2
    requires f'.traceValue[0] == f'.traceValue[1] == false
    requires f'.traceDLStart.Length == 2
    requires f'.traceDLStart[0] == f'.traceDLStart[1] == 0
    requires f'.traceDLEnd.Length == 2
    requires f'.traceDLEnd[0] == f.traceDLEnd[1] == 0
    requires f'.assignmentsTrace == {}
    // references for f
    requires (f.truthAssignment != f.trueLiteralsCount) &&
    (f.truthAssignment != f.falseLiteralsCount) &&
    (f.truthAssignment != f.clauseLength) &&
    (f.truthAssignment != f.traceVariable) &&
    (f.truthAssignment != f.traceDLStart) &&
    (f.truthAssignment != f.traceDLEnd) &&
    (f.trueLiteralsCount != f.falseLiteralsCount) &&
    (f.trueLiteralsCount != f.clauseLength) &&
    (f.trueLiteralsCount != f.traceVariable) &&
    (f.trueLiteralsCount != f.traceDLStart) &&
    (f.trueLiteralsCount != f.traceDLEnd) &&
    (f.falseLiteralsCount != f.clauseLength) &&
    (f.falseLiteralsCount != f.traceVariable) &&
    (f.falseLiteralsCount != f.traceDLStart) &&
    (f.falseLiteralsCount != f.traceDLEnd) &&
    (f.clauseLength != f.traceVariable) &&
    (f.clauseLength != f.traceDLStart) &&
    (f.clauseLength != f.traceDLEnd) &&
    (f.positiveLiteralsToClauses != f.negativeLiteralsToClauses) &&
    (f.traceVariable != f.traceDLStart) &&
    (f.traceVariable != f.traceDLEnd) &&
    (f.traceDLStart != f.traceDLEnd)
    // references for f'
    requires (f.truthAssignment != f'.trueLiteralsCount) &&
    (f'.truthAssignment != f'.falseLiteralsCount) &&
    (f'.truthAssignment != f'.clauseLength) &&
    (f'.truthAssignment != f'.traceVariable) &&
    (f'.truthAssignment != f'.traceDLStart) &&
    (f'.truthAssignment != f'.traceDLEnd) &&
    (f'.trueLiteralsCount != f'.falseLiteralsCount) &&
    (f'.trueLiteralsCount != f'.clauseLength) &&
    (f'.trueLiteralsCount != f'.traceVariable) &&
    (f'.trueLiteralsCount != f'.traceDLStart) &&
    (f'.trueLiteralsCount != f'.traceDLEnd) &&
    (f'.falseLiteralsCount != f'.clauseLength) &&
    (f'.falseLiteralsCount != f'.traceVariable) &&
    (f'.falseLiteralsCount != f'.traceDLStart) &&
    (f'.falseLiteralsCount != f'.traceDLEnd) &&
    (f'.clauseLength != f'.traceVariable) &&
    (f'.clauseLength != f'.traceDLStart) &&
    (f'.clauseLength != f'.traceDLEnd) &&
    (f'.positiveLiteralsToClauses != f'.negativeLiteralsToClauses) &&
    (f'.traceVariable != f'.traceDLStart) &&
    (f'.traceVariable != f'.traceDLEnd) &&
    (f'.traceDLStart != f'.traceDLEnd)
    // reference between f and f'
    requires f.truthAssignment == f'.truthAssignment
    requires f.traceVariable == f'.traceVariable
    requires f.traceValue == f'.traceValue
    requires f.traceDLStart == f'.traceDLStart
    requires f.traceDLEnd == f'.traceDLEnd
    requires f.trueLiteralsCount == f'.trueLiteralsCount
    requires f.falseLiteralsCount == f'.falseLiteralsCount
    // specification of output
    requires result.SAT?
    requires result.tau == [-1,-1]
    // preconditions
    ensures f.valid();
    ensures f.decisionLevel == -1;
    // modifies
    ensures f'.variablesCount == f.variablesCount
    ensures f'.clauses == f.clauses
    ensures f'.clausesCount == f.clausesCount
    ensures f'.clauseLength.Length == f.clauseLength.Length
    ensures forall i | 0 <= i < f.clauseLength.Length :: f.clauseLength[i] == f'.clauseLength[i]
    ensures f'.positiveLiteralsToClauses.Length == f.positiveLiteralsToClauses.Length
    ensures f'.negativeLiteralsToClauses.Length == f.negativeLiteralsToClauses.Length
    ensures f.truthAssignment == f'.truthAssignment
    ensures f.traceVariable == f'.traceVariable
    ensures f.traceValue == f'.traceValue
    ensures f.traceDLStart == f'.traceDLStart
    ensures f.traceDLEnd == f'.traceDLEnd
    ensures f.trueLiteralsCount == f'.trueLiteralsCount
    ensures f.falseLiteralsCount == f'.falseLiteralsCount
    // postconditions
    ensures f'.valid()
    ensures result.SAT? ==> f'.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> f'.isSatisfiableExtend(f.truthAssignment[..]);
    ensures result.UNSAT? ==>
      !f'.isSatisfiableExtend(f.truthAssignment[..])
    {
        // f
        assert f.validValuesTruthAssignment([1,1]);
        assert f.isTauComplete([1,1]);
        assert f.isExtendingTau([-1,-1], [1,1]);
        assert f.getLiteralValue([1,1], 1) == 1;
        assert 1 in f.clauses[0];

        assert f.isSatisfied([1,1]);

        assert f.validVariablesCount();
        assert f.validClauses();
        assert f.validValuesTruthAssignment(f.truthAssignment[..]);

        // f'
        assert f'.validValuesTruthAssignment([1,1]);
        assert f'.isTauComplete([1,1]);
        assert f'.isExtendingTau([-1,-1], [1,1]);
        assert f'.getLiteralValue([1,1], 1) == 1;
        assert 1 in f.clauses[0];

        assert f'.isSatisfied([1,1]);

        assert f'.validVariablesCount();
        assert f'.validClauses();
        assert f'.validValuesTruthAssignment(f.truthAssignment[..]);
    }

  method start_precondition_test()
    // specification of input
    requires formula.variablesCount == 2
    requires formula.clauses == [[1]]
    requires formula.clausesCount == 1
    requires formula.clauseLength.Length == 1
    requires formula.clauseLength[0] == 1
    requires formula.truthAssignment.Length == 2
    requires formula.truthAssignment[0] == -1
    requires formula.truthAssignment[1] == -1
    requires formula.trueLiteralsCount.Length == 1
    requires formula.trueLiteralsCount[0] == 0
    requires formula.falseLiteralsCount.Length == 1
    requires formula.falseLiteralsCount[0] == 0
    requires formula.positiveLiteralsToClauses.Length == 2
    requires formula.negativeLiteralsToClauses.Length == 2
    requires formula.positiveLiteralsToClauses[0] == [0]
    requires formula.positiveLiteralsToClauses[1] == []
    requires formula.negativeLiteralsToClauses[0] == []
    requires formula.negativeLiteralsToClauses[1] == []
    requires formula.decisionLevel == -1
    requires formula.traceVariable.Length == 2
    requires formula.traceVariable[0] == formula.traceVariable[1] == 0
    requires formula.traceValue.Length == 2
    requires formula.traceValue[0] == formula.traceValue[1] == false
    requires formula.traceDLStart.Length == 2
    requires formula.traceDLStart[0] == formula.traceDLStart[1] == 0
    requires formula.traceDLEnd.Length == 2
    requires formula.traceDLEnd[0] == formula.traceDLEnd[1] == 0
    requires formula.assignmentsTrace == {}
    // references
    requires (formula.truthAssignment != formula.trueLiteralsCount) &&
    (formula.truthAssignment != formula.falseLiteralsCount) &&
    (formula.truthAssignment != formula.clauseLength) &&
    (formula.truthAssignment != formula.traceVariable) &&
    (formula.truthAssignment != formula.traceDLStart) &&
    (formula.truthAssignment != formula.traceDLEnd) &&
    (formula.trueLiteralsCount != formula.falseLiteralsCount) &&
    (formula.trueLiteralsCount != formula.clauseLength) &&
    (formula.trueLiteralsCount != formula.traceVariable) &&
    (formula.trueLiteralsCount != formula.traceDLStart) &&
    (formula.trueLiteralsCount != formula.traceDLEnd) &&
    (formula.falseLiteralsCount != formula.clauseLength) &&
    (formula.falseLiteralsCount != formula.traceVariable) &&
    (formula.falseLiteralsCount != formula.traceDLStart) &&
    (formula.falseLiteralsCount != formula.traceDLEnd) &&
    (formula.clauseLength != formula.traceVariable) &&
    (formula.clauseLength != formula.traceDLStart) &&
    (formula.clauseLength != formula.traceDLEnd) &&
    (formula.positiveLiteralsToClauses != formula.negativeLiteralsToClauses) &&
    (formula.traceVariable != formula.traceDLStart) &&
    (formula.traceVariable != formula.traceDLEnd) &&
    (formula.traceDLStart != formula.traceDLEnd)
    ensures old(formula.valid())
    ensures old(formula.decisionLevel) == -1
  {}


  method start_counterexample() returns (result : SAT_UNSAT) // tau may be arbitrary truth assignment
 // original specification
    requires formula.valid();
    requires formula.decisionLevel == -1;
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
              formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
              formula`assignmentsTrace, formula.trueLiteralsCount,
              formula.falseLiteralsCount;
      ensures formula.valid();
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
    // counterexample specific - a wrong behavior
    ensures result.SAT? ==> result.tau[0] == -1
  {
  // original start() implementation:
    formula.level0UnitPropagation();
    result := solve();
  // added at the end of original start() implementation:
    if result.SAT? {
      result := SAT(seq(formula.variablesCount, _ => -1));
    } 
  }
}

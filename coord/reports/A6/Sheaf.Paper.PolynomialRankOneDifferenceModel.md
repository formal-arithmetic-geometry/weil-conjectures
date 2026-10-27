## What changed

Extracted the nine existing data declarations, from Variables through PresentationAssertion,
verbatim into Sheaf.Paper.PolynomialRankOneDifferenceModelData. Their original names,
signatures, definition bodies, structure fields and visibility are preserved. The original
item publicly reexports that module. The extraction avoids import cycles for two independent
subtasks: finite polynomial algebra, and its internal scalar-extended presentation.

The original theorem polynomial_rank_one_difference_model is proved by constructing one
PolynomialSystem over E₀ and applying the generic presentation statement to that same
system over E₀ and Ω. The scalar towers are inferred canonically; continuity is proved by
continuous_algebraMap for the identity and continuous_subtype_val for E₀ into Ω.
No target statement changes and no unproved theorem is used to define an object.

The lower presentation statement explicitly requires the scalar tower and continuity of
the coefficient map. Those are necessary to compare the Q_ell translation coordinates
with the scalar-extended representation, and both are satisfied in the original theorem.
The finite-system existence statement is independent of an algebraic closure: it only
needs a finite normed extension of Q_ell. The two new statements have full natural-language
proofs and matching DAG nodes. The original node now records the actual combining proof.

Read the current blueprint direct-image proof paragraph (3), the original nine-step node,
its proof dependencies and their Lean signatures. Library and Mathlib searches found Taylor
maps and bounded-polynomial modules but no complete construction or presentation matching
these interfaces. The unit route is retained; no statement or proof step of the unit is
bypassed. Checked the empty-residual k=0, empty-spectator m=0, constant-stage n=0 and empty
test-space cases in the split statements and their proof descriptions.

Remote lcompile.py --all typechecked all four modules. A profiling check of the data
module after removing unused imports finished in 9.9 seconds, with 1.59 seconds of
elaboration and no slow declaration. Development profiler settings are removed.

Change record: coord/changes/A6-polynomial-rank-one-data.md. No other existing Lean module
is changed. Direct-importer search and tools/downstream.py found no current Lean importer;
the unfinished DAG parents still need this theorem, which remains in place.

## Proved and sorry left

Closed the original hole in
Profinite.CondensedAction.PolynomialRankOne.polynomial_rank_one_difference_model
(node lem-sfb-polynomial-rank-one-difference-model). Its complete combining proof typechecks.

Two holes added, each the entire proof of a named public theorem in its own module:

- Profinite.CondensedAction.PolynomialRankOne.exists_polynomial_system
  (lem-sfb-polynomial-rank-one-system-existence): original proof steps 1--5.
- Profinite.CondensedAction.PolynomialRankOne.presentation_assertion
  (lem-sfb-polynomial-rank-one-presentation): original proof steps 6--9, for an already given
  system and a single arbitrary compatible continuous coefficient extension.

This is a decomposition, not an axiom-free proof of the original result. Original item:
1 of 1 local holes closed; 2 split off; 0 local holes left. Whole delivery: 2 holes.
The data module contains no sorry, and no definition contains a postponed proof or witness.

## No longer needed

Removed the unused private imports Mathlib.Data.Nat.Choose.Sum and
Mathlib.Topology.Algebra.Module.FiniteDimension from the data-only extraction. Their
mathematical results remain dependencies of the finite-system construction split.
The main module only needs its public data reexport and the two private split imports.
The original proof dependencies remain below the appropriate split nodes; none is claimed
unnecessary. No existing DAG node or Lean module is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The listed proof dependencies provide general polynomial algebra, continuity, condensation
and colimit facts. None states the combined finite-system construction or the normalized
presentation with all the specified section equations. The two split statements isolate
exactly those substantial glue arguments rather than assuming an existing declaration
already states them. They are distinct parts of the original nine-step plan.

The original data lived in the theorem module, so new statements using them could not be
imported there. Their unchanged extraction resolves that dependency cycle. The original
module-level import of PolynomialTranslationAcyclic still supplies its Model definition;
no downstream acyclicity theorem is used as a proof ingredient. The existing source note
that an exact external all-continuous noncomplete reference is WANTED remains applicable;
these proofs in words are explicitly the original agent-formulated expansion.

## New nodes

- def-sfb-polynomial-rank-one-model-data records the unchanged Variables, Indices, Residual,
  coordinates, translate, PolynomialSystem, tensorPolynomial, polynomialSection and
  PresentationAssertion definitions in their extracted module. It has no theorem hole.
- lem-sfb-polynomial-rank-one-system-existence isolates finite stages, bases, translations,
  continuity, nilpotence and the finite Taylor identity, with no internal colimit assertion.
- lem-sfb-polynomial-rank-one-presentation assumes a given PolynomialSystem and constructs
  its internal presentation over one compatible continuous coefficient field. It does not
  construct a system. Its proof describes finite coproducts, normalized colimits and the
  three operators, using only the categorical part of action-colimit creation.

All new nodes retain the chapter and unit of the item. Search logs record LeanSearch,
LeanFinder, Loogle and grep queries actually run. The change record is
coord/changes/A6-polynomial-rank-one-data.md.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

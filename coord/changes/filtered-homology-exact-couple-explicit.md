# CategoryTheory.filteredHomologyExactCouple and CategoryTheory.filteredHomologyEIso

## Reason

Replace the two postponed data constructions by the exact explicit construction
specified by node `def-sp-filtered-homology-exact-couple`. No signature, hypothesis,
universe, visibility, or underlying mathematical definition changes. The record is
required because filling a data-valued definition changes its visible body.

## Old

```lean
noncomputable abbrev filteredHomologyExactCouple {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) : BigradedExactCouple C 0 := by
  sorry

/-- The reindexed initial E term is graded-piece homology.
Source: Stacks Project, Tag 012K.
(blueprint: def-sp-filtered-homology-exact-couple). -/
noncomputable def filteredHomologyEIso {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    ((filteredHomologyExactCouple K F).pageCouple 0).E (2 * p + q) (-p) ≅
      (F.gradedPiece p).homology (p + q) := by
  sorry
```

## New

```lean
noncomputable abbrev filteredHomologyExactCouple {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) : BigradedExactCouple C 0 := by
  let h := filteredHomologyCouple_exact C K F
  exact
    { D := filteredHomologyD K F
      E := filteredHomologyE K F
      alpha := filteredHomologyAlpha K F
      f := filteredHomologyF K F
      g := filteredHomologyG K F
      alpha_f_zero := h.1
      f_g_zero := h.2.1
      g_alpha_zero := h.2.2.1
      exact_alpha := h.the project server
      exact_f := h.the project server.1
      exact_g := h.the project server.2 }

/-- The reindexed initial E term is graded-piece homology.
Source: Stacks Project, Tag 012K.
(blueprint: def-sp-filtered-homology-exact-couple). -/
noncomputable def filteredHomologyEIso {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    ((filteredHomologyExactCouple K F).pageCouple 0).E (2 * p + q) (-p) ≅
      (F.gradedPiece p).homology (p + q) := eqToIso (by
  change (F.gradedPiece (-(-p))).homology (2 * p + q + -p) =
    (F.gradedPiece p).homology (p + q)
  exact congrArg₂ (fun a n ↦ (F.gradedPiece a).homology n) (by omega) (by omega))
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.FilteredHomologyExactCouple
--uses filteredHomologyExactCouple` was read, together with a textual search for
both declaration names. Every existing consumer receives exactly the explicit data
and index equality isomorphism the node specifies. No consumer signature changes
and no consumer is adapted. All five direct consumers listed below compiled
unchanged in a scratch sandbox against the completed definitions. The forward
representative and differential modules emit private-module linter warnings;
the other three compile cleanly. The two definitions are not in the signatures of the
five targets in `Challenge.lean`; the meaning of those targets is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages | F7 | Same type; explicit couple and initial-page isomorphism. |
| Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives | unclaimed in shared snapshot | Same type; terms and maps reduce to explicit homology data. |
| Sheaf.CategoryTheory.FilteredHomologyTowerQuotients | M6 | Same type; explicit initial terms and index transport. |
| Sheaf.CategoryTheory.FilteredHomologyTowerDifferential | unclaimed in shared snapshot | Same type; explicit graded-projection map. |
| Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure | unclaimed in shared snapshot | Import retained; no statement change. |

## Status

landed 20261018T062753-L-650150 2026-10-18 (merge of deliver/F8/Sheaf.CategoryTheory.FilteredHomologyExactCouple)

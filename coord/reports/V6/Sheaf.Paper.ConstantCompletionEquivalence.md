## What changed

Repair of the returned delivery at `287119c8c16` (reviewer C-28711):
retained the reviewed proofs and elaboration repairs, checked them against the
current shared source, and compiled the complete module again on the project
server on 2026-10-21 (26.0 seconds, exit code 0, no warnings). The delivery tool
rebuilds this packet on the freshly fetched `sheaf-dag` before preflight and push.
The unrelated missing `SmoothSourceConstructibleLocalAcyclicity` source remains
preserved in quarantine; this packet neither withdraws nor alters it.

In `Sheaf.Paper.ConstantCompletionEquivalence`, filled four existing theorem proofs:
constructed insertion by forgetting the proved scalar-extension unit to underlying sheaves;
assembled the reduction unit from sectionwise module adjunction units followed by
sheafification and the stated transition formula; proved pullback additivity through the underlying-sheaf isomorphism; and
transported the recorded homotopy-level derived pullback to the complex-level Kan
universal property. Two private, proved categorical helpers perform this transport. A third private lemma
constructs the normalized scalar-extension unit and proves its section formula. A further
private lemma proves the ordinary complex-limit unit for abstract tower functors;
`ordinaryUnit_existsUnique` specializes it with its original statement unchanged.

The existing `Sheaf.Paper.RingedTopoiDerivedPullback` import supplies derived pullback.
The scalar unit uses Mathlib's sectionwise unit and module sheafification.
Reproved the existing `change_laws` and `change_additive` directly from sectionwise
scalar extension and sheafification, using the proof-only import
`Mathlib.CategoryTheory.Adjunction.Additive`. This avoids recovering elementary
functor laws from the derived change-of-rings construction.

Reexpressed `reductionTowerComparisonComplex` using the canonical complex-composition
isomorphisms, to prevent repeated unfolding during kernel checking. The maps are the
same termwise maps; no mathematical hypothesis or conclusion changes. The sole user
is the existing comparison formula in this module. See
`coord/changes/V6-constant-completion-complex-comparison.md`.
Also optimized the existing `limitRestriction_existsUnique` proof by constructing its
complex comparison generically and proving its coordinate formula before specialization.
Its statement is unchanged; the isolated proof takes 0.15 seconds of kernel checking.
The existing `ordinaryLimit` now specializes the abstract `complexLimitFunctor`,
supplying its canonical additive proof. This shares the functor name with the abstract
unit theorem. A Lean `rfl` check proved equality with the original functor in 8.5 seconds;
see `coord/changes/V6-constant-completion-limit-instance.md`.
The later proofs temporarily use Mathlib's generic composite-functor additivity and
zero-map preservation instances. The three existing specialized instance attributes
are restored at the module's end, preserving the exported instance setup.
Updated the main node's proof and dependencies to record these constructions.
The complete module compiled without warnings in 39.3 seconds. The full source with
the delivery axiom audit also compiled in 41.1 seconds, reporting precisely the twenty
remaining holes and no unexpected axioms. A separate Lean check
verified that the repaired comparison's degree maps are exactly the original strict
tower comparison maps. Another conversion check verified that the new generic
`DerivedTowerComparisonFormula` unfolds to the original representative-computation
equation; the latter check compiled in 11.9 seconds. This predicate is a genuine formula,
with no new assumption or proof hole, attached to the existing node. See the separate
`coord/changes/V6-constant-completion-derived-formula.md` change record.
Likewise, the existing derived scalar-comparison and finite-pullback equations now use
`DerivedPullComparisonFormula` and `FinitePullComparisonFormula`. A Lean check applied
the old theorems directly to both complete new theorem types in 9.4 seconds, with no
rewriting. Their witness getters keep their exact signatures and bodies. See
`coord/changes/V6-constant-completion-pull-formulas.md`.

## Proved and sorry left

Closed 4 of the original 24 holes, with no new holes and no split-off statements:

- `CategoryTheory.ConstantCompletion.reductionUnit_existsUnique`.
- `CategoryTheory.ConstantCompletion.insertion_existsUnique`.
- `CategoryTheory.ConstantCompletion.pull_additive`.
- `CategoryTheory.ConstantCompletion.derivedPull_exists`.

The remaining 20 holes are unchanged. Each belongs to
`lem-weil-pbc-constant-completion-equivalence`, with its existing source and proof
in words in the declaration's docstring:

- `CategoryTheory.ConstantCompletion.flat_and_quotients`.
- `CategoryTheory.ConstantCompletion.equivalence`.
- `CategoryTheory.ConstantCompletion.finiteComparison_existsUnique`.
- `CategoryTheory.ConstantCompletion.finiteDerivedComparison`.
- `CategoryTheory.ConstantCompletion.reductionStep_existsUnique`.
- `CategoryTheory.ConstantCompletion.quotientPresentation_exists`.
- `CategoryTheory.ConstantCompletion.koszul_quotient_reflector`.
- `CategoryTheory.ConstantCompletion.completion_restriction`.
- `CategoryTheory.ConstantCompletion.reductionTowerComparison_existsUnique`.
- `CategoryTheory.ConstantCompletion.derivedReductionTowerComparison`.
- `CategoryTheory.ConstantCompletion.derivedLimitRestriction`.
- `CategoryTheory.ConstantCompletion.inverseImageData_exists`.
- `CategoryTheory.ConstantCompletion.ordinaryPullComparison_existsUnique`.
- `CategoryTheory.ConstantCompletion.derivedPullComparison_existsUnique`.
- `CategoryTheory.ConstantCompletion.ordinaryFinitePull_existsUnique`.
- `CategoryTheory.ConstantCompletion.finitePull_existsUnique`.
- `CategoryTheory.ConstantCompletion.completedFinitePull_existsUnique`.
- `CategoryTheory.ConstantCompletion.pullbackTowerComparison_existsUnique`.
- `CategoryTheory.ConstantCompletion.pullback_composition`.
- `CategoryTheory.ConstantCompletion.pullback_identity`.

The reduction-unit proof uses the existing named `reductionStep_existsUnique` theorem;
its remaining hole is included above. This delivery does not claim the whole module
is sorry-free.

## No longer needed

Removed direct proof imports unused by the proofs actually written here:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`.
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `WeilConjectures.RingTheory.LimitFlatModules`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.RingTheory.NoetherianKoszulAugmentationProZero`.
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

These are import removals, not module withdrawals. The cochain model still uses the
independent-coefficient change-of-rings module transitively. Dependencies for the twenty
remaining holes stay in the DAG and their unit route; no node or module is withdrawn.
No new module is introduced and no adopted source declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The existing complex comparison relied on conversion between a complex of a composite
functor and the corresponding composite of complex functors. Profiling found about
14 seconds of kernel checking in the derived-tower comparison statement alone.
Explicit canonical composition isomorphisms give the same comparison with matching
source and target expressions. Recording its computation square as a generic predicate
also avoids repeating the concrete conversions in the theorem statement. This is an elaboration repair, not a mathematical
statement dispute. The change record lists the sole declaration consumer.

The same conversion issue affected selection of the derived scalar and finite-pullback
comparisons. Their equations are now checked with abstract ordinary functors, retaining
the original normalized computations definitionally. The elementary scalar-extension construction is checked before specializing to the
strict reduction tower.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

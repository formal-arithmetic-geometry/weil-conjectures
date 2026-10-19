## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible` with its existing signature unchanged. All helper theorems are private and proved. The only public import remains `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward`.

The proof explicitly normalizes finite coefficient fields by their algebraic-closure embeddings, transports their condensed rings by continuous ring equivalences, compares finite constant models with stratified local finite presentations (using the existing integral comparison for integral coefficients), and identifies the two ordinary localizing hulls with the same coproduct indexing universe. It obtains the preserving adjoint from `exceptionalInverseImage_exists`, identifies its left functor with actual proper pushforward using `proper_exceptional_restriction`, and transports preservation to the supplied right adjoint by `Adjunction.rightAdjointUniq`.

Added proof imports:

- `Mathlib.Algebra.Field.ULift`
- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`
- `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`
- `Sheaf.Paper.FiniteCoefficientDescentTwoColimit`
- `Sheaf.Paper.IntegralConstantModelHeartClosure`

The `import all` declarations reuse existing proved private presentation, coefficient-isomorphism, and sized-localizing-closure lemmas; they do not use the two-colimit or Serre conclusions merely because those helpers occur in those modules. The original namespace and file-level commands are preserved; every additional `open` is scoped to a private helper. The static interface comparison is empty. The DAG proof now records the route actually taken. No statement, definition, universe binder, or public visibility was changed.

Validation: the complete proof compiled cleanly through the required `lcompile.py`; after import pruning it compiled again without errors or warnings. The file contains no `sorry`, `axiom`, or data definition. Every new line is at most 100 characters. The new imports have no path back to this module; the existing unit route is retained through `sk-thm-existence` and `det-cor-existence-ii-restriction`.

## Proved and sorry left

Closed 1 of the original 1 holes: `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible` (node `lem-sfb-adic-localizing-exceptional-cohomology`). Added 0 holes; split off 0 statements. No `sorry` remains in the delivery. This is a proof from existing library statements, including their existing proof obligations; it is not a claim that all transitive dependencies are axiom-free yet.

## No longer needed

Removed these direct imports:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `Sheaf.Paper.LocalizingExceptionalAdjoint`
- `Sheaf.Paper.RationalExceptionalRestriction`
- `Sheaf.SixFunctors.IntegralBrownAdjoint`
- `Sheaf.SixFunctors.IntegralExceptionalRestriction`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`

The separate source-restriction applications `sk-thm-restriction`, `det-prop-int-brown-adjoint`, and `sk-thm-int-restriction`, and the separate Brown-existence application `sk-prop-sf-existence`, are unnecessary in this proof: the already-stated `sk-thm-existence` supplies precisely their assembled adjoint-preservation conclusion. Their modules may remain needed transitively and are not claimed to have left the targets' import closure.

`def-weil-pbc-internal-abelian-sheaf-module-equivalence` is unnecessary: all comparisons are made directly in the same internal module-object category, by scalar comap and explicit presentation isomorphisms. The integral torsion-chart and locally-free-resolution modules need no direct import: their contribution is already packaged by `lem-sfb-integral-lfp-constant-model-comparison`. Other removed imports remain available through the retained imports where their definitions or comparison APIs are needed. No module is withdrawn.

Obsolete `tool_uses` approvals removed from this node: `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, `sk-prop-sf-existence`, `sk-thm-restriction`, `det-prop-int-brown-adjoint`, and `sk-thm-int-restriction`. The remaining approval entries keep their original order. The sized-closure helper comes from `det-proper-image-localizing-principle`; the independent reader/maintainer can record its tool use if required. No new approval is written by this worker.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature repair was needed. The previous plan did more work than necessary: `exceptionalInverseImage_exists` already states preservation of the supplied existence theorem's right adjoint, so repeating its rational/integral construction is unnecessary. The essential glue omitted by the earlier splits was the comparison of coefficient presentations and the exact ambient localizing hulls; both are proved here.

The algebraic-closure coefficient is the finite-subextension-valued `Profinite.padicAlgClRingObj`, throughout. No identification with all continuous maps to the algebraic closure is made. Arbitrary finite extensions allowed by the certificate are normalized to actual intermediate fields, rather than silently assuming the two coefficient conventions are definitionally equal. Empty schemes, zero modules, and empty strata are handled by the existing cover/stratification definitions and the generic isomorphism arguments, without added hypotheses.

Read-only dependency-graph audit also encountered an existing unrelated cycle `def-weil-integral-scalar-extension` → `lem-weil-integral-constructible-linear` → `lem-weil-integral-constructible-triangulated` → `def-pur-completed-coefficient-presentation-transport` → `def-weil-integral-scalar-extension`. None of those nodes is changed here. A separate check of all 20 delivered proof dependencies finds no path back to this item.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

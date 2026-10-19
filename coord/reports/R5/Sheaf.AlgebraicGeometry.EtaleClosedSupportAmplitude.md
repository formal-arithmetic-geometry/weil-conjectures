## What changed

Proved `AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_amplitude` in
`Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude`, preserving its entire signature,
universes, hypotheses, conclusions and public imports. Updated its proof docstring and
DAG proof to follow the compiled argument. No definition or statement was changed;
no consumer adaptation or change record is needed.

The shorter route uses the already proved source-library finite truncation induction
lemmas `DerivedCategory.isGE_obj_of_isGE`, `isLE_obj_of_isLE` and `prop_of_bounded`.
Exact pullback preserves [a,b]; degree-zero right-derived bounds give [a,b+c] for
Rj_*j^*K; the closed-support triangle and faithful exact closed pushforward give
[a,b+c+1] for Ri^!K. Constructibility follows from the source homology-property
triangulated subcategory, bounded devissage, exact closed cohomology comparison,
constructible pullback, and the closed counit isomorphism. The finite-constant-value
constructibility predicate is converted in both directions using the proved
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf` comparison.

Proof imports added:

- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
- `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`

The resumed remote single-file compile passed cleanly in 3.9 seconds, with zero
warnings and zero holes. The theorem signature was compared textually with the current
source and is identical; all public imports are preserved and every Lean line is at
most 100 characters. The compile result is retained in scratchpad/compile-resumed.log.

Earlier attempts did not push: the compile service was temporarily busy, one process
was killed with exit code 137, and a retry timed out during delivery worktree checkout.
No delivery process for this item remained running when this session resumed. The
required fresh dry run and delivery use the unchanged launcher tools.

Checked the current main-20261015 amplitude statement and its two proof paragraphs,
the DAG node and the unit realized record (all realized lists are empty). The statement
is unchanged between the archived and current blueprint. The route retains the supported
triangle and Serre-closure argument; it replaces only the auxiliary spectral sequence
with its already proved finite-truncation argument.

## Proved and sorry left

Closed 1 of 1 original holes:

- `AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_amplitude`
  (node `lem-exc-closed-amplitude`), both the amplitude and constructibility clauses.

There are zero `sorry`s left in the item, zero holes added, and zero split-off statements.
The proof uses the existing closed-support triangle and ambient right-adjoint declarations;
this delivery changes only the amplitude module and its proof-route node.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`
- `Sheaf.CategoryTheory.Filtration`
- `Sheaf.CategoryTheory.TruncationCouple`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`

Removed these original direct proof dependencies from this node:

- `def-weil-pbc-etale-constructible-sheaf`
- `lemma-constructible-pullback-stratification`
- `lem-pur-scheme-constructible-preimage`
- `lem-weil-pbc-etale-covering-base-change`
- `lemma-constructible-pullback-constant`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `thm-sp-truncation-e2`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`

`thm-sp-truncation-e2`, `Sheaf.CategoryTheory.TruncationHypercohomology`,
`Sheaf.CategoryTheory.ExactCoupleConvergence`, `Sheaf.CategoryTheory.Filtration`,
and `Sheaf.CategoryTheory.TruncationCouple` are not used: bounded truncation induction
supplies both the amplitude bounds and constructibility. The explicit Grothendieck,
enough-injectives, left-exactness and forgetful comparison wrapper imports are also
unneeded: the source library already supplies the exact/module-valued functor APIs
and their instances. The explicit pullback stratification, cover base-change, constant
sheaf and constructible-preimage wrappers are replaced by the proved constructible
pullback API. Those mathematical facts can remain transitive prerequisites of those
proved APIs; this report does not assert they disappear globally from every target.
The precise modules pruned from the targets' total closure are determined by the
maintainer's import-closure ledger. Obsolete tool_uses entries for the removed direct
proof dependencies were removed while retaining the remaining entries in order.

The newly used proved generic source tools are the triangulated right-derived functor,
the constructibility comparison, the constructible-homology triangulated subcategory,
and constructible pullback; no new tool approval is written into tool_uses.

## Where the brief, the DAG or earlier work was wrong

The original DAG over-planned this auxiliary lemma through hypercohomology convergence,
page induction and filtration reconstruction, although the source library already proves
bounded truncation devissage. No mathematical statement was found false. The DAG comparison
node still records its old Sheaf wrapper/name; its lean_audit correctly names the proved
upstream declaration actually imported here. No node attachment was modified outside the
item, and no duplicate comparison theorem was introduced.

Edge cases checked: no a<=b hypothesis is added (the zero/empty interval case is handled
by the source bounded-devissage lemmas); c=0 retains the upper extra degree; the lower
vanishing uses n-1<a; the upper vanishing uses c>=0 to infer n>b. Constructibility uses
only finite commutative A, and no noetherian, finite-type or quasi-compact scheme assumption
is added. Empty schemes, zero K and the identity/empty complementary pair are allowed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

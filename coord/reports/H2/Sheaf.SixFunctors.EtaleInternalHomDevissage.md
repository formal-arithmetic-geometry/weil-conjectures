## What changed

Restored the complete quarantined item at its original Lean path and proved
`AlgebraicGeometry.Etale.isBoundedConstructible_finiteTor_derivedHom_by_devissage`.
The public declaration signature and all seven archived public imports are unchanged.
No definition, source-library file, other consumer, or target statement changed.

The proof converts the recorded predicates to the source `constructibleFiniteTor`,
passes to the algebraic closure of the separably closed base, applies the existing
source preservation theorems over that algebraically closed field, and descends
along the purely inseparable universal homeomorphism. Three fully proved private
helpers supply predicate conversion, the internal-Hom comparison, and descent.
The DAG proof and dependencies now describe this route. The archived docstring's
original proof plan remains as documentation of the statement-stage argument;
an inline proof comment identifies the replacement route.

Validation: the entire restored module compiles through `lcompile.py` in 6.3 seconds
with no diagnostics. The initial specialized internal-Hom comparison exceeded the
60-second limit; isolating its steps located the kernel computation at the
comparison of derived monoidal structures. Following the source `Point.lean`
implementation note, the comparison is proved for an abstract coefficient category
before specialization. The complete module is compiled together; no limit was raised
and no statement was split to satisfy the time limit.

## Proved and sorry left

Closed the single archived hole:
`AlgebraicGeometry.Etale.isBoundedConstructible_finiteTor_derivedHom_by_devissage`
(node `det-rem-sf-matrix-hom-devissage`). Proved 1 of 1 original holes.
There are zero `sorry` declarations left in the item and zero holes added elsewhere;
zero results were split off. The three private helpers are proved in full.
This uses existing library declarations with their existing dependencies; it does
not claim that all imported library theorems are independent of existing holes.

## No longer needed

Removed the following archived proof-only imports (the duplicated reduced-induced
closed-subscheme import is listed once):

- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.SixFunctors.FlatModelGeneration`
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.SfHomTriangulated`
- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Paper.StratumAmbientHom`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`
- `WeilConjectures.ConstructibleSheaf.GenericConstancy`
- `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.LisseSplitHomFlatConstructible`
- `Sheaf.Paper.DirectImageCtfOpenTor`

The following original proof dependencies are no longer direct dependencies of this
item's proof; the corresponding 28 old `tool_uses` approvals were removed, without
adding or rearranging approvals:

- `cor-fin-deligne-open-finite-coefficients`
- `det-cor-sf-direct-image-ctf-open-tor`
- `det-sf-flat-model-generation`
- `lem-cbc-open-closed-recollement`
- `lem-exc-closed-support-triangle`
- `lem-fin-closed-immersion`
- `lem-kun-04ca`
- `lem-kun-0f10`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-sf-etale-flat-constructible`
- `lem-sf-hom-triangulated`
- `lem-sfb-lisse-split-hom-flat-constructible`
- `lem-weil-pbc-constructible-etale-set-pullback`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`
- `lem-weil-pbc-ringed-topos-flat-module-pullback`
- `lem-weil-stratum-ambient-hom`
- `lemma-openclosed-stalk-lowerstar`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-constructible-derived-subcategory`
- `prop-constructible-generic-constancy`
- `prop-openclosed-lowerstar-fully-faithful`
- `prop-weil-pbc-geometric-stalks-exact`
- `prop-weil-pbc-inverse-image-modules-exact`
- `thm-constructible-serre`

These are item-level dependency/import removals, not withdrawals of their declarations
or claims that the modules are unused elsewhere in the targets' closure. In particular,
source preservation can continue to use some of this theory internally. The seven
public imports are preserved as the restored public interface. Every new proof-only
import directly supplies a declaration used by the proof.

## Where the brief, the DAG or earlier work was wrong

The module's absence is quarantine, as recorded in `coord/rework.tsv`, not withdrawal.
The archived source was restored, preserving its Lean attachment and theorem statement.
No deletion or empty replacement is proposed.

The original DAG plan is valid but not needed given the currently proved source
library. Its source preservation theorem assumes algebraic closedness, which cannot
be inferred from separable closedness. The proof therefore explicitly constructs the
algebraic-closure base change and proves descent; it never adds a perfectness,
algebraic-closedness, separatedness, or coefficient-presentation hypothesis.

The source preservation declarations themselves apply to arbitrary finite commutative
rings with invertible exponent; the similarly named Sheaf.Paper declarations have
more specialized coefficient statements and are not used. The DAG step cites the
actual source declarations directly. Source modules were only read and imported.
No chapter or unit record or realized unit statement/step was changed. Searches used
LeanFinder, Loogle, the project grep service, and local source searches.

Edge cases checked in the argument: empty schemes, nonreduced and nonseparated
finite-type schemes, the zero coefficient ring (including exponent n=0), and reversed
intermediate Tor/support intervals. Predicate conversion widens those intervals to
ordered hulls; the source theorem handles empty schemes. The universal-homeomorphism
and monoidal-equivalence arguments require no nonemptiness or coefficient
nontriviality. No new nodes or statement/definition repairs were needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the sole remaining sorry in the assigned source module by finite truncation
induction using `prop_of_boundedConstructibleModule`. The inverse image of bounded
constructibility under the triangulated right-derived direct-image functor is
triangulated. For a constructible sheaf in degree zero, the generic right-derived
lower bound is combined with two separate finiteness inputs: an upper bound and
constructibility of every cohomology sheaf. These inputs are new single-statement
Sheaf modules. Existing source signatures, attributes, public imports and all
non-theorem bodies are unchanged. All three sandbox modules compile through
`lcompile.py --all` after including the coefficient parameters explicitly. A
read-only traversal of the overlaid DAG confirms that neither new node reaches
the parent theorem. The main DAG proof now records this induction.

## Proved and sorry left

Closed the source hole
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`
from two strictly smaller single-sheaf assertions. This is a decomposition, not a
net proof: 1 original hole removed, 2 holes added, net -1. There are zero sorry
bodies left in the assigned module. The new holes are:

- `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`
  (`lem-sfb-dc-lower-star-single-bound`). Only an upper cohomological bound for F[0].
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeDirectImage_single_constructible`
  (`lem-sfb-dc-lower-star-single-constructible`). Only constructibility of the
  individual cohomology modules of Rf_*(F[0]).

The assembly uses the finite truncation triangles through an existing complete
Lean induction; neither new assertion quantifies over bounded constructible
complexes. The first compile caught omitted section parameters in the new statements; explicit
`include ℓ k` restores all prime and coefficient hypotheses before delivery.

Edge checks: zero sheaves and the zero coefficient ring give zero;
f=id gives a single sheaf in degree zero; negative direct-image degrees vanish;
finite torsion coefficients retain the prime-to-characteristic condition. No Tor
amplitude is imposed on F or on finite torsion coefficient rings.

## No longer needed

Removed these private proof imports from the assigned module (no public imports
removed):

- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.Paper.DerivedInternalHomFilteredColimit`
- `Sheaf.Paper.IntegralHomReduction`
- `Sheaf.Paper.IntegralLfpConstantModelComparison`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`
- `WeilConjectures.Algebra.Homology.KFlat`
- `WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`
- `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`

The source proof no longer directly uses these old proof dependencies:

- `def-sfb-rationalization-equivalence`
- `lem-kun-dimension-finite-type`
- `lem-sf-integral-direct-image-constructible`
- `lem-sfb-extend-scalars-bounded-constructible`
- `lem-sfb-extend-to-qlbar-constructible`
- `lem-sfb-finite-discrete-constructible-model`
- `lem-sfb-integral-ambient-tower-comparison`
- `lem-sfb-integral-constructible-completion-bridge`
- `lem-sfb-localized-direct-image-comparison`
- `lem-sfb-normed-coefficient-realization`
- `lem-sfb-qlbar-direct-image-comparison`
- `lem-weil-pbc-finite-discrete-derived-coefficient-data`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-qcqs-over-affine`
- `sk-def-sfb-dc-setting`
- `sk-def-sfb-rationalization`
- `sk-thm-sfb-qlbar-two-colimit`
- `thm-dg-finite-type-constructibility`
- `lem-sfb-proper-dc-preserves-continuous`
- `lem-sfb-proper-dc-preserves-qbar`
- `lem-sfb-proper-dc-preserves-integral`

The coefficient-comparison dependencies remain in the proof plans of the two
new nodes. This delivery does not claim that these modules are globally pruned,
and withdraws no declaration or module. The old proper-direct-image nodes are
not used by this finite-truncation assembly. The unit record has no realized
nodes; its integral-completion and rational-continuity route remains in the
single-sheaf finiteness arguments.

## Where the brief, the DAG or earlier work was wrong

The planned direct imports are obstructed by import paths back to this module.
For example, IntegralConstructibleCompletionBridge imports CartesianCoefficients,
which reaches ContinuousCoefficientCommRing, then BaseChangeTheorems.MorphismDefs,
then the assigned module. FiniteDiscreteConstructibleModel reaches it via
FiniteDiscreteCoefficientEncoding and FiniteDiscreteRealizationFunctor.
LocalizedDirectImageComparison has the same CartesianCoefficients path.
`tools/import_direction.py may` rejects these imports. Thus the already-stated
coefficient bridges cannot simply be imported into this source theorem.
The new statements have only lower-level public imports, avoiding that cycle.
The current blueprint omits the finite-discrete case present in the adopted
source signature; the source signature and the additional true case are retained.

## New nodes

`lem-sfb-dc-lower-star-single-bound` states only existence of an upper bound for
the direct image of a constructible sheaf in degree zero. Its proof follows the
same coefficient reduction as the source, taking the upper endpoint at each step.
It does not include the truncation induction for general complexes.

`lem-sfb-dc-lower-star-single-constructible` states only constructibility of each
higher direct image of a constructible sheaf. Its coefficient-wise proof is
recorded in its node and docstring. Both nodes retain the original chapter and
unit. No definition, statement or consumer interface changes; no change record
is required.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

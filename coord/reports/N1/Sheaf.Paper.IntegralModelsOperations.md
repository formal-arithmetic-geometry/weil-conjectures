## What changed

Retained the interrupted attempt and proved the parent theorem from its pullback,
tensor, immersion and projection constituents. The parent statement is unchanged. Its proof docstring now describes the Lean route
and its four constituent arguments.
Five new modules isolate and prove the constituents: constant-model preservation
for open and closed sheaf images; the open projection formula by internal-Hom
adjunctions; the closed projection formula by the existing closed formula and
derived comparisons; the degree-zero tensor calculation using stratified local
finite presentation; and bounded tensor closure by two finite cohomological
inductions. All six delivered modules contain zero sorry.
The parent supplies the four constituent functions directly. It uses exact-functor
homology and boundedness comparisons. Its closed direct
image is identified with the exact termwise functor through the actual derived
comparison. The locally closed projection formula composes the open and closed
formulas and the derived upper-star composition comparison. All proof dependencies
are ordinary imports. No existing public interface, definition, or target is changed.
Local irreducibility settings keep elaboration from expanding monoidal, inverse-image,
and derived-functor constructions. The degree-zero proof first establishes the generic
Noetherian stratified calculation in a private helper and uses the explicit derived
pullback tensor comparison. It uses the canonical resolution instances directly:
local caches caused costly comparison of the derived structures in both tensor modules.
The upper bound is annotated at degree zero directly, avoiding an arithmetic rewrite
through the complete derived-object type.
The specialized complex monoidal shortcuts are disabled only within the two
degree-zero declarations. The closure proof carries out the two inductions in a
private lemma for an arbitrary abelian monoidal category and a weak Serre property. Its specialization then supplies
the integral heart closure and sheaf tensor results. This avoids repeatedly unfolding
the coefficient category while transporting kernel and cokernel closure. An explicit
equation identifies the coefficient derived tensor with the generic monoidal tensor.
The specialization transports the sheaf case and the final result along that equation
with congrArg and Eq.mp/Eq.mpr. Keeping derivedTensor locally irreducible and using
these explicit transports avoids goal conversions through the monoidal construction. No limit is increased and no kernel check is suppressed.

The proof-context commands are documented in
coord/changes/N1-integral-models-proof-context.md for the static interface check.
The theorem has two external textual users; both retain the same interface, and
no downstream module is adapted.

All six modules compile without warnings. The repaired closure and parent compiled
in 33.0 and 14.5 seconds respectively. The required delivery dry run passed
compilation, axiom probes and stage-3 preflight with the proof-context change record
included. Its review class is CODEX because it adds the five proved constituent
modules and nodes and records local proof-context commands.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations
(det-lem-integral-models-operations). Proved all five new constituent declarations:

- AlgebraicGeometry.ProEtale.CondensedRing.constantModel_immersion_images
  (lem-sfb-constant-model-immersion-images).
- AlgebraicGeometry.ProEtale.CondensedRing.constantModel_open_projection
  (lem-sfb-constant-model-open-projection).
- AlgebraicGeometry.ProEtale.CondensedRing.constantModel_closed_projection
  (lem-sfb-constant-model-closed-projection).
- AlgebraicGeometry.ProEtale.CondensedRing.integralModels_tensor_closure
  (lem-sfb-integral-models-tensor-closure).
- AlgebraicGeometry.ProEtale.CondensedRing.integralModels_sheaf_tensor
  (lem-sfb-integral-models-sheaf-tensor).

Holes closed: 1 of 1 original holes. Holes added: 0. Holes remaining in the
six delivery modules: 0. No private helper or definition contains sorry.
The proof uses existing declared dependencies, including
integralLfpConstantModelComparison, whose current proof is still sorry; this is
an existing dependency, not a hole added by the delivery. No claim is made that
the complete transitive axiom closure of the parent is already sorry-free.

## No longer needed

Removed direct proof imports from the original item module:

- WeilConjectures.ConstructibleSheaf.Pullback
- Mathlib.AlgebraicGeometry.Sites.Proetale
- Mathlib.CategoryTheory.MorphismProperty.Composition
- Mathlib.CategoryTheory.Sites.Precoverage
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Mathlib.LinearAlgebra.FreeModule.PID
- Sheaf.Algebra.Homology.KFlat
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.CategoryTheory.Sites.ConstantSheaf
- Mathlib.CategoryTheory.Sites.Sheafification
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.AlgebraicGeometry.NoetherianStratumDetection
- Mathlib.Algebra.Homology.DerivedCategory.TStructure
- Sheaf.Paper.ProjectionMateExact
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Mathlib.CategoryTheory.Adjunction.Limits
- WeilConjectures.CategoryTheory.SiteMorphismComposition
- Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
- Sheaf.AlgebraicGeometry.IntegralConstantCompletion
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients

The tensor-closure module also drops direct imports of ExtensionIntegersDvr,
FreeModule.PID, NoetherianStratumDetection, RingedTopoiCanonicalTensorPullbackOfUniverses,
DerivedCategory.HomologySequence and DerivedCategory.TStructure. The degree-zero
child instead uses LfpTensorSingle, the integral local-finite-presentation comparison,
the common stratification construction and abelian stratum zero detection.
The tensor-pullback edge uses new-proetale-derived-module-pullback-monoidal, which
records the actual imported module-object comparison. Exact homology transport is
recorded explicitly by lem-weil-pbc-exact-functor-bounded-below.
The explicit scalar Smith-form and cyclic K-flat calculations are already handled
by the existing local tensor theory; they are not new obligations here.

The new projection proofs need neither ringed-slice tensor totalization nor an
additional projection mate, weakly-etale localization, K-flat-resolution transport,
or a site-morphism composition theorem: internal-Hom duality, uniqueness of left
adjoints and the existing derived composition API suffice. The following old direct
proof dependencies and maintainer tool approvals are no longer direct parent edges;
those used in child nodes remain there. No whole module is withdrawn. Comparing the current dependency closures of the item
node gives 2603 old nodes and 2592 new nodes, with 46 nodes removed.
This comparison follows statement and proof edges in the DAG, with the sandbox nodes
overlaid on the current shared sources. It does not measure the targets' compiled
import closure. The removed nodes are:

- det-prop-integral-criterion-constant-coefficients
- lem-pe-internal-section-tensor-comparison
- lem-pe-kflat-roos-representative-invariance
- lem-pe-roos-coordinates-quasi-iso
- lem-sfb-abstract-kflat-resolution
- lem-sfb-extend-scalars-kflat
- lem-weil-pbc-affine-closed-specialization-localization
- lem-weil-pbc-affine-proetale-single-cover-local-surjectivity
- lem-weil-pbc-bounded-extremally-disconnected-cover
- lem-weil-pbc-closed-immersion-base-change
- lem-weil-pbc-etale-contraction-size
- lem-weil-pbc-existing-weakly-etale-indetale-refinement
- lem-weil-pbc-finite-global-presentation-internal-hom-colimit
- lem-weil-pbc-finite-list-cardinality
- lem-weil-pbc-flat-generalizations-lift
- lem-weil-pbc-localization-kan-discrete-lifts
- lem-weil-pbc-localization-ring-weakly-etale
- lem-weil-pbc-localization-spectrum-embedding
- lem-weil-pbc-localization-units-or-zero
- lem-weil-pbc-module-inverse-image-unit-comparison
- lem-weil-pbc-principal-w-localization-size
- lem-weil-pbc-proetale-closed-abelian-filtered-colimits
- lem-weil-pbc-proetale-module-specialization-unit
- lem-weil-pbc-proetale-qcqs-fp-section-calculus
- lem-weil-pbc-proetale-ringed-closed-counit
- lem-weil-pbc-proetale-ringed-filtered-colimits
- lem-weil-pbc-proetale-ringed-localization-sequence
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-proetale-shriek-specialization-zero
- lem-weil-pbc-proetale-specialization-restriction-sections
- lem-weil-pbc-retained-localization-size
- lem-weil-pbc-site-finite-presentation-internal-hom-colimit
- lem-weil-pbc-spec-localization-away-basic-open
- lem-weil-pbc-strict-w-cover-size
- lem-weil-pbc-wcontractible-affine-weakly-contractible
- lem-weil-pbc-wcontractible-closed-localization
- lem-weil-pbc-wcontractible-cover-section
- lem-weil-pbc-wcontractible-geometric-criterion
- lem-weil-pbc-wcontractible-ring-extension
- new-lem-weil-pbc-proetale-module-canonical-unit
- new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison
- new-lem-weil-pbc-specialization-affine-coordinates
- new-lem-weil-pbc-specialization-closed-site-counit
- new-lem-weil-pbc-specialization-unit-comparison
- sk-def-pe-derived-completion
- sk-def-sfb-derived-extension-of-scalars

Old direct parent dependencies removed:

- def-pc-flat-sheaf-modules
- def-pc-kflat-complex
- def-sbc-standard-tstructure-derived-category
- def-weil-pbc-constant-sheaf
- def-weil-pbc-proetale-site
- def-weil-pbc-sites-and-cohomology
- det-prop-integral-criterion-constant-coefficients
- lem-galois-fpqc-covering-base-change
- lem-pc-kflat-resolution
- lem-sc-dvr-saturation-line-smith-normal-form
- lem-sf-derived-homology-long-exact
- lem-weil-l-adic-extension-integers-dvr
- lem-weil-pbc-left-adjoint-preserves-colimits
- lem-weil-pbc-noetherian-stratum-detection
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-ringed-projection-mate-exact
- lem-weil-pbc-ringed-slice-extension-tensor
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-weil-pbc-sheafification-exact
- lem-weil-pbc-site-morphism-composition
- lem-weil-pbc-weakly-etale-composition-base-change
- lem-weil-proetale-weakly-etale-localization
- lemma-constructible-pullback-stratification
- sk-def-sfb-bounded-constructible
- sk-def-sfb-constructible
- sk-def-sfb-derived-categories
- sk-def-sfb-derived-tensor-hom
- sk-prop-sfb-cartesian-coefficients

All original top-level tool_uses entries are withdrawn in the parent node:

- lemma-constructible-pullback-stratification
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-weil-l-adic-extension-integers-dvr
- lem-weil-pbc-noetherian-stratum-detection
- lem-weil-pbc-ringed-projection-mate-exact
- lem-weil-proetale-weakly-etale-localization
- lem-pc-kflat-resolution
- lem-weil-pbc-ringed-slice-extension-tensor
- lem-weil-pbc-site-morphism-composition
- lem-weil-pbc-sheafification-exact

## Where the brief, the DAG or earlier work was wrong

The resumed source no longer elaborated within 60 seconds: generic derived-functor
expansion and repeated structural instance comparisons were expensive. Local reducibility
settings and the explicit comparison API keep the constructions compact. In the degree-zero
module, removing local function-valued resolution-instance caches and annotating the upper
bound directly at zero resolves its timeout. The closure module uses an abstract private
categorical lemma for the two inductions, avoiding repeated coefficient-structure reduction.
A subsequent required dry run still timed out in its specialization. Profiling located
costly goal conversions through the derived tensor. Explicit equality transport replaces
those conversions and keeps derivedTensor locally irreducible during elaboration.
No definition or public statement changes, no limit is increased, and kernel checking
remains enabled.

The retained report was stale: it listed the degree-zero tensor theorem as sorry,
but its module contains a complete proof. The current delivery retains that proof
and aligns its docstring and DAG with the actual local finite-presentation route.
The old open-projection plan called for a separate K-flat totalization argument;
the existing natural internal-Hom formula supplies its dual adjunction argument.
The closed formula already exists for supportPullback and exact termwise direct
image, so the actual derived comparison isomorphisms are used.

The independent integral constant-model weak Serre lemma applies to arbitrary
Noetherian schemes and has no dependency path back to this item. It supplies the
triangulated closure needed for bounded dévissage; it is not replaced by a finite-type
or finite-coefficient theorem. Other tensor theorems found by search impose finite
field/type hypotheses and cannot prove the present arbitrary-Noetherian statement.
No such hypothesis was added. Empty loci, zero modules, identity immersions and empty
cohomological intervals are included in the constructions and adjunction arguments.

The current shared DAG already has the cycle
lem-weil-integral-constructible-triangulated ->
def-pur-completed-coefficient-presentation-transport ->
prop-weil-pbc-scalar-extension -> def-weil-integral-scalar-extension ->
lem-weil-integral-constructible-linear -> lem-weil-integral-constructible-triangulated.
The same cycle is present before and after this delivery; no edge of it is edited.


## New nodes

lem-sfb-constant-model-immersion-images: proved sheaf-level preservation for open
extension and closed direct image, with arbitrary commutative condensed coefficients.
The parent separately supplies cohomology and boundedness transport.

lem-sfb-constant-model-open-projection: proved unbounded open projection formula
from the natural internal-Hom formula and uniqueness of left adjoints.

lem-sfb-constant-model-closed-projection: proved transport of the existing unbounded
closed formula to the precise right-derived and upper-star functors in the parent.

lem-sfb-integral-models-tensor-closure: proved bounded tensor dévissage from its
sheaf case and the integral constructible weak Serre property.

lem-sfb-integral-models-sheaf-tensor: proved degree-zero part of original steps 4--7.
It compares constant models with stratified local finite presentation, uses the
existing local tensor calculation on a common stratification, descends the lower
cohomology bound by zero detection, and transports constructibility back.

Proof-context change record: coord/changes/N1-integral-models-proof-context.md.
The static checker records the parent's local irreducibility and namespace-opening
commands. No definition, existing public statement, or public import changes.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

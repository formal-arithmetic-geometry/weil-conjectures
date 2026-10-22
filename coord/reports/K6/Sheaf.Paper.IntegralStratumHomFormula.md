## What changed

Replaced both proofs in `Sheaf.Paper.IntegralStratumHomFormula`, preserving every existing
public declaration signature and public import. No source-library module
was changed. The proof imports the existing bounded-degree devissage, signed triangulated shifts,
cover-local dualizability and local Tor descent, open–closed internal-Hom formulas,
closed-support adjunction and derived tensor APIs.

The filtration uses the bounded interval already present in constructibility. Its finitely many
cohomology sheaves admit one ordered reduced stratification. Reverse induction on its closed
tails generates each sheaf from the prescribed stratum extensions. Bounded devissage and a
finite extension-hull induction give the actual sequence of distinguished triangles. When the
original object is concentrated in degree zero, only the zero shift is used.

The Hom formula obtains a common pro-étale locally free resolution of the constant model,
descends dualizability and the dual Tor interval, and combines the closed and open Hom
identities with the global-sections comparison along a right adjoint. A K-flat representative
comes from the existing derived tensor model. Tensoring with that complex preserves colimits
by its complex tensor–Hom adjunction. The dual tensor functor is a right adjoint as well, so
it preserves the countable products in the stated Roos triangle; exactness then gives the
required derived-limit triangle with its specified product projection.

Three new supporting modules contain complete proofs. The parent DAG proof and dependencies
now describe this route. Local irreducibility settings keep proof elaboration on the existing
functor APIs instead of expanding sheafification and chosen derived-category representatives.
The dual Tor, tensor comparison, K-flat model and tower calculation are performed together
over an abstract abelian category, then specialized to the concrete coefficient modules.
The Hom comparison itself keeps the coefficient ring abstract until the final specialization.
Dualizability descends directly by the cover theorem; the Tor component of the existing
local-duality-descent theorem supplies the global Tor bound. The chosen dual directly gives
the tensor adjunction. Uniqueness of right adjoints identifies it with the recorded internal
Hom, and evaluation at the unit identifies the chosen and recorded dual objects.
The K-flat representative is eliminated from an existential statement before entering the
tensor comparison, keeping its data abstract during elaboration. Private comparison lemmas
identify the derived and complex monoidal structures once, then transport tensoring, the
unit and dualizability by congruence. The recorded internal Hom is handled by uniqueness
of right adjoints, so the categorical argument does not unfold its chosen implementation.
A private generic lemma transports the derived two-term resolution along its cokernel
isomorphism before specializing its monoidal structure. The cover-descent isomorphism
is handled by the same generic interface. This avoids repeatedly normalizing the concrete
module-object tensor structure in the dualizability proofs. The full conclusion is packaged
as a private proposition, so final coefficient specialization applies the generic proof once.
Finite-model invariance under isomorphism is proved directly by transporting the cover
isomorphisms, which avoids importing the old filtration module directly into the parent.
Three public generic constructions now keep the coefficient ring abstract in derived
sections, the derived dual and tensor by that dual. Their existing integral definitions
delegate to the same constructions. This is a definition performance repair: projecting
the monoidal unit independently before and after specialization caused expensive kernel
normalization. The original ordinary sections abbreviation is unchanged. The generic
construction bodies unfold to the original definitions, with no change of mathematical
meaning. No external module uses the repaired definition names directly.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_filtration`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_hom_formula`.

New proved declarations:

- `AlgebraicGeometry.ProEtale.CondensedRing.integral_constantModel_localResolution`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteConstantModels_commonReducedStratification`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteConstantModel_fixedStrata_generation`.

The server compiled all four delivery modules together successfully. Two original holes
closed; zero holes added; zero holes left in the delivered modules.
No theorem is merely renamed or moved to another hole. Existing imported statements that
remain unfinished elsewhere are used as the stage-3 brief permits.

## No longer needed

No original public import was removed; no existing module or declaration was withdrawn.
The following original proof imports were removed directly (some remain available indirectly
through implementations still used):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`.
- `WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle`.
- `Sheaf.Paper.CoefficientHeartCommonStratification`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `WeilConjectures.AlgebraicGeometry.ImmersionFiberDegreeOne`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.CartesianCoefficients`.
- `Sheaf.Paper.IntegralModelSurjectiveClosedReflection`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`.
- `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`.
- `Mathlib.CategoryTheory.Adjunction.Unique`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Mathlib.RingTheory.FiniteType`.
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
- `Sheaf.Paper.IntegralConstructibleHeart`.
- `Sheaf.Paper.IntegralHeartDualizable`.

The new local-resolution module keeps finite-projective dualizability as a private proof
import and omits the unused derived-Hom import; the generation module does not import
constructibility publicly, and its short-exact-triangle import is private.

The following are no longer direct proof dependencies of this node (some still occur inside
the proved supporting modules or existing imported implementations):

- `sk-lem-int-integral-heart`.
- `lem-pc-derived-lower-truncation-step-triangle`.
- `lem-wf-affine-noetherian-components`.
- `det-lem-coefficient-heart-common-stratification`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `lem-weil-pbc-immersion-fibre-degree-one`.
- `def-weil-closed-immersion`.
- `def-weil-proetale-inverse-image`.
- `sk-prop-sfb-cartesian-coefficients`.
- `sk-def-sfb-module-pushforward-pullback`.
- `lem-sfb-integral-model-surjective-closed-reflection`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `lem-weil-pbc-complex-ses-triangle`.
- `sk-def-localizing-closure`.
- `det-lem-formal-closed-support-derived`.
- `lem-sfb-derived-internal-hom-sections-model`.
- `sk-def-sfb-derived-tensor-hom`.
- `prop-pur-kinjective-resolutions-exist`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `det-prop-sfb-qlbar-colimit-x-integral-limit`.
- `det-lem-int-integral-heart-dualizable`.
- `lem-sfb-dual-tensor-adjunctions`.
- `lem-pc-kflat-resolution`.
- `lem-pc-module-filtered-colimits-tensor`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
- `def-pc-tensor-complex-sheaves`.
- `def-weil-abstract-derived-category`.

The retained approved tools stay in their original order. The following obsolete entries
were removed from this node's `tool_uses`:

- `lem-wf-affine-noetherian-components`.
- `lem-pc-derived-lower-truncation-step-triangle`.
- `det-lem-coefficient-heart-common-stratification`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `lem-weil-pbc-fibre-product-points`.
- `sk-prop-sfb-cartesian-coefficients`.
- `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement`.
- `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`.
- `new-lem-weil-pbc-condensed-surjective-closed-equivalence`.
- `prop-pur-kinjective-resolutions-exist`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-pc-kflat-resolution`.
- `lem-pc-module-filtered-colimits-tensor`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
- `det-prop-sfb-qlbar-colimit-x-integral-limit`.
- `lem-weil-pbc-immersion-fibre-degree-one`.

The reduced refinement factors directly through each old locally closed immersion and pulls
back its finite presentation. The old surjective closed-cover/reflection detour and its fibre
product argument are unnecessary. Existing degreewise bounded devissage replaces a separate
lower-truncation/octahedral construction. The complex tensor adjunction and exact product-
preserving tensor functor replace filtered-colimit and separate tower-existence machinery.
No claim is made that an adopted upstream declaration or its dependencies may be deleted.

## Where the brief, the DAG or earlier work was wrong

The old plan's closed-cover reflection is unnecessary for reduced refined strata; the existing
reduced-source factorization lemma gives the needed restriction directly. Constructibility
already supplies the bounded interval, so its proof does not need to re-establish boundedness
from a separate integral-heart theorem. The unit route is preserved: first finite stratum
filtration, then local duality and the open–closed Hom comparison, with the tensor and tower
clauses derived from the same dual.

No existing statement was found false or changed. Three definitions received the generic
coefficient performance repair described above and in the change records. No forced
adaptation was needed. Choosing a stratification directly inside the data of subsequent functors caused
large elaboration costs; existential elimination with abstract scheme parameters avoids
expanding those proof-dependent choices. The generic filtration, Hom comparison and combined
tensor/limit helper also keep coefficient-specific normalization out of the categorical arguments.
The canonical internal-Hom comparison is unnecessary for constructing the dual tensor
adjunction; the already imported descent theorem remains needed for its Tor component.

## New nodes

Each new node records LeanSearch, Loogle/LeanFinder and a Mathlib source search.
LeanSearch found general finite-presentation, constructibility and sheaf APIs, without
any matching geometric resolution or stratification-generation result.

`lem-integral-constant-model-local-resolution` records the locally free two-term resolution
on one pro-étale cover. Its module transports the existing coefficient-ring resolution through
the small coefficient-ring isomorphism and exact inverse image; both free terms are dualizable.
The result is fully proved and is strictly the local resolution input to duality descent.

`lem-finite-constant-models-common-reduced-stratification` records common ordered reduced
strata and reduced closed tails for a finite family. It intersects old partitions, applies the
proved Noetherian ordered refinement, constructs the reduced induced closed schemes and
restricts each finite constant model by reduced-source factorization. It is fully proved,
including the empty-family and empty-scheme cases.

`lem-finite-constant-model-fixed-strata-generation` records generation of a single module
from one fixed reduced stratification. Reverse induction on the closed tails uses the open–
closed short exact sequence and its distinguished triangle. The empty final tail is zero and
the first tail covers the whole scheme. This lemma is fully proved and does not assert the
bounded derived filtration or any part of the Hom formula.

Definition-change records:

- `coord/changes/integralStratumDerivedSections-generic-coefficient-api.md`.
- `coord/changes/integralStratumDual-generic-coefficient-api.md`.
- `coord/changes/integralStratumDualTensor-generic-coefficient-api.md`.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

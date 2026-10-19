/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.SixFunctors.FlatModelGeneration
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Paper.StratumAmbientHom
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-!
# Finite-field internal Hom finiteness over an arbitrary ground field

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.7.13 with
`R = A` and `m = 0`, Definition 6.5.1 and Lemma 6.3.16
(blueprint: lem-sfb-finite-field-internal-hom-finiteness).

The coefficient is the continuous-map condensed ring of the discrete finite field,
pulled back along the recorded inverse image from the point. Constructibility uses the
recorded finite constant scalar models, and Hom is the ambient Layer-B derived Hom.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The discrete finite field as a condensed ring, using the recorded continuous-map
construction, with sections `C(S,A)` and pointwise ring operations.
Source: Bhatt--Scholze, Section 6.5 with `R = A`, `m = 0`
(blueprint: lem-sfb-finite-field-internal-hom-finiteness). -/
noncomputable def finiteFieldCondensedRing (A : Type u) [Field A] [Finite A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  exact Profinite.continuousMapRingObjOfUniverse.{u, u} A

/-- The canonical pointwise ring structure of the discrete finite coefficient field.
Source: Bhatt--Scholze, Section 6.5 with `R = A`, `m = 0`
(blueprint: lem-sfb-finite-field-internal-hom-finiteness). -/
noncomputable instance finiteFieldCondensedRingMonObj (A : Type u) [Field A] [Finite A] :
    MonObj (finiteFieldCondensedRing A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  exact Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A

/-- The discrete finite coefficient field is a commutative condensed ring.
Source: Bhatt--Scholze, Section 6.5 with `R = A`, `m = 0`
(blueprint: lem-sfb-finite-field-internal-hom-finiteness). -/
noncomputable instance finiteFieldCondensedRingComm (A : Type u) [Field A] [Finite A] :
    IsCommMonObj (finiteFieldCondensedRing A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A

/-- Ambient derived internal Hom preserves bounded finite-constant-model constructibility
for finite field coefficients over any characteristic-p ground field with `p ≠ l`.
Source: Bhatt--Scholze, Lemma 6.7.13, finite-field specialization, together with
Definition 6.5.1 and Lemma 6.3.16
(blueprint: lem-sfb-finite-field-internal-hom-finiteness).

Proof (the eleven steps of the node):
1. The discrete condensed ring has locally constant functions as sections. Inverse image
from the point preserves sheafification; the Kan extension of the constant presheaf is
constant, since the indexing category has the terminal map to `T[*] = T`. Thus its pullback
is the constant ring sheaf A. Finite presentation, finite generation and finite dimension
over A coincide. Finite-type schemes over k are Noetherian, as are their closed and open
subschemes. Their immersion maps are finite type and qcqs. The ring-object module category
and tensor are the ordinary constant-ring module category and K-flat tensor, so uniqueness
of right adjoints identifies the ambient Hom with the ringed-site Hom below.
2. The weak-Serre result `lem-sfb-discrete-noetherian-constructible-serre` applies to A.
Its affine-local convention agrees with the global finite stratification convention:
restrict a partition to affine opens; conversely use a finite affine cover and
`lem-weil-pbc-etale-stratification-local-gluing-core` to refine the local partitions.
Pullback of their constant finite models gives the global models. Thus constructible
sheaves are closed under zero, kernels, cokernels and extensions.
3. Apply `lem-sbc-cohomology-in-weak-serre-subcategory`: the bounded constructible
complexes are closed under shifts and distinguished triangles.
4. Exact inverse image commutes with cohomology by
`lem-weil-pbc-site-pullback-abelian-exact` and
`lem-weil-pbc-exact-functor-complex-cohomology`. Constructible pullback is supplied by
`lem-weil-pbc-module-constructible-pullback`. For finite A, refine covers until the finitely
many matrix entries are scalar constants; their cokernels are finite-dimensional models.
Thus ordinary inverse image preserves both constructibility and every bounding interval.
5. Choose bounded constructible etale origins using
`lem-weil-pbc-finite-ring-constructible-derived-origin`. Since l annihilates A and is
invertible in k, `thm-dg-finite-type-constructibility` applies over this arbitrary field.
The bounded-below qcqs comparison `sk-thm-pe-direct-image-comparison` identifies ordinary
pro-etale direct image with inverse image of the etale direct image. Hence finite-type
ordinary direct images preserve bounded constructibility, in particular for the immersions.
6. For a closed g with open complement h, `lem-exc-proetale-support-triangle` gives
`g_* Rg^! M -> M -> Rh_* h^* M`. Steps 3--5 make its first term bounded constructible.
The exact inverse image g^*, and g^* g_* = id from
`lem-weil-pbc-proetale-ringed-open-closed`, give bounded constructibility of `Rg^! M`.
7. Every constant-field module sheaf is flat: by
`lem-pc-sites-module-sheafification-tensor` its tensor is sheafified sectionwise tensor
over A. A basis makes sectionwise tensor preserve injections, and exact sheafification
(`lem-weil-pbc-sheafification-exact`) preserves them. Tensor is already right exact.
8. Clauses 1--2 of `det-sf-flat-model-generation` express every constructible sheaf as
finite extensions of `g_* j_! L`, with j open in its closure, g closed, and L locally
constant finite-dimensional. Short exact sequences give triangles by
`lem-weil-pbc-complex-ses-triangle`. The lower truncation triangles of
`lem-pc-derived-lower-truncation-step-triangle` then express bounded P by finitely many
shifts and extensions of these generators: start above the upper cohomological bound at
zero, and finish below the lower bound at P.
9. For locally constant finite-dimensional L, the slice restriction in
`lem-weil-pbc-ringed-internal-hom-exact-restriction` computes Hom(L,N) on a trivializing
cover as a finite sum of N. It has the same bounding interval; its cohomology is
`L^dual tensor H^r(N)`, whose finite constant models follow by intersecting the two covers.
10. Apply `lem-weil-stratum-ambient-hom` first to g with identity open factor, then to j
with identity closed factor. The ambient Hom of `g_* j_! L` into Q is
`Rg_* Rj_* RHom(L, j^* Rg^! Q)`. Open exceptional inverse image is j^*, by its adjunction
with exact j_!, and closed g_* is exact by
`lem-weil-pbc-condensed-open-closed-recollement`. Steps 4, 6, 9 and then 5 show that this
object is bounded constructible. The order open-then-closed is retained throughout.
11. The triangle and contravariant shift clauses of
`lem-weil-pbc-ringed-internal-hom-exact-restriction` propagate step 10 through the finite
construction of P in step 8. Step 3 closes each induction step. This proves both asserted
properties for the ambient Hom, without any bound on global Galois cohomology of k. -/
theorem finiteField_constantModel_internalHom
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (A : Type u) [Field A] [Finite A] [CharP A l]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (P Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (finiteFieldCondensedRing A) X)))
    (hP : constantModelBoundedConstructible (finiteFieldCondensedRing A) X P)
    (hQ : constantModelBoundedConstructible (finiteFieldCondensedRing A) X Q) :
    constantModelBoundedConstructible (finiteFieldCondensedRing A) X
      (((CondensedRing.derivedHom (finiteFieldCondensedRing A) X).obj (op P)).obj Q) := by
  sorry

end AlgebraicGeometry.ProEtale

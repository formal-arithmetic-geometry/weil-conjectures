/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData

import Sheaf.Paper.AdicStratifiedLocalModels
import Sheaf.Paper.AdicStratifiedDescent
import Sheaf.Paper.AdicConstructibleResidueTriangles
import Sheaf.CategoryTheory.LocallyDerivedCompleteTriangulated
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# Adic constructibility and stratified perfect models

Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect).

The coefficients are arbitrary complete Noetherian local rings. No finiteness of their
residue fields or perfectness of their quotient modules over the original ring is assumed.

## Main definitions

* `IsSfbAdicConstructible`: completeness and bounded constructible etale residue origin.
* `IsSfbStratifiedPerfect`: finite strata with pro-etale locally perfect coefficient models.
* `SfbAdicConstructibleCategory`: the full ambient subcategory of these objects.

## Main statements

* `adic_stratified_perfect`: equivalence, boundedness and triangulated closure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

private theorem sfb_complete_triangulated (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsSfbAdicComplete X I) ∧
      ObjectProperty.IsTriangulated (IsSfbAdicComplete X I) := by
  let B := adicLisseCompletedRing X I
  let R := (adicLisseForget X).obj B
  let F := proEtaleModuleToModel R
  let e := (proEtaleModuleModelEquivalence X R).symm
  have : F.IsEquivalence := e.isEquivalence_functor
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  let O := (sfbModelRings X).obj B
  let q := (sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op 0))
  let : HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _
  let : ∀ U : proEtaleSiteModel X,
      HasDerivedCategory (ConstantCompletion.Mod (O.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  have hp := locallyDerivedRingedIdealComplete_triangulated O
    (ConstantCompletion.kernelIdeal q).module (ConstantCompletion.kernelIdeal q).inclusion
  let P : ObjectProperty (ConstantCompletion.D O) := ConstantCompletion.IsComplete q
  have : P.IsClosedUnderIsomorphisms := hp.1
  have : P.IsTriangulated := hp.2
  let : HasDerivedCategory (SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj R)) :=
    HasDerivedCategory.standard _
  let D : DerivedCategory (proEtaleRingModules X B) ⥤ ConstantCompletion.D O :=
    F.mapDerivedCategory
  have heq : IsSfbAdicComplete X I = P.inverseImage D := by
    funext K
    apply propext
    exact (P.prop_iff_of_iso
      ((D.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K))).symm
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

/-- Adic constructibility is equivalent to stratified perfect local models; these objects
are bounded and form a full triangulated subcategory.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect).

Proof, following the six steps of the node:
1. Restrict completed coefficients and the Koszul completion unit to immersions and slice
sites. Immersion inverse image and slice restriction preserve limits. Exact countable
products and the strict-tower Roos triangle compute the unit. Finite-stratum detection
therefore detects its zero cone, so completeness restricts and is detected on these covers.
2. For bounded etale residue complexes, geometric stalks commute with derived tensor.
Tensor of vector spaces over the residue field is exact; exact conservative stalks give
finite Tor amplitude in the same interval, without finite-coefficient assumptions.
3. Refine the finitely many cohomology stratifications by fibre-product immersions. Each
stratum is Noetherian. Comparison-pullback identifies its residue reduction, and the local
perfect-lifting lemma gives the required pro-etale perfect coefficient models.
4. Conversely finite projective terms are idempotent summands of finite completed free
modules, hence limits of power-torsion quotient sheaves. Torsion-limit completeness and the
constant/completed equivalence give local completeness; step 1 detects it globally.
Quasi-compact strata admit finitely many quasi-compact pieces of trivializing covers;
the finitely many perfect models give global cohomological bounds, also for empty X.
5. Completed reduction identifies each model with the constant complex P tensor_A A/I.
Its cohomology is locally constant finite dimensional. The constructible comparison theorem
for arbitrary discrete Noetherian coefficients descends it to a bounded etale complex.
Affine-local and global constructibility agree on Noetherian X: refine affine strata by
successive differences of a finite affine cover. Step 2 gives its finite Tor amplitude.
6. Completion units are natural maps of exact functors, so complete objects form a full
triangulated subcategory. Residue reduction is triangulated. Constructible cohomology is
closed under kernels, cokernels and extensions by the weak Serre lemma; the long exact
sequence of an ambient triangle gives two-out-of-three and boundedness. Zero, isomorphisms
and shifts preserve both conditions. No dimension or residue-invertibility bound is used.

Proof dependencies by step:
1. lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-proetale-weakly-etale-
localization, lem-weil-pbc-constant-completion-equivalence, lem-weil-proetale-countable-products-
exact, lem-weil-derived-countable-products-core, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-pbc-noetherian-stratum-detection.
2. prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-weil-
pbc-ringed-topoi-derived-tensor-pullback.
3. lem-weil-pbc-constructible-stratification-intersection, lem-weil-pbc-comparison-pullback, lem-
sfb-adic-residue-lisse-perfect-lift.
4. lem-weil-pbc-torsion-limit-sheaf-completeness, lem-weil-pbc-constant-completion-equivalence,
def-weil-pbc-proetale-site, lem-weil-pbc-noetherian-stratum-detection.
5. lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-noetherian-stratum-detection, sk-
thm-pe-constructible-comparison, lem-weil-pbc-constant-module-section-properties, def-pe-etale-
constructible-module, lem-sc-affine-noetherian-underlying-space, def-weil-constructible-subset.
6. lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-pur-derived-change-of-rings, sk-thm-pe-constructible-comparison, lem-sf-derived-homology-long-
exact, lem-sfb-discrete-noetherian-constructible-serre. -/
theorem adic_stratified_perfect (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A] :
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K ↔ IsSfbStratifiedPerfect X I K) ∧
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K → ∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    IsSfbAdicConstructible X I (0 : DerivedCategory
      (proEtaleRingModules X (adicLisseCompletedRing X I))) ∧
    (∀ (K L : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      Nonempty (K ≅ L) → IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I L) ∧
    (∀ (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) (n : ℤ),
      IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I (K⟦n⟧)) ∧
    ∀ T : Triangle (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      T ∈ distTriang _ →
        (IsSfbAdicConstructible X I T.obj₁ ∧ IsSfbAdicConstructible X I T.obj₂ →
          IsSfbAdicConstructible X I T.obj₃) ∧
        (IsSfbAdicConstructible X I T.obj₂ ∧ IsSfbAdicConstructible X I T.obj₃ →
          IsSfbAdicConstructible X I T.obj₁) ∧
        (IsSfbAdicConstructible X I T.obj₃ ∧ IsSfbAdicConstructible X I T.obj₁ →
          IsSfbAdicConstructible X I T.obj₂) := by
  have forward (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
      (hK : IsSfbAdicConstructible X I K) : IsSfbStratifiedPerfect X I K := by
    obtain ⟨s, hs, hlocal⟩ := sfb_adic_stratified_local_models X A I _hI K hK
    refine ⟨s, hs, ?_⟩
    intro α
    obtain ⟨V, hV, hmodels⟩ := hlocal α
    refine ⟨V, hV, ?_⟩
    intro U f hf
    obtain ⟨P, a, b, hge, hle, hterms, hiso⟩ := hmodels U f hf
    refine ⟨P, a, b, ?_, hge, hle, hterms, hiso⟩
    exact ⟨P, a, b, hge, hle, hterms, ⟨Iso.refl _⟩⟩
  have reverse (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
      (hK : IsSfbStratifiedPerfect X I K) : IsSfbAdicConstructible X I K := by
    obtain ⟨hc, hr, _⟩ := sfb_adic_stratified_descent X A I _hI K hK
    exact ⟨hc, hr⟩
  have hc := sfb_complete_triangulated X I
  have hr := sfb_adic_residue_triangulated X A I _hI
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsSfbAdicComplete X I) := hc.1
  have : ObjectProperty.IsTriangulated (IsSfbAdicComplete X I) := hc.2
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsSfbResidueConstructible X I) := hr.1
  have : ObjectProperty.IsTriangulated (IsSfbResidueConstructible X I) := hr.2
  let P : ObjectProperty
      (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :=
    IsSfbAdicComplete X I ⊓ IsSfbResidueConstructible X I
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have : P.IsTriangulated := inferInstance
  refine ⟨fun K ↦ ⟨forward K, reverse K⟩, ?_, P.prop_zero, ?_, ?_, ?_⟩
  · intro K hK
    exact (sfb_adic_stratified_descent X A I _hI K (forward K hK)).2.2
  · rintro K L ⟨e⟩ hK
    exact P.prop_of_iso e hK
  · intro K n hK
    exact P.le_shift n K hK
  · intro T hT
    exact ⟨fun h ↦ P.ext_of_isTriangulatedClosed₃ T hT h.1 h.2,
      fun h ↦ P.ext_of_isTriangulatedClosed₁ T hT h.1 h.2,
      fun h ↦ P.ext_of_isTriangulatedClosed₂ T hT h.2 h.1⟩

end AlgebraicGeometry.Scheme

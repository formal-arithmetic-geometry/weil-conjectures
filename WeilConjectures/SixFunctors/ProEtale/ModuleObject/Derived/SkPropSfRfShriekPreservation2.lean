/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Finite-coefficient preservation by the supplied exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-prop-sf-rf-shriek-preservation/_section.md and its proof
sk-prop-sf-rf-shriek-preservation.proof.md in the same directory
(blueprint: sk-prop-sf-rf-shriek-preservation).

The exceptional functor and adjunction below are selected from the actual existence
statement, not assumed. The compactification is the existing fixed choice over the field.
The small object properties are the recorded Dctf property pulled back along the full
localizing inclusions. No new coefficient, constructibility or localizing notion is defined.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)
  (A : Type) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
  (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

set_option maxHeartbeats 800000 in
-- Unfolding the supplied adjunction and the two coefficient lifts exceeds the default limit.
set_option synthInstance.maxSize 2048 in
/-- The exceptional inverse image supplied by `sk_prop_sf_existence` for a finite
commutative ell-primary coefficient ring preserves Dctf, and its own adjunction restricts.
The Hom equality specifies the restriction of that adjunction, including unit and counit.
Finite coefficient rings are represented in Type 0, as in the recorded admissibility
predicate, without restricting their isomorphism classes. Classical choices in the helper use
existence with counit-compatible uniqueness, which determines the adjoint up to the
natural isomorphisms relevant to preservation.

Source: latest blueprint, sk-prop-sf-rf-shriek-preservation, entire statement and proof;
standing finite or algebraically closed base-field convention in prose-P1-01
(blueprint: sk-prop-sf-rf-shriek-preservation).

Implementation: the closed-support, affine-projection and finite-cover argument below is
already proved by `localizingExceptionalAdjoint_preserves_finiteConstructible`, including
transport from ordinary finite coefficients to the recorded condensed localizing category.
Apply it at `ULift A` and transport through `finite_coefficientIso`; this accounts only for
coefficient universes. Apply it to the supplied adjoint, rather than assuming an adjoint as
input. Restrict that very adjunction by `Adjunction.restrictFullyFaithful`, and calculate
its Hom map from the original unit. Compact-support preservation is already contained in
`compactification_localizing` for the same chosen compactification.

Proof:
1. Specialize sk-prop-sf-existence to the finite coefficient A and the already chosen
   compactification. This supplies F = Rf_!, G = f^! and the adjunction used below.
   The standing field has finite ell-cohomological dimension; finite-type chart schemes
   are Noetherian. Inverse images preserve Dctf by the native pullback-and-line lemma.
2. For a closed immersion i with complement j, the formal-support triangle is
   i_* R Gamma_Z K -> K -> Rj_* j^* K. Open direct-image finiteness and the native
   support-fibre bound put R Gamma_Z K in Dctf, with Tor bound [a,b+e+1] for
   e >= cd_ell(j). Closed compact support is i_*. Fullness and uniqueness of right
   adjoints identify this support value with i^! K, compatibly with counits.
3. For p : affine d-space over Y -> Y, the projective-line adjunction and affine-local
   formula, restricted and iterated on the localizing categories, identify p^! with
   p^*(-)(d)[2d]. Pullback and tensor with the locally free Tate line preserve Dctf;
   the shift subtracts 2d from both endpoints of each interval.
4. Use the finite affine chart factorizations fs = vpi. Composition and open restriction
   of the supplied adjoints identify s^* f^! K with i^! p^! v^* K. Steps 2 and 3 give
   constructibility and finite cohomological and Tor intervals on each chart. Finite-cover
   gluing takes the minimum lower and maximum upper endpoints. Empty X gives zero.
5. Compactification coherence writes the supplied Rf_! as Rp_* D(j_!). The finite proper
   localizing lemma puts D(j_!) M in Dctf; proper finite-coefficient preservation puts
   Rp_* D(j_!) M in Dctf. Both functors therefore lift to the full Dctf subcategories.
   Restrict the supplied Hom bijections and their inverses through the full inclusions.
   Their naturality and triangle identities are inherited; the displayed equality is
   the equality with the original Hom bijection, not merely existence of an adjunction.
-/
theorem sk_prop_sf_rf_shriek_preservation :
    ∃ (hF : ∀ M : (localizingDctfProperty
        (Profinite.continuousMapRingObj.{u} A) X).FullSubcategory,
        localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) Y
          ((finiteSuppliedLowerShriek ell k hk A hA f).obj M.obj))
      (hG : ∀ K : (localizingDctfProperty
        (Profinite.continuousMapRingObj.{u} A) Y).FullSubcategory,
        localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) X
          ((finiteSuppliedUpperShriek ell k hk A hA f).obj K.obj)),
      ∃ adjSmall :
        (localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) Y).lift
          ((localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) X).ι ⋙
            finiteSuppliedLowerShriek ell k hk A hA f) hF ⊣
        (localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) X).lift
          ((localizingDctfProperty (Profinite.continuousMapRingObj.{u} A) Y).ι ⋙
            finiteSuppliedUpperShriek ell k hk A hA f) hG,
        ∀ (M : (localizingDctfProperty
              (Profinite.continuousMapRingObj.{u} A) X).FullSubcategory)
          (K : (localizingDctfProperty
              (Profinite.continuousMapRingObj.{u} A) Y).FullSubcategory)
          (a : (finiteSuppliedLowerShriek ell k hk A hA f).obj M.obj ⟶ K.obj),
          (adjSmall.homEquiv M K (ObjectProperty.homMk a)).hom =
            (finiteSuppliedShriekAdjunction ell k hk A hA f).homEquiv M.obj K.obj a := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  let Λ := Profinite.continuousMapRingObj.{u} A
  let hΛ : IsLocalizingAdmissibleCoefficient ell Λ :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hA, ⟨Iso.refl _⟩⟩
  let c := AlgebraicGeometry.compactificationOverField k f
  let h := (sk_prop_sf_existence Λ ell k hk f hΛ c).choose
  let F := finiteSuppliedLowerShriek ell k hk A hA f
  let G := finiteSuppliedUpperShriek ell k hk A hA f
  let adj := finiteSuppliedShriekAdjunction ell k hk A hA f
  have hF (M : (localizingDctfProperty Λ X).FullSubcategory) :
      localizingDctfProperty Λ Y (F.obj M.obj) :=
    (compactification_localizing Λ ell k f c hΛ).2.2.2 M.obj.obj M.property
  have hG (K : (localizingDctfProperty Λ Y).FullSubcategory) :
      localizingDctfProperty Λ X (G.obj K.obj) := by
    refine preservation_coefficientIso Λ (finite_coefficientIso A) c h G adj ?_ K.obj K.property
    intro h' G' adj' N hN
    have hpow : ∃ r : ℕ, ((ell ^ r : ℕ) : ULift.{u + 1} (ULift.{u} A)) = 0 := by
      obtain ⟨r, hr⟩ := hA
      refine ⟨r, ?_⟩
      apply ULift.ext
      apply ULift.ext
      simpa using hr 1
    obtain ⟨_, hp, _⟩ := localizingExceptionalAdjoint_preserves_finiteConstructible
      ell k (ULift.{u} A) hpow f c h' G' adj'
    exact hp ⟨N, hN⟩
  let Ls := (localizingDctfProperty Λ Y).lift
    ((localizingDctfProperty Λ X).ι ⋙ F) hF
  let Rs := (localizingDctfProperty Λ X).lift
    ((localizingDctfProperty Λ Y).ι ⋙ G) hG
  let small : Ls ⊣ Rs := adj.restrictFullyFaithful
    (localizingDctfProperty Λ X).fullyFaithfulι
    (localizingDctfProperty Λ Y).fullyFaithfulι (Iso.refl _) (Iso.refl _)
  refine ⟨hF, hG, small, ?_⟩
  intro M K a
  dsimp only [small]
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
  change adj.unit.app M.obj ≫ G.map (𝟙 _) ≫ G.map a ≫ 𝟙 _ = _
  rw [G.map_id]
  erw [Category.comp_id, Category.id_comp]
  exact (adj.homEquiv_unit M.obj K.obj a).symm

end AlgebraicGeometry.ProEtale.CondensedRing

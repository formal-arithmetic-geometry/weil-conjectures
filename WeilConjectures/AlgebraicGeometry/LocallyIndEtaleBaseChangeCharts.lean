/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Affine ind-etale charts after arbitrary base change

Source: Stacks Project, Tags 01JR, 01I4, 01JQ and 097J
(blueprint: lem-trf-locally-ind-etale-base-change-charts).

Affine open presentations are open immersions from spectra, so their images are the
chosen opens. The intermediate affine fibre product is retained, and its canonical
`pullbackSpecIso` gives the tensor presentation with both projection equations.
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

private theorem across_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : f.IndEtaleAcrossUniverses ↔ f.IndEtale := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  constructor
  · intro h
    exact hi.2 _ (ULift.ringEquiv.symm : A ≃+* ULift.{u} A)
      (hi.1 _ (ULift.ringEquiv : ULift.{u} B ≃+* B) h)
  · intro h
    exact hi.1 _ (ULift.ringEquiv.symm : B ≃+* ULift.{u} B)
      (hi.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A) h)

private theorem indEtale_right (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (h : RingHom.IndEtaleAcrossUniverses (algebraMap A B)) :
    RingHom.IndEtaleAcrossUniverses
      (Algebra.TensorProduct.includeRight.toRingHom : C →+* B ⊗[A] C) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := C)
  apply (across_iff _).mpr
  exact RingHom.IndEtale.isStableUnderBaseChange A B C (B ⊗[A] C)
    ((across_iff _).mp h)

/-- Local affine ind-etale charts, with their fixed presentations and both projections,
are preserved by an arbitrary base change of schemes.
Source: Stacks Project, Tags 01JR, 01I4, 01JQ and 097J
(blueprint: lem-trf-locally-ind-etale-base-change-charts).

Proof:
1. For the fixed charts, apply `lem-weil-pbc-open-fibre-product` (Tag 01JR).
   It identifies the affine-chart pullback with the intersection of the inverse images
   of the two open charts. The two membership assumptions put the chosen point there.
2. Use `def-weil-affine-spectrum` to identify the chart maps with their ring maps.
   Apply `lem-weil-pbc-fibre-product-affine-spectra` (Tags 01I4 and 01JQ): its
   `pullbackSpecIso` has projections induced by b ↦ b ⊗ 1 and c ↦ 1 ⊗ c.
   Composing the open-pullback identification with it gives the displayed projection
   equations. Uniqueness in `def-pc-fibre-product` makes the identification canonical
   relative to the fixed presentations.
3. Apply the base-change clause of `lem-weil-pbc-ind-etale-stability` (Tag 097J)
   to A → B and A → C. It makes exactly c ↦ 1 ⊗ c ind-etale, without a condition
   on A → C.
4. At any point of the full pullback, choose V and U using the local hypothesis.
   The pullback equation puts its second image in g⁻¹(U). By
   `lem-weil-pbc-affine-opens-basis` (Tag 01IT), choose an affine W inside this open.
   The preceding construction supplies the required affine ind-etale chart for the
   second projection. No affineness or separation of the ambient schemes is used.
-/
theorem locally_indEtale_base_change_charts
    {T S S' : Scheme.{u}} (u : T ⟶ S)
    (hu : ∀ x : T, ∃ (A B : CommRingCat.{u}) (f : A ⟶ B)
      (iV : Spec B ⟶ T) (iU : Spec A ⟶ S),
      IsOpenImmersion iV ∧ IsOpenImmersion iU ∧ x ∈ Set.range iV ∧
      Spec.map f ≫ iU = iV ≫ u ∧ RingHom.IndEtaleAcrossUniverses f.hom)
    (g : S' ⟶ S) :
    (∀ (x' : (pullback u g : Scheme.{u})) (A B C : Type u)
      [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
      (iV : Spec (.of B) ⟶ T) (iU : Spec (.of A) ⟶ S)
      (iW : Spec (.of C) ⟶ S')
      [IsOpenImmersion iV] [IsOpenImmersion iU] [IsOpenImmersion iW],
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ iU = iV ≫ u →
      Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ iU = iW ≫ g →
      pullback.fst u g x' ∈ iV.opensRange →
      pullback.snd u g x' ∈ iW.opensRange →
      RingHom.IndEtaleAcrossUniverses (algebraMap A B) →
      x' ∈ ((pullback.fst u g) ⁻¹ᵁ iV.opensRange ⊓
        (pullback.snd u g) ⁻¹ᵁ iW.opensRange) ∧
      (∃! e : (((pullback.fst u g) ⁻¹ᵁ iV.opensRange ⊓
          (pullback.snd u g) ⁻¹ᵁ iW.opensRange).toScheme ≅
          pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
            (Spec.map (CommRingCat.ofHom (algebraMap A C)))),
        (e ≪≫ pullbackSpecIso A B C).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)) ≫ iV =
          ((pullback.fst u g) ⁻¹ᵁ iV.opensRange ⊓
            (pullback.snd u g) ⁻¹ᵁ iW.opensRange).ι ≫ pullback.fst u g ∧
        (e ≪≫ pullbackSpecIso A B C).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : C →+* B ⊗[A] C)) ≫ iW =
          ((pullback.fst u g) ⁻¹ᵁ iV.opensRange ⊓
            (pullback.snd u g) ⁻¹ᵁ iW.opensRange).ι ≫ pullback.snd u g) ∧
      RingHom.IndEtaleAcrossUniverses
        (Algebra.TensorProduct.includeRight.toRingHom : C →+* B ⊗[A] C)) ∧
    (∀ x' : (pullback u g : Scheme.{u}), ∃ (C D : CommRingCat.{u}) (f : C ⟶ D)
      (iV' : Spec D ⟶ pullback u g) (iW : Spec C ⟶ S'),
      IsOpenImmersion iV' ∧ IsOpenImmersion iW ∧ x' ∈ Set.range iV' ∧
      Spec.map f ≫ iW = iV' ≫ pullback.snd u g ∧
      RingHom.IndEtaleAcrossUniverses f.hom) := by
  classical
  constructor
  · intro x' A B C _ _ _ _ _ iV iU iW _ _ _ hV hW hxV hxW hind
    let a := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let b := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let m := pullback.map a b u g iV iW iU hV hW
    let O := (pullback.fst u g) ⁻¹ᵁ iV.opensRange ⊓
      (pullback.snd u g) ⁻¹ᵁ iW.opensRange
    have hr : Set.range O.ι = Set.range m := by
      rw [Scheme.Opens.range_ι]
      exact (Scheme.Pullback.range_map (f := a) (g := b) u g iV iW iU hV hW).symm
    let e : O.toScheme ≅ pullback a b := IsOpenImmersion.isoOfRangeEq O.ι m hr
    have he : e.hom ≫ m = O.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hj : (pullbackSpecIso A B C).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : C →+* B ⊗[A] C)) ≫ iW =
        pullback.snd a b ≫ iW := by
      exact pullbackSpecIso_hom_snd_assoc A B C iW
    have hfst : e.hom ≫ pullback.fst a b ≫ iV = O.ι ≫ pullback.fst u g := by
      rw [← he]
      simp [m, Category.assoc]
    have hsnd : e.hom ≫ pullback.snd a b ≫ iW = O.ι ≫ pullback.snd u g := by
      rw [← he]
      simp [m, Category.assoc]
    refine ⟨⟨hxV, hxW⟩, ⟨e, ?_, ?_⟩, indEtale_right A B C hind⟩
    · simpa only [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst_assoc,
        hj] using And.intro hfst hsnd
    · intro e' he'
      apply Iso.ext
      apply pullback.hom_ext
      · apply (cancel_mono iV).mp
        simpa only [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst_assoc]
          using he'.1.trans hfst.symm
      · apply (cancel_mono iW).mp
        simpa only [Iso.trans_hom, Category.assoc, hj]
          using he'.2.trans hsnd.symm
  · intro x'
    obtain ⟨A, B, f, iV, iU, hV, hU, hxV, hf, hind⟩ := hu (pullback.fst u g x')
    let := hV
    let := hU
    have hxU : pullback.snd u g x' ∈ g ⁻¹ᵁ iU.opensRange := by
      obtain ⟨v, hv⟩ := hxV
      refine ⟨Spec.map f v, ?_⟩
      calc
        iU (Spec.map f v) = u (iV v) := congrArg (fun k ↦ k v) hf
        _ = u (pullback.fst u g x') := congrArg u hv
        _ = g (pullback.snd u g x') :=
          congrArg (fun k ↦ k x') (pullback.condition (f := u) (g := g))
    obtain ⟨C, iW, hW, hxW, hWU⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset hxU
    let := hW
    have hw : Set.range (iW ≫ g) ⊆ Set.range iU := by
      rintro _ ⟨w, rfl⟩
      exact hWU ⟨w, rfl⟩
    let b := IsOpenImmersion.lift iU (iW ≫ g) hw
    let c : A ⟶ C := Spec.preimage b
    have hc : Spec.map c ≫ iU = iW ≫ g := by
      rw [Spec.map_preimage]
      exact IsOpenImmersion.lift_fac _ _ _
    let : Algebra A B := f.hom.toAlgebra
    let : Algebra A C := c.hom.toAlgebra
    let m := pullback.map (Spec.map f) (Spec.map c) u g iV iW iU hf hc
    let j := pullbackSpecIso A B C
    let iV' : Spec (.of (B ⊗[A] C)) ⟶ pullback u g := j.inv ≫ m
    have hm : x' ∈ Set.range m := by
      rw [Scheme.Pullback.range_map (f := Spec.map f) (g := Spec.map c)
        u g iV iW iU hf hc]
      exact ⟨hxV, hxW⟩
    have hx : x' ∈ Set.range iV' := by
      change x' ∈ iV'.opensRange
      rw [Scheme.Hom.opensRange_comp_of_isIso]
      exact hm
    refine ⟨C, .of (B ⊗[A] C),
      CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom,
      iV', iW, inferInstance, hW, hx, ?_, ?_⟩
    · change Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : C →+* B ⊗[A] C)) ≫ iW =
        j.inv ≫ m ≫ pullback.snd u g
      have hms : m ≫ pullback.snd u g =
          pullback.snd (Spec.map f) (Spec.map c) ≫ iW := by
        simp [m, pullback.map]
      rw [hms]
      exact (pullbackSpecIso_inv_snd_assoc A B C iW).symm
    · exact indEtale_right A B C hind

end AlgebraicGeometry

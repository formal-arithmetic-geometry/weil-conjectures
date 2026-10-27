/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Coordinate identities for an affine groupoid

Source: Stacks Project, Groupoids, Tags 03C8 (`lemma-basis`), 02YE (`lemma-diagram`),
and 0231 (`definition-groupoid`); Schemes, Tag 01I4
(blueprint: lem-a1-affine-groupoid-coordinate-identities).

The tensor product below uses two separately specified algebra structures on the same ring.
Its ring operations and inclusions are exactly Mathlib's tensor-product constructions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coordinate ring `B ⊗[A] B`, using `σ` on the first factor and `τ` on the second.
Source: Stacks Project, Tag 03C8, first diagram of the proof of `lemma-basis`
(blueprint: lem-a1-affine-groupoid-coordinate-identities). Both module structures and the
standard tensor-product commutative-ring structure are supplied explicitly. -/
def affineGroupoidTensorRing {A B : CommRingCat.{u}} (σ τ : A ⟶ B) : CommRingCat.{u} :=
  @CommRingCat.of
    (@TensorProduct A _ B B _ _ σ.hom.toAlgebra.toModule τ.hom.toAlgebra.toModule)
    (@Algebra.TensorProduct.instCommRing A B B _ _ σ.hom.toAlgebra _ τ.hom.toAlgebra)

/-- The first tensor inclusion `p₀(b) = b ⊗ 1` for the specified source/target structures.
Source: Stacks Project, Tag 03C8, notation preceding the first diagram of `lemma-basis`
(blueprint: lem-a1-affine-groupoid-coordinate-identities). -/
def affineGroupoidTensorLeft {A B : CommRingCat.{u}} (σ τ : A ⟶ B) :
    B ⟶ affineGroupoidTensorRing σ τ :=
  CommRingCat.ofHom
    (@Algebra.TensorProduct.includeLeftRingHom A B B _ _ σ.hom.toAlgebra _ τ.hom.toAlgebra)

/-- The second tensor inclusion `p₁(b) = 1 ⊗ b` for the specified source/target structures.
Source: Stacks Project, Tag 03C8, notation preceding the first diagram of `lemma-basis`
(blueprint: lem-a1-affine-groupoid-coordinate-identities). -/
def affineGroupoidTensorRight {A B : CommRingCat.{u}} (σ τ : A ⟶ B) :
    B ⟶ affineGroupoidTensorRing σ τ :=
  CommRingCat.ofHom
    (@AlgHom.toRingHom A B (affineGroupoidTensorRing σ τ) _ _ _ τ.hom.toAlgebra
      (@Algebra.TensorProduct.instAlgebra A B B _ _ σ.hom.toAlgebra _ τ.hom.toAlgebra)
      (@Algebra.TensorProduct.includeRight A B B _ _ σ.hom.toAlgebra _ τ.hom.toAlgebra))

/-- The coordinate identities, injectivity and invariant subring of an affine groupoid.
Source: Stacks Project, Tags 03C8, 02YE and 0231
(blueprint: lem-a1-affine-groupoid-coordinate-identities).
Here `Spec.preimage` gives the coordinate homomorphism; for the displayed isomorphism `F`,
`Spec.preimage (F.inv ≫ c)` is the composition coordinate map `Δ`. The invariant subring is
Mathlib's `RingHom.eqLocus`, whose carrier is exactly `{a | σ a = τ a}`.

Proof plan (the four steps of the DAG node):
1. Apply `pullbackSpecIso` from [lem-weil-pbc-fibre-product-affine-spectra] to the two
   copies of `B`, with algebra structures `σ = s♯` and `τ = t♯`. Transport its source
   along `Spec.map_preimage` to obtain `F`. The projection formulas give the two displayed
   equations for `F.inv`. The tensor balancing relation, or the algebra-homomorphism
   property of the inclusions in [lem-weil-pbc-algebra-tensor-pushout-universal-property],
   gives `p₀.comp σ = p₁.comp τ`.
2. The identity laws from [def-a1-groupoid-scheme] say `e ≫ s = 𝟙` and `e ≫ t = 𝟙`.
   Contravariant functoriality from [def-weil-affine-spectrum] gives `εσ = ετ = id`.
   Apply `ε` to any equality of source images or target images to prove injectivity.
3. The same groupoid definition gives `c ≫ s = pullback.snd s t ≫ s` and
   `c ≫ t = pullback.fst s t ≫ t`. Precompose with `F.inv`, use the projection
   formulas, and apply contravariant functoriality to obtain `Δσ = p₁σ` and `Δτ = p₀τ`.
4. The equalizer carrier contains `0` and `1` and is closed under subtraction and
   multiplication because `σ` and `τ` are ring homomorphisms. This is precisely
   `RingHom.eqLocus σ τ`. Its defining equality gives equality of the restricted maps. -/
theorem affineGroupoid_coordinate_identities (A B : CommRingCat.{u})
    (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback s t ⟶ Spec B) (_hG : IsGroupoidScheme s t e i c) :
    (Spec.preimage e).hom.comp (Spec.preimage s).hom = RingHom.id A ∧
    (Spec.preimage e).hom.comp (Spec.preimage t).hom = RingHom.id A ∧
    Function.Injective (Spec.preimage s).hom ∧
    Function.Injective (Spec.preimage t).hom ∧
    (Spec.preimage s).hom.domRestrict
        (RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom) =
      (Spec.preimage t).hom.domRestrict
        (RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom) ∧
    ∃ F : pullback s t ≅
        Spec (affineGroupoidTensorRing (Spec.preimage s) (Spec.preimage t)),
      F.inv ≫ pullback.fst s t =
        Spec.map (affineGroupoidTensorLeft (Spec.preimage s) (Spec.preimage t)) ∧
      F.inv ≫ pullback.snd s t =
        Spec.map (affineGroupoidTensorRight (Spec.preimage s) (Spec.preimage t)) ∧
      (affineGroupoidTensorLeft (Spec.preimage s) (Spec.preimage t)).hom.comp
          (Spec.preimage s).hom =
        (affineGroupoidTensorRight (Spec.preimage s) (Spec.preimage t)).hom.comp
          (Spec.preimage t).hom ∧
      (Spec.preimage (F.inv ≫ c)).hom.comp (Spec.preimage s).hom =
        (affineGroupoidTensorRight (Spec.preimage s) (Spec.preimage t)).hom.comp
          (Spec.preimage s).hom ∧
      (Spec.preimage (F.inv ≫ c)).hom.comp (Spec.preimage t).hom =
        (affineGroupoidTensorLeft (Spec.preimage s) (Spec.preimage t)).hom.comp
          (Spec.preimage t).hom := by
  have hs : Spec.preimage s ≫ Spec.preimage e = 𝟙 A := by
    rw [← Spec.preimage_comp, _hG.identity_source, Spec.preimage_id]
  have ht : Spec.preimage t ≫ Spec.preimage e = 𝟙 A := by
    rw [← Spec.preimage_comp, _hG.identity_target, Spec.preimage_id]
  have hs' : (Spec.preimage e).hom.comp (Spec.preimage s).hom = RingHom.id A :=
    congrArg CommRingCat.Hom.hom hs
  have ht' : (Spec.preimage e).hom.comp (Spec.preimage t).hom = RingHom.id A :=
    congrArg CommRingCat.Hom.hom ht
  refine ⟨hs', ht', ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h' := congrArg (Spec.preimage e).hom h
    simpa only [← RingHom.comp_apply, hs', RingHom.id_apply] using h'
  · intro a b h
    have h' := congrArg (Spec.preimage e).hom h
    simpa only [← RingHom.comp_apply, ht', RingHom.id_apply] using h'
  · ext a
    exact a.property
  · let σ := Spec.preimage s
    let τ := Spec.preimage t
    let E := @pullbackSpecIso A B B _ _ _ σ.hom.toAlgebra τ.hom.toAlgebra
    let F : pullback s t ≅ Spec (affineGroupoidTensorRing σ τ) :=
      pullback.congrHom (Spec.map_preimage s).symm (Spec.map_preimage t).symm ≪≫ E
    have hfst : F.inv ≫ pullback.fst s t = Spec.map (affineGroupoidTensorLeft σ τ) := by
      dsimp only [F, Iso.trans_inv]
      rw [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]
      exact @pullbackSpecIso_inv_fst A B B _ _ _ σ.hom.toAlgebra τ.hom.toAlgebra
    have hsnd : F.inv ≫ pullback.snd s t = Spec.map (affineGroupoidTensorRight σ τ) := by
      dsimp only [F, Iso.trans_inv]
      rw [Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
      exact @pullbackSpecIso_inv_snd A B B _ _ _ σ.hom.toAlgebra τ.hom.toAlgebra
    refine ⟨F, hfst, hsnd, ?_, ?_, ?_⟩
    · have h : Spec.preimage s ≫ affineGroupoidTensorLeft σ τ =
          Spec.preimage t ≫ affineGroupoidTensorRight σ τ := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
          ← hfst, ← hsnd, Category.assoc, Category.assoc, pullback.condition]
      exact congrArg CommRingCat.Hom.hom h
    · have h : (F.inv ≫ c) ≫ s = Spec.map (affineGroupoidTensorRight σ τ) ≫ s := by
        rw [Category.assoc, _hG.composition_source, ← Category.assoc, hsnd]
      have h' := congrArg Spec.preimage h
      simp only [Spec.preimage_comp, Spec.preimage_map] at h'
      exact congrArg CommRingCat.Hom.hom h'
    · have h : (F.inv ≫ c) ≫ t = Spec.map (affineGroupoidTensorLeft σ τ) ≫ t := by
        rw [Category.assoc, _hG.composition_target, ← Category.assoc, hfst]
      have h' := congrArg Spec.preimage h
      simp only [Spec.preimage_comp, Spec.preimage_map] at h'
      exact congrArg CommRingCat.Hom.hom h'

end AlgebraicGeometry

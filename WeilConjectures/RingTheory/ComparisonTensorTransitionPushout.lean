/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.IsTensorProduct


/-! # A step of finite-stage tensor comparison

Given a directed system `F` of rings over `F.obj i₀`, a map `φ₀ : B₀ →ₐ C₀` and a natural
transformation `α : D ⟶ E` identified with the canonical comparison
`(F_j ⊗ B₀) ⊗_P Q ⟶ F_j ⊗ C₀`, every transition square of `α` is a pushout of commutative rings.

## Implementation details

For a transition `j ⟶ k`, cancellation of iterated tensor products makes the scalar-extension
squares for `B₀` and `C₀` pushouts, and cancelling one against the other shows that
`B_j, C_j, B_k, C_k` is a pushout (the private lemma `canonical_tensor_comparison_pushout`). A
cocone is then descended through the algebra pushout universal property, and uniqueness follows
by tensor induction. No invertibility of `α`, nontriviality or flatness is assumed.

## References

* [Stacks, Tag 02JO]
* [Stacks, Tag 00DD]
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
universe v w x y
namespace RingHom

private theorem canonical_tensor_comparison_pushout
    {R S T A B : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R T]
    [Algebra R A] [Algebra R B] (t : S →ₐ[R] T) (f : A →ₐ[R] B) :
    let D₀ := S ⊗[R] A
    let E₀ := S ⊗[R] B
    let D₁ := T ⊗[R] A
    let E₁ := T ⊗[R] B
    let d₀ := (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
    let d₁ := (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
    let mD := (Algebra.TensorProduct.map t (AlgHom.id R A)).toRingHom
    let mE := (Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom
    let : Algebra D₀ E₀ := d₀.toAlgebra
    let : Algebra D₀ D₁ := mD.toAlgebra
    let : Algebra E₀ E₁ := mE.toAlgebra
    let : Algebra D₁ E₁ := d₁.toAlgebra
    let : Algebra D₀ E₁ := (mE.comp d₀).toAlgebra
    let : IsScalarTower D₀ E₀ E₁ := .of_algebraMap_eq fun _ ↦ rfl
    let : IsScalarTower D₀ D₁ E₁ := .of_algebraMap_eq fun a ↦ by
      change mE (d₀ a) = d₁ (mD a)
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
      | tmul s a => rfl
    Algebra.IsPushout D₀ E₀ D₁ E₁ := by
  dsimp only
  let D₀ := S ⊗[R] A
  let E₀ := S ⊗[R] B
  let D₁ := T ⊗[R] A
  let E₁ := T ⊗[R] B
  let d₀ : D₀ →+* E₀ := (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
  let d₁ : D₁ →+* E₁ := (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
  let mD : D₀ →+* D₁ := (Algebra.TensorProduct.map t (AlgHom.id R A)).toRingHom
  let mE : E₀ →+* E₁ := (Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom
  let : Algebra D₀ E₀ := d₀.toAlgebra
  let : Algebra D₀ D₁ := mD.toAlgebra
  let : Algebra E₀ E₁ := mE.toAlgebra
  let : Algebra D₁ E₁ := d₁.toAlgebra
  let : Algebra D₀ E₁ := (mE.comp d₀).toAlgebra
  have square : d₁.comp mD = mE.comp d₀ := by
    apply RingHom.ext
    intro a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s a => rfl
  let : IsScalarTower D₀ E₀ E₁ := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower D₀ D₁ E₁ := .of_algebraMap_eq fun a ↦
    (DFunLike.congr_fun square a).symm
  let : Algebra S T := t.toRingHom.toAlgebra
  let : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ (t.commutes r).symm
  let : Algebra S D₁ := Algebra.TensorProduct.leftAlgebra
  let : Algebra S E₁ := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower S T D₁ := inferInstance
  let : IsScalarTower S T E₁ := inferInstance
  let : IsScalarTower S D₀ D₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : A) =
      Algebra.TensorProduct.map t (AlgHom.id R A) (s ⊗ₜ[R] (1 : A))
    simp
  let : IsScalarTower S E₀ E₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map t (AlgHom.id R B) (s ⊗ₜ[R] (1 : B))
    simp
  have HD : Algebra.IsPushout S T D₀ D₁ := by
    let : Algebra D₀ (T ⊗[S] D₀) := Algebra.TensorProduct.rightAlgebra
    apply Algebra.IsPushout.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R S T T A)
    apply RingHom.ext
    intro a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s a =>
      change (Algebra.TensorProduct.cancelBaseChange R S T T A)
        (1 ⊗ₜ[S] (s ⊗ₜ[R] a)) = t s ⊗ₜ[R] a
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have HE : Algebra.IsPushout S T E₀ E₁ := by
    let : Algebra E₀ (T ⊗[S] E₀) := Algebra.TensorProduct.rightAlgebra
    apply Algebra.IsPushout.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R S T T B)
    apply RingHom.ext
    intro a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s b =>
      change (Algebra.TensorProduct.cancelBaseChange R S T T B)
        (1 ⊗ₜ[S] (s ⊗ₜ[R] b)) = t s ⊗ₜ[R] b
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let : Algebra.IsPushout S D₀ T D₁ := HD.symm
  let : IsScalarTower S D₀ E₀ := .of_algebraMap_eq fun s ↦ by
    change s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map (AlgHom.id S S) f (s ⊗ₜ[R] (1 : A))
    simp
  let : IsScalarTower S D₁ E₁ := .of_algebraMap_eq fun s ↦ by
    change t s ⊗ₜ[R] (1 : B) =
      Algebra.TensorProduct.map (AlgHom.id T T) f (t s ⊗ₜ[R] (1 : A))
    simp
  exact (Algebra.IsPushout.comp_iff S D₀ (T := E₀) T D₁).mp HE.symm



/-- Let `α : D ⟶ E` be a natural transformation of functors on `{j // i ≤ j}`, with
`D_j ≅ (F_j ⊗ B₀) ⊗_P Q` and `E_j ≅ F_j ⊗ C₀` compatibly with the transitions, such that `α_j`
restricts to `F_j ⊗ φ₀` on `F_j ⊗ B₀`. Then every naturality square of `α` is a pushout.
-/
theorem comparison_tensor_transition_isPushout
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v})
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (i : I) (hi : i₀ ≤ i)
    (_aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)) :
      let J := {j : I // i ≤ j}
      ∀ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∀ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∀ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∀ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
                  (∀ {j k : J} (r : j ⟶ k),
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aPs k
                    ∃ β : (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
                        (↥(F.obj k.val) ⊗[F.obj i₀] B₀),
                      (let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
                        { (F.map (homOfLE (leOfHom r))).hom with
                          commutes' := fun s ↦
                            congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                              (F.map_comp (homOfLE (hi.trans j.property))
                                (homOfLE (leOfHom r))).symm };
                        β.toRingHom =
                          (Algebra.TensorProduct.map αjk
                            (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
                      (d k).toRingHom.comp (D.map r).hom =
                        (Algebra.TensorProduct.map β (AlgHom.id P Q)).toRingHom.comp
                          (d j).toRingHom) →
                  (∀ {j k : J} (r : j ⟶ k),
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
                    let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
                        { (F.map (homOfLE (leOfHom r))).hom with
                          commutes' := fun s ↦
                            congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                              (F.map_comp (homOfLE (hi.trans j.property))
                                (homOfLE (leOfHom r))).symm }
                    (c k).toRingHom.comp (E.map r).hom =
                      (Algebra.TensorProduct.map αjk (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
                        (c j).toRingHom) →
                  (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom) →
                  (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                    (E.map r) (α.app k)) := by
  classical
  dsimp only
  intro aPs D E α d c hDt hEt hcompat j k r
  let : Algebra (F.obj i₀) (F.obj j.val) :=
    (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let : Algebra (F.obj i₀) (F.obj k.val) :=
    (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
  let := aPs j
  let := aPs k
  let Bj := ↥(F.obj j.val) ⊗[F.obj i₀] B₀
  let Bk := ↥(F.obj k.val) ⊗[F.obj i₀] B₀
  let Cj := ↥(F.obj j.val) ⊗[F.obj i₀] C₀
  let Ck := ↥(F.obj k.val) ⊗[F.obj i₀] C₀
  let t : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
    { (F.map (homOfLE (leOfHom r))).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
        (F.map_comp (homOfLE (hi.trans j.property)) (homOfLE (leOfHom r))).symm }
  let b : Bj →+* Bk :=
    (Algebra.TensorProduct.map t (AlgHom.id (F.obj i₀) B₀)).toRingHom
  let e : Cj →+* Ck :=
    (Algebra.TensorProduct.map t (AlgHom.id (F.obj i₀) C₀)).toRingHom
  let φj : Bj →+* Cj :=
    (Algebra.TensorProduct.map (AlgHom.id (F.obj j.val) (F.obj j.val)) φ₀).toRingHom
  let φk : Bk →+* Ck :=
    (Algebra.TensorProduct.map (AlgHom.id (F.obj k.val) (F.obj k.val)) φ₀).toRingHom
  let : Algebra Bj Cj := φj.toAlgebra
  let : Algebra Bj Bk := b.toAlgebra
  let : Algebra Cj Ck := e.toAlgebra
  let : Algebra Bk Ck := φk.toAlgebra
  let : Algebra Bj Ck := (e.comp φj).toAlgebra
  let : IsScalarTower Bj Cj Ck := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower Bj Bk Ck := .of_algebraMap_eq fun z ↦ by
    change e (φj z) = φk (b z)
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s a => rfl
  let : Algebra.IsPushout Bj Cj Bk Ck := canonical_tensor_comparison_pushout t φ₀
  obtain ⟨β, hβ, hd⟩ := hDt r
  have he := hEt r
  have hcj (z : Bj) : c j ((α.app j).hom ((d j).symm (z ⊗ₜ[P] 1))) = φj z :=
    DFunLike.congr_fun (hcompat j) z
  have hck (z : Bk) : c k ((α.app k).hom ((d k).symm (z ⊗ₜ[P] 1))) = φk z :=
    DFunLike.congr_fun (hcompat k) z
  have hD (z : Bj ⊗[P] Q) :
      (D.map r).hom ((d j).symm z) =
        (d k).symm (Algebra.TensorProduct.map β (AlgHom.id P Q) z) := by
    apply (d k).injective
    have h := DFunLike.congr_fun hd ((d j).symm z)
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      RingEquiv.apply_symm_apply] using h
  have hE (z : Cj) : (E.map r).hom ((c j).symm z) = (c k).symm (e z) := by
    apply (c k).injective
    have h := DFunLike.congr_fun he ((c j).symm z)
    change c k ((E.map r).hom ((c j).symm z)) = e (c j ((c j).symm z)) at h
    rw [RingEquiv.apply_symm_apply] at h
    simpa only [RingEquiv.apply_symm_apply] using h
  have hβ' (z : Bj) : β z = b z := DFunLike.congr_fun hβ z
  refine { w := (α.naturality r).symm, isColimit' := ?_ }
  refine ⟨PushoutCocone.isColimitAux' _ (fun s ↦ ?_)⟩
  let f : Cj →+* s.pt := s.inl.hom.comp (c j).symm.toRingHom
  let g : Bk →+* s.pt :=
    s.inr.hom.comp ((d k).symm.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := Bk) (B := Q)))
  have hfg (z : Bj) : f (φj z) = g (b z) := by
    change s.inl.hom ((c j).symm (φj z)) = s.inr.hom ((d k).symm (b z ⊗ₜ[P] 1))
    rw [← hcj z, RingEquiv.symm_apply_apply]
    have hs := congrArg (fun f : D.obj j ⟶ s.pt ↦ f ((d j).symm (z ⊗ₜ[P] 1)))
      s.condition
    change s.inl.hom ((α.app j).hom ((d j).symm (z ⊗ₜ[P] 1))) =
      s.inr.hom ((D.map r).hom ((d j).symm (z ⊗ₜ[P] 1))) at hs
    rw [hD, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hβ'] at hs
    exact hs
  let : Algebra Bj s.pt := (g.comp b).toAlgebra
  let f' : Cj →ₐ[Bj] s.pt := { f with commutes' := hfg }
  let g' : Bk →ₐ[Bj] s.pt := { g with commutes' := fun _ ↦ rfl }
  let δ : Ck →+* s.pt :=
    (Algebra.pushoutDesc Ck f' g' (fun _ _ ↦ mul_comm _ _)).toRingHom
  have hδe (z : Cj) : δ (e z) = f z :=
    Algebra.pushoutDesc_left Ck f' g' (fun _ _ ↦ mul_comm _ _) z
  have hδφ (z : Bk) : δ (φk z) = g z :=
    Algebra.pushoutDesc_right Ck f' g' (fun _ _ ↦ mul_comm _ _) z
  let δ' : E.obj k ⟶ s.pt := CommRingCat.ofHom (δ.comp (c k).toRingHom)
  have hfacE : E.map r ≫ δ' = s.inl := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    have h := DFunLike.congr_fun he z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    change δ (c k ((E.map r).hom z)) = s.inl.hom z
    rw [h]
    change δ (e (c j z)) = _
    rw [hδe]
    change s.inl.hom ((c j).symm (c j z)) = _
    rw [RingEquiv.symm_apply_apply]
  have hfacQ (q : Q) :
      δ (c k ((α.app k).hom ((d k).symm (1 ⊗ₜ[P] q)))) =
        s.inr.hom ((d k).symm (1 ⊗ₜ[P] q)) := by
    have hn := congrArg
      (fun f : D.obj j ⟶ E.obj k ↦ f ((d j).symm (1 ⊗ₜ[P] q))) (α.naturality r)
    change (α.app k).hom ((D.map r).hom ((d j).symm (1 ⊗ₜ[P] q))) =
      (E.map r).hom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))) at hn
    rw [hD, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hn
    rw [hn]
    have hf := congrArg (fun f : E.obj j ⟶ s.pt ↦
      f ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q)))) hfacE
    change δ (c k ((E.map r).hom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))))) =
      s.inl.hom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))) at hf
    rw [hf]
    have hs := congrArg (fun f : D.obj j ⟶ s.pt ↦ f ((d j).symm (1 ⊗ₜ[P] q)))
      s.condition
    change s.inl.hom ((α.app j).hom ((d j).symm (1 ⊗ₜ[P] q))) =
      s.inr.hom ((D.map r).hom ((d j).symm (1 ⊗ₜ[P] q))) at hs
    rw [hD, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hs
    exact hs
  have hfacD : α.app k ≫ δ' = s.inr := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := (d k).symm.surjective z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    | tmul b q =>
      change δ (c k ((α.app k).hom ((d k).symm (b ⊗ₜ[P] q)))) =
        s.inr.hom ((d k).symm (b ⊗ₜ[P] q))
      have hmul : b ⊗ₜ[P] q = (b ⊗ₜ[P] 1) * (1 ⊗ₜ[P] q) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hmul, map_mul, map_mul, map_mul, map_mul, map_mul, hfacQ, hck, hδφ]
      rfl
  refine ⟨δ', hfacE, hfacD, ?_⟩
  intro h hE' hD'
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := (c k).symm.surjective z
  change h.hom ((c k).symm z) = δ (c k ((c k).symm z))
  rw [RingEquiv.apply_symm_apply]
  have heqE (a : Cj) : h.hom ((c k).symm (e a)) = δ (e a) := by
    rw [← hE a]
    have hh := congrArg (fun f : E.obj j ⟶ s.pt ↦ f ((c j).symm a)) hE'
    change h.hom ((E.map r).hom ((c j).symm a)) = s.inl.hom ((c j).symm a) at hh
    rw [hh, hδe]
    rfl
  have heqB (a : Bk) : h.hom ((c k).symm (φk a)) = δ (φk a) := by
    rw [← hck a, RingEquiv.symm_apply_apply]
    have h' := congrArg (fun f : D.obj k ⟶ s.pt ↦ f ((d k).symm (a ⊗ₜ[P] 1))) hD'
    change h.hom ((α.app k).hom ((d k).symm (a ⊗ₜ[P] 1))) =
      s.inr.hom ((d k).symm (a ⊗ₜ[P] 1)) at h'
    rw [h', hck a, hδφ]
    rfl
  obtain ⟨z, rfl⟩ := (Algebra.IsPushout.equiv Bj Cj Bk Ck).surjective z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul a b =>
    change h.hom ((c k).symm ((Algebra.IsPushout.equiv Bj Cj Bk Ck) (a ⊗ₜ[Bj] b))) =
      δ ((Algebra.IsPushout.equiv Bj Cj Bk Ck) (a ⊗ₜ[Bj] b))
    rw [Algebra.IsPushout.equiv_tmul]
    change h.hom ((c k).symm (e a * φk b)) = δ (e a * φk b)
    rw [map_mul, map_mul, map_mul, heqE, heqB]


end RingHom

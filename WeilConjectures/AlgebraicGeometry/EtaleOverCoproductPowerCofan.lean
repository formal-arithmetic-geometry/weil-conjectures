/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.AlgebraicGeometry.EtaleFibreProductCoproduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-! # The coproduct cofan of products over an étale object

## References

* Stacks Project, Tag 03OZ
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The canonical tuple-indexed maps exhibit a positive power of a coproduct over `U`
as a coproduct of the corresponding products of its summands (Stacks, Tag 03OZ). -/
theorem etale_over_coproduct_power_isColimit
    (X : Scheme.{u}) (U : X.Etale) (I : Type (u + 1)) [Finite I]
    (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (W : X.Etale) (g : W ⟶ U) (c : ∀ i : I, V i ⟶ W)
    (hc : IsColimit (Cofan.mk W.left (fun i ↦ (c i).left)))
    (hw : ∀ i : I, c i ≫ g = f i) (n : ℕ) :
    let A : I → Over U := fun i ↦ Over.mk (f i)
    let B : Fin (n + 1) → Over U := fun _ ↦ Over.mk g
    Nonempty (IsColimit (Cofan.mk (∏ᶜ B).left.left (fun t : Fin (n + 1) → I ↦
      ((Limits.Pi.map (fun r ↦ Over.homMk (c (t r)) (hw (t r))) :
        (∏ᶜ fun r ↦ A (t r)) ⟶ ∏ᶜ B).left).left))) := by
  classical
  dsimp only
  let F := (Etale.overEquiv U).functor ⋙ Etale.forget U.left
  let A : I → Over U := fun i ↦ Over.mk (f i)
  let A' : I → Over U.left := fun i ↦ Over.mk (f i).left
  let B : Over U := Over.mk g
  let cc (i : I) : A i ⟶ B := Over.homMk (c i) (hw i)
  let B₀ : Over U.left := Over.mk (Sigma.desc (fun i ↦ (f i).left))
  let k := Sigma.desc (fun i ↦ (c i).left)
  have hk : IsIso k :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk W.left (fun i ↦ (c i).left))).mp ⟨hc⟩
  have hk' : k ≫ g.left = Sigma.desc (fun i ↦ (f i).left) := by
    apply Sigma.hom_ext
    intro i
    simp only [k, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact congrArg (fun a ↦ a.left) (hw i)
  let b : B₀ ≅ F.obj B := Over.isoMk (asIso k) hk'
  obtain ⟨e, he, _⟩ :=
    AlgebraicGeometry.etale_fibre_product_coproduct U.left I
      (fun i ↦ (V i).left) (fun i ↦ (f i).left)
  let P := fun t : Fin (n + 1) → I ↦ ∏ᶜ fun r ↦ A' (t r)
  let Q := ∏ᶜ fun _ : Fin (n + 1) ↦ F.obj B
  let d' : ∀ t : Fin (n + 1) → I, P t ⟶ Q := fun t ↦
    Limits.Pi.map (fun r ↦ Over.homMk (c (t r)).left
      (congrArg (fun a ↦ a.left) (hw (t r))))
  let q : (∏ᶜ fun _ : Fin (n + 1) ↦ B₀) ≅ Q := Pi.mapIso (fun _ ↦ b)
  have hd' : Sigma.desc d' = (e n).hom ≫ q.hom := by
    apply Sigma.hom_ext
    intro t
    apply Pi.hom_ext
    intro r
    dsimp [q, d']
    simp only [Category.assoc, Sigma.ι_comp_desc, Pi.map_π]
    change _ = Sigma.ι P t ≫ (e n).hom ≫ Limits.Pi.map (fun _ ↦ b.hom) ≫ _
    rw [Pi.map_π]
    have h := congrArg (fun z ↦ z ≫ b.hom) (he n t r)
    simp only [Category.assoc] at h
    rw [h]
    congr 1
    apply Over.OverMorphism.ext
    exact (Sigma.ι_comp_desc (fun i ↦ (c i).left) (t r)).symm
  have hi : IsIso (Sigma.desc d') := by rw [hd']; infer_instance
  have hcol : IsColimit (Cofan.mk Q d') :=
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hi).some
  let p (t : Fin (n + 1) → I) : F.obj (∏ᶜ fun r ↦ A (t r)) ≅ P t :=
    asIso (piComparison F (fun r ↦ A (t r)))
  let q' : F.obj (∏ᶜ fun _ : Fin (n + 1) ↦ B) ≅ Q :=
    asIso (piComparison F (fun _ : Fin (n + 1) ↦ B))
  let d : ∀ t : Fin (n + 1) → I,
      F.obj (∏ᶜ fun r ↦ A (t r)) ⟶ F.obj (∏ᶜ fun _ : Fin (n + 1) ↦ B) :=
    fun t ↦ F.map (Limits.Pi.map (fun r ↦ cc (t r)))
  have hd (t) : d t ≫ q'.hom = (p t).hom ≫ d' t := by
    apply Pi.hom_ext
    intro r
    dsimp [d, p, q']
    simp only [Category.assoc, piComparison_comp_π, ← F.map_comp]
    dsimp [d']
    simp only [Pi.map_π]
    change F.map (Pi.π (fun r ↦ A (t r)) r ≫ cc (t r)) =
      (piComparison F (fun r ↦ A (t r))) ≫
        Pi.π (fun r ↦ F.obj (A (t r))) r ≫
          F.map (cc (t r))
    rw [← Category.assoc, piComparison_comp_π, ← F.map_comp]
  have hcol' : IsColimit (Cofan.mk (F.obj (∏ᶜ fun _ : Fin (n + 1) ↦ B)) d) := by
    let T (s : Cofan (fun t ↦ F.obj (∏ᶜ fun r ↦ A (t r)))) : Cofan P :=
      Cofan.mk s.pt (fun t ↦ (p t).inv ≫ s.inj t)
    refine Cofan.IsColimit.mk _ (fun s ↦ q'.hom ≫ hcol.desc (T s)) ?_ ?_
    · intro s t
      change d t ≫ q'.hom ≫ hcol.desc (T s) = s.inj t
      rw [← Category.assoc, hd, Category.assoc]
      have hf := hcol.fac (T s) (Discrete.mk t)
      change d' t ≫ hcol.desc (T s) = (p t).inv ≫ s.inj t at hf
      rw [hf]
      simp
    · intro s m hm
      have hh : q'.inv ≫ m = hcol.desc (T s) := by
        apply hcol.uniq (T s)
        intro t
        change d' t.as ≫ q'.inv ≫ m = (p t.as).inv ≫ s.inj t.as
        have hh := congrArg (fun z ↦ (p t.as).inv ≫ z ≫ q'.inv) (hd t.as)
        simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
          Category.comp_id] at hh
        rw [← Category.assoc, ← hh, Category.assoc]
        have hf := hm t.as
        change d t.as ≫ m = s.inj t.as at hf
        rw [hf]
      calc
        m = q'.hom ≫ (q'.inv ≫ m) := by simp
        _ = q'.hom ≫ hcol.desc (T s) := by rw [hh]
  have hh := Cofan.isColimitMapCoconeEquiv (Over.forget U.left) _ _
    (isColimitOfPreserves (Over.forget U.left) hcol')
  exact ⟨hh⟩

end AlgebraicGeometry.Scheme

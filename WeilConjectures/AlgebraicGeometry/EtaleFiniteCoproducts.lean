/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentAux

/-!
# Finite coproducts in the small étale site and base change

* a finite coproduct cofan in `X.Etale` is a coproduct cofan of the underlying schemes, and
  conversely;
* base change of schemes over `X` preserves finite coproduct cofans.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite coproduct cofan in `X.Etale` is a coproduct cofan of the underlying schemes. -/
noncomputable def Scheme.Etale.isColimitCofanLeft {X : Scheme.{u}} {ι : Type} [Finite ι]
    {Y : ι → X.Etale} {Z : X.Etale} (f : ∀ k, Y k ⟶ Z) (hs : IsColimit (Cofan.mk Z f)) :
    IsColimit (Cofan.mk Z.left fun k ↦ (f k).left) := by
  let Yl : ι → Scheme.{u} := fun k ↦ (Y k).left
  let p : ∀ k, Yl k ⟶ X := fun k ↦ (Y k).hom
  let W : X.Etale := MorphismProperty.Over.mk ⊤ (Sigma.desc p)
    (IsZariskiLocalAtSource.sigmaDesc fun k ↦ (Y k).prop)
  let ιW : ∀ k, Y k ⟶ W := fun k ↦
    MorphismProperty.Over.homMk (Sigma.ι Yl k) (Sigma.ι_desc p k)
  have hW : IsColimit (Cofan.mk W ιW) := Cofan.IsColimit.mk _
    (fun s ↦ MorphismProperty.Over.homMk (Sigma.desc fun k ↦ (s.inj k).left) (by
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      rw [Sigma.ι_desc_assoc]
      exact (MorphismProperty.Over.w (s.inj k)).trans (Sigma.ι_desc p k).symm))
    (fun s k ↦ MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ k))
    (fun s m hm ↦ MorphismProperty.Over.Hom.ext (Sigma.hom_ext _ _ fun k ↦
      (congrArg (fun φ ↦ φ.left) (hm k)).trans
        (Sigma.ι_desc (fun k ↦ (s.inj k).left) k).symm))
  let e := hs.coconePointUniqueUpToIso hW
  have he : ∀ k, (f k).left ≫ e.hom.left = Sigma.ι Yl k := fun k ↦
    congrArg (fun φ ↦ φ.left) (hs.comp_coconePointUniqueUpToIso_hom hW ⟨k⟩)
  refine IsColimit.ofIsoColimit (coproductIsCoproduct Yl) (Cofan.ext
    ((Scheme.Etale.forget X ⋙ Over.forget X).mapIso e).symm fun k ↦ ?_)
  change Sigma.ι Yl k ≫ e.inv.left = (f k).left
  rw [← he k, Category.assoc, ← MorphismProperty.Comma.comp_left, e.hom_inv_id]
  exact Category.comp_id _

/-- A cofan in `X.Etale` whose underlying cofan of schemes is a coproduct is a coproduct. -/
noncomputable def Scheme.Etale.isColimitOfCofanLeft {X : Scheme.{u}} {ι : Type*}
    {Y : ι → X.Etale} {Z : X.Etale} (f : ∀ k, Y k ⟶ Z)
    (hs : IsColimit (Cofan.mk Z.left fun k ↦ (f k).left)) : IsColimit (Cofan.mk Z f) :=
  Cofan.IsColimit.mk _
    (fun s ↦ MorphismProperty.Over.homMk
      (Cofan.IsColimit.desc hs fun k ↦ (s.inj k).left)
      (Cofan.IsColimit.hom_ext hs _ _ fun k ↦ by
        have h₁ : (f k).left ≫ Cofan.IsColimit.desc hs (fun k ↦ (s.inj k).left) =
            (s.inj k).left := Cofan.IsColimit.fac hs _ k
        change (f k).left ≫ _ ≫ _ = (f k).left ≫ Z.hom
        rw [reassoc_of% h₁, MorphismProperty.Over.w (s.inj k), MorphismProperty.Over.w (f k)]))
    (fun s k ↦ MorphismProperty.Over.Hom.ext (Cofan.IsColimit.fac hs _ k))
    (fun s m hm ↦ MorphismProperty.Over.Hom.ext (Cofan.IsColimit.hom_ext hs _ _ fun k ↦ by
      change (f k).left ≫ m.left = (f k).left ≫ Cofan.IsColimit.desc hs (fun k ↦ (s.inj k).left)
      rw [show (f k).left ≫ Cofan.IsColimit.desc hs (fun k ↦ (s.inj k).left) =
        (s.inj k).left from Cofan.IsColimit.fac hs _ k]
      exact congrArg (fun φ ↦ φ.left) (hm k)))

/-- Base change of schemes over `X` preserves finite coproduct cofans. -/
lemma Over.nonempty_isColimit_pullback_cofan_left {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type*}
    [Finite ι] {A : ι → Over X} {Z : Over X} (ℓ : ∀ k, A k ⟶ Z)
    (hs : IsColimit (Cofan.mk Z.left fun k ↦ (ℓ k).left)) :
    Nonempty (IsColimit (Cofan.mk ((Over.pullback g).obj Z).left
      fun k ↦ ((Over.pullback g).map (ℓ k)).left)) :=
  (FinitaryPreExtensive.isUniversal_finiteCoproducts hs).nonempty_isColimit_of_isPullback_left
    (fun k ↦ (A k).hom) Z.hom g (fun k ↦ pullback.snd _ _) (fun k ↦ pullback.fst _ _)
    (fun k ↦ (IsPullback.of_hasPullback (A k).hom g).flip)
    (IsPullback.of_hasPullback Z.hom g).flip _ (Iso.refl _) (fun k ↦ Over.w (ℓ k))
    (fun k ↦ by simp) (fun k ↦ by simp)

end AlgebraicGeometry

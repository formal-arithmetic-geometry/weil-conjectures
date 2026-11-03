/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.EqToHom

/-! # Multiplication of factorization trivializations

Source: the addition-of-exponents step of `prop-trf-scheme-galois-comparison`.
-/

@[expose] public section
set_option autoImplicit false
universe u v uC vC
open CategoryTheory
namespace CategoryTheory

section
variable {S : Type u} [Category.{v} S] {X : S}
  {C : Type uC} [Category.{vC} C]
  (P : End X → C ⥤ C)
  (c : ∀ f g : End X, P (f ≫ g) ≅ P g ⋙ P f)

private def expansion (f g t : End X) (e : t = f ≫ g) : P t ≅ P g ⋙ P f :=
  eqToIso (congrArg P e) ≪≫ c f g

private theorem expansion_coherence
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (f g h fg gh t : End X) (efg : fg = f ≫ g) (egh : gh = g ≫ h)
    (et : t = f ≫ gh) (et' : t = fg ≫ h) (K : C) :
    (expansion P c f gh t et).hom.app K ≫
        (P f).map ((expansion P c g h gh egh).hom.app K) =
      (expansion P c fg h t et').hom.app K ≫
        (expansion P c f g fg efg).hom.app ((P h).obj K) := by
  subst fg
  subst gh
  cases et
  simpa only [expansion, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc] using hc f g h K

private theorem expansion_refl (f g : End X) :
    expansion P c f g (f ≫ g) rfl = c f g := by
  simp only [expansion, eqToIso_refl, Iso.refl_trans]

private theorem interchange_expansion
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (g h k : End X) (w : h ≫ g = g ≫ h) (K : C) :
    (c g (h ≫ k)).hom.app K ≫ (P g).map ((c h k).hom.app K) ≫
        (c g h).inv.app ((P k).obj K) ≫
        (eqToIso (congrArg P w.symm)).hom.app ((P k).obj K) ≫
        (c h g).hom.app ((P k).obj K) =
      (expansion P c h (g ≫ k) (g ≫ h ≫ k)
        (by rw [← Category.assoc, ← w, Category.assoc])).hom.app K ≫
        (P h).map ((c g k).hom.app K) := by
  let t := g ≫ h ≫ k
  have et : t = (h ≫ g) ≫ k := by dsimp [t]; rw [← Category.assoc, w]
  have et' : t = h ≫ g ≫ k := by rw [et, Category.assoc]
  have h₁ := expansion_coherence P c hc g h k (h ≫ g) (h ≫ k) t
    w rfl rfl et K
  have h₂ := expansion_coherence P c hc h g k (h ≫ g) (g ≫ k) t
    rfl rfl et' et K
  dsimp only [t] at h₁ h₂
  simp only [expansion_refl] at h₁ h₂
  rw [reassoc_of% h₁]
  simp only [expansion, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    Category.assoc] at h₁ h₂ ⊢
  simp only [Iso.hom_inv_id_app_assoc, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simpa only [eqToHom_app] using h₂.symm

/-- Cancelling a natural, multiplicative trivialization in two commuting
factorizations is compatible with the canonical pullback composition maps.
Source: blueprint `prop-trf-scheme-galois-comparison`, proof paragraph 2
(blueprint: lem-trf-factorization-trivialization-multiplication).
Proof: expand both factorizations using the composition comparisons. Their
associativity identifies the two expansions of three consecutive factors. The
naturality square for the second trivialization moves it through the first
Galois pullback. Naturality of the first trivialization then moves it through
that square. Apply the addition law for the two trivializations, and cancel the
Galois composition comparison. All steps are equations of natural transformations,
so extensionality in the object proves the identity. -/
theorem factorizationTrivialization_multiplication
    (hc : ∀ (f g h : End X) (K : C),
      (c f (g ≫ h)).hom.app K ≫ (P f).map ((c g h).hom.app K) =
        (eqToIso (congrArg P (Category.assoc f g h).symm)).hom.app K ≫
          (c (f ≫ g) h).hom.app K ≫ (c f g).hom.app ((P h).obj K))
    (f g h k : End X) (w : h ≫ g = g ≫ h)
    (t : P f ≅ 𝟭 C) (s : P h ≅ 𝟭 C) (z : P (f ≫ h) ≅ 𝟭 C)
    (hz : ∀ K : C, z.hom.app K =
      (c f h).hom.app K ≫ t.hom.app ((P h).obj K) ≫ s.hom.app K)
    (hs : ∀ K : C,
      (c g h).inv.app K ≫ (eqToIso (congrArg P w.symm)).hom.app K ≫
          (c h g).hom.app K ≫ s.hom.app ((P g).obj K) =
        (P g).map (s.hom.app K)) :
    ∀ K : C,
      (eqToIso (congrArg P
        (show (f ≫ g) ≫ (h ≫ k) = (f ≫ h) ≫ (g ≫ k) by
          simp only [Category.assoc]; rw [← Category.assoc g h k, ← w,
            Category.assoc]))).hom.app K ≫
          (c (f ≫ h) (g ≫ k)).hom.app K ≫ z.hom.app ((P (g ≫ k)).obj K) =
        (c (f ≫ g) (h ≫ k)).hom.app K ≫
          (c f g).hom.app ((P (h ≫ k)).obj K) ≫
          t.hom.app ((P g).obj ((P (h ≫ k)).obj K)) ≫
          (P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)) ≫
          (c g k).inv.app K := by
  intro K
  let b := g ≫ h ≫ k
  let total := (f ≫ g) ≫ (h ≫ k)
  have eb : b = h ≫ g ≫ k := by
    dsimp [b]
    rw [← Category.assoc, ← w, Category.assoc]
  have et : total = f ≫ b := Category.assoc _ _ _
  have et' : total = (f ≫ h) ≫ (g ≫ k) := by
    rw [et, eb, ← Category.assoc]
  have h₁ := expansion_coherence P c hc f g (h ≫ k) (f ≫ g) b total
    rfl rfl et rfl K
  have h₂ := expansion_coherence P c hc f h (g ≫ k) (f ≫ h) b total
    rfl eb et et' K
  dsimp only [b, total] at h₁ h₂
  simp only [expansion_refl] at h₁ h₂
  have hswap := interchange_expansion P c hc g h k w K
  have hh : (c g (h ≫ k)).hom.app K ≫
      (P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)) =
    (expansion P c h (g ≫ k) b eb).hom.app K ≫
      (P h).map ((c g k).hom.app K) ≫ s.hom.app ((P g).obj ((P k).obj K)) := by
    rw [Functor.map_comp, ← hs ((P k).obj K)]
    simpa only [Category.assoc] using
      congrArg (· ≫ s.hom.app ((P g).obj ((P k).obj K))) hswap
  have nt := t.hom.naturality
    ((P g).map ((c h k).hom.app K ≫ s.hom.app ((P k).obj K)))
  have nt₁ := t.hom.naturality (s.hom.app ((P g).obj ((P k).obj K)))
  have nt₂ := t.hom.naturality ((P h).map ((c g k).hom.app K))
  have ns := s.hom.naturality ((c g k).hom.app K)
  simp only [Functor.id_map] at nt nt₁ nt₂ ns
  symm
  rw [← reassoc_of% nt, ← reassoc_of% h₁]
  rw [← Functor.map_comp_assoc, hh]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nt₁, reassoc_of% nt₂, reassoc_of% ns,
    Iso.hom_inv_id_app, Category.comp_id]
  rw [reassoc_of% h₂, ← hz]
  simp only [expansion, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

end
end CategoryTheory

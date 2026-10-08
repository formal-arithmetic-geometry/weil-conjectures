/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Torsion abelian étale sheaves

A sheaf of abelian groups is torsion (`CategoryTheory.Sheaf.IsTorsion`) if all its groups of
sections are torsion. On the small étale site of a scheme, where infinite disjoint unions of
étale `X`-schemes are again étale over `X`, this forces a uniform bound on the orders.

## Main statements

- `AlgebraicGeometry.Scheme.exists_nsmul_eq_zero_of_isTorsion`: a torsion étale sheaf is killed
  by a single positive integer.
- `AlgebraicGeometry.Etale.isTorsion_upperStar`: the pullback of a torsion étale sheaf along any
  morphism of schemes is torsion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- The sections of an abelian étale sheaf over an étale `X`-scheme with empty underlying
scheme form a subsingleton: the empty family covers it. -/
lemma subsingleton_obj_of_isEmpty (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (W : X.Etale) [IsEmpty W.left] : Subsingleton (F.obj.obj (op W)) := by
  have h := isSheafFor_ofArrows F (κ := PEmpty.{1}) (U := PEmpty.elim) (W := W) (fun a ↦ a.elim)
    (Set.eq_univ_of_forall fun x ↦ (IsEmpty.false x).elim)
  refine ⟨fun a b ↦ h.isSeparatedFor.ext fun Y f hf ↦ ?_⟩
  obtain ⟨i⟩ := hf
  exact i.elim

/-- **A torsion étale sheaf has bounded exponent.** If every section of the abelian étale sheaf
`F` on `X` is torsion, then a single `N > 0` kills all sections of `F`. Otherwise there are
sections `sₙ` over étale `X`-schemes `Uₙ` not killed by `(n + 1)!`; they glue to a section of `F`
over the disjoint union `∐ₙ Uₙ`, whose order `m` then kills `sₘ`, which divides `(m + 1)!`. -/
lemma exists_nsmul_eq_zero_of_isTorsion
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : F.IsTorsion) :
    ∃ N : ℕ, 0 < N ∧ ∀ (U : X.Etaleᵒᵖ) (s : F.obj.obj U), N • s = 0 := by
  by_contra! h
  choose U s hs using fun n : ℕ ↦ h (n + 1).factorial (Nat.factorial_pos _)
  let g : ℕ → Scheme.{u} := fun n ↦ (U n).unop.left
  have : IsZariskiLocalAtSource @AlgebraicGeometry.Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have : AlgebraicGeometry.Etale (Sigma.desc fun n ↦ (U n).unop.hom) :=
    IsZariskiLocalAtSource.sigmaDesc fun n ↦ (U n).unop.prop
  let W : X.Etale := Etale.mk (Sigma.desc fun n ↦ (U n).unop.hom)
  let ι : ∀ n, (U n).unop ⟶ W := fun n ↦
    MorphismProperty.Over.homMk (Sigma.ι g n) (Sigma.ι_desc _ n)
  have hcov : ⋃ n, Set.range (ι n).left = Set.univ := (sigmaOpenCover g).iUnion_range
  have hsh := (Presieve.isSheafFor_arrows_iff _ _).1 (isSheafFor_ofArrows F ι hcov)
  obtain ⟨t, ht, -⟩ := hsh s (by
    intro a b Z ga gb hab
    by_cases h : a = b
    · subst h
      have : Mono (ι a).left := inferInstanceAs (Mono (Sigma.ι g a))
      have : ga = gb := MorphismProperty.Over.Hom.ext
        ((cancel_mono (ι a).left).1 (congrArg (fun f ↦ f.left) hab))
      rw [this]
    · have hl : ga.left ≫ Sigma.ι g a = gb.left ≫ Sigma.ι g b :=
        congrArg (fun f ↦ f.left) hab
      have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne ⟨hl⟩ h
      have := subsingleton_obj_of_isEmpty F Z
      exact Subsingleton.elim (α := F.obj.obj (op Z)) _ _)
  obtain ⟨m, hm, hmt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hF (op W) t)
  refine hs m ?_
  obtain ⟨c, hc⟩ : m ∣ (m + 1).factorial := Nat.dvd_factorial hm (Nat.le_succ m)
  have h' : m • s m = 0 := by
    have := congrArg (F.obj.map (ι m).op).hom hmt
    rw [map_nsmul, map_zero] at this
    exact (congrArg (m • ·) (ht m)).symm.trans this
  rw [hc, mul_comm, mul_nsmul', h', smul_zero]

end Scheme

/-- An abelian étale sheaf all of whose sections are killed by `N > 0` is torsion. -/
lemma Scheme.isTorsion_of_nsmul_id_eq_zero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {N : ℕ} (hN : 0 < N)
    (h : N • 𝟙 F = 0) : F.IsTorsion := by
  intro U s
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, ?_⟩
  have h₂ := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app U) h
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h₂
  simpa using congrArg (fun g ↦ g.hom s) h₂

/-- The pullback `g^* F` of a torsion étale sheaf `F` along a morphism of schemes `g` is torsion.
Since sections over infinite disjoint unions are products, a torsion sheaf in the sense of
`CategoryTheory.Sheaf.IsTorsion` is killed by a single integer `N ≠ 0`
(`AlgebraicGeometry.Scheme.exists_nsmul_eq_zero_of_isTorsion`); then so is `g^* F`, as
`g^*` is additive. -/
theorem Etale.isTorsion_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : F.IsTorsion) :
    ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).IsTorsion := by
  obtain ⟨N, hN, h⟩ := Scheme.exists_nsmul_eq_zero_of_isTorsion hF
  refine Scheme.isTorsion_of_nsmul_id_eq_zero hN ?_
  have h₀ : N • 𝟙 F = 0 := by
    refine (sheafToPresheaf _ _).map_injective ?_
    ext U s
    rw [Functor.map_nsmul, NatTrans.app_nsmul]
    simpa using h U s
  rw [← (Etale.upperStar AddCommGrpCat.{u + 1} g).map_id, ← Functor.map_nsmul, h₀, Functor.map_zero]

end AlgebraicGeometry

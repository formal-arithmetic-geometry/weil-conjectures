/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.RationalizationDiagram
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Torsion sheaves of modules have vanishing rationalization

A sheaf of modules `F` whose underlying abelian sheaf is torsion
(`CategoryTheory.Sheaf.IsTorsion`) has zero rationalization: the colimit of the sequence
`F --1--> F --2--> F --3--> ⋯` (`CategoryTheory.Preadditive.rationalizationDiagram`) vanishes.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Preadditive

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]

/-- If the underlying abelian sheaf of a sheaf of modules `F` is torsion, then the colimit of
the rationalization diagram `F --1--> F --2--> F --3--> ⋯` of `F` is zero: a section `x` of `F`
is, locally, killed by some `N > 0`, and its image in the colimit at stage `k` is the image of
`(k + 1) ⋯ (k + N) • x` at stage `k + N`, which vanishes as `N` divides `(k + 1) ⋯ (k + N)`. -/
lemma IsTorsion.isZero_colimit_rationalizationDiagram {F : Sheaf J (ModuleCat.{w} R)}
    (hF : ((sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F).IsTorsion)
    [HasColimit (rationalizationDiagram F)] :
    IsZero (colimit (rationalizationDiagram F)) := by
  rw [isZero_colimit_rationalizationDiagram_iff]
  intro k
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ ?_)))
  obtain ⟨S, hS, hx⟩ := hF x
  refine (colimit (rationalizationDiagram F)).isSeparated _ S hS _ _ fun V f hf ↦ ?_
  obtain ⟨N, hN, hNx⟩ := (hx hf).exists_nsmul_eq_zero
  have hι := colimit_ι_rationalizationDiagram F k N
  have hdvd : N ∣ (k + 1).ascFactorial N :=
    (Nat.dvd_factorial hN le_rfl).trans (Nat.factorial_dvd_ascFactorial _ _)
  obtain ⟨m, hm⟩ := hdvd
  have hx0 : (N * m) • (F.obj.map f.op).hom x = 0 := by
    rw [mul_comm, mul_smul]
    exact (congr_arg (m • ·) hNx).trans (smul_zero _)
  have hnat := ConcreteCategory.congr_hom
    ((colimit.ι (rationalizationDiagram F) k).hom.naturality f.op) x
  have hnat' := ConcreteCategory.congr_hom
    ((0 : (rationalizationDiagram F).obj k ⟶ colimit (rationalizationDiagram F)).hom.naturality
      f.op) x
  refine (hnat.symm.trans ?_).trans hnat'
  rw [hι, hm]
  have hs : ((N * m) • colimit.ι (rationalizationDiagram F) (k + N)).hom.app (op V) =
      (N * m) • (colimit.ι (rationalizationDiagram F) (k + N)).hom.app (op V) := by
    rw [← NatTrans.app_nsmul]; rfl
  have h0 : (0 : (rationalizationDiagram F).obj k ⟶ colimit (rationalizationDiagram F)).hom.app
      (op V) = 0 := rfl
  rw [hs, h0, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  simp only [ModuleCat.hom_nsmul, LinearMap.smul_apply]
  rw [← map_nsmul]
  exact (congr_arg _ hx0).trans (map_zero _)

end CategoryTheory.Sheaf

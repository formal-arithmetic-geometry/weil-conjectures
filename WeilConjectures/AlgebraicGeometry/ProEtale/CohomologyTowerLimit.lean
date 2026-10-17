/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Cohomology of limits of towers of abelian pro-étale sheaves

The pro-étale topos is replete: for a tower `⋯ ⟶ F₁ ⟶ F₀` of epimorphisms of abelian sheaves on
`S_proét`, the Milnor sequence `0 ⟶ lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0` is exact and countable
products are exact (Bhatt–Scholze, §3.1 and Proposition 4.2.8). Hence if `Hᵠ(Fₙ) = 0` for
`q > N` and the transition maps are surjective on `H^N`, then `Hᵠ(lim Fₙ) = 0` for `q > N`.

The repleteness results of the repository are stated for sheaves of modules over a ring in
`Type (u + 1)`; we transport them to abelian sheaves along the equivalence between abelian
sheaves and sheaves of `ULift ℤ`-modules.

## Main statements

- `AlgebraicGeometry.Scheme.ProEt.epi_one_sub_of_epi`: `1 - t` is an epimorphism on the product
  of a tower of epimorphisms of abelian pro-étale sheaves.
- `AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isLimit_tower`: vanishing of the cohomology
  of the limit of a tower.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- Taking underlying abelian sheaves is an equivalence from pro-étale sheaves of
`ULift ℤ`-modules to abelian pro-étale sheaves. -/
noncomputable def sheafForget₂UliftIntEquivalence :
    Sheaf (topology S) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ≌
      Sheaf (topology S) AddCommGrpCat.{u + 1} := by
  let E := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfSize.{u, u + 1} E.inv :=
    E.asEquivalence.toAdjunction.rightAdjoint_preservesLimits
  have : (topology S).HasSheafCompose E.inv := hasSheafCompose_of_preservesLimitsOfSize _
  exact ((E.asEquivalence.toAdjunction.whiskerRight (S.ProEt)ᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (L := sheafCompose (topology S) E) (R := sheafCompose (topology S) E.inv)
    (Iso.refl _) (Iso.refl _)).toEquivalence

/-- **Repleteness**: countable products of abelian pro-étale sheaves are exact. -/
instance hasExactLimitsOfShape_discrete_nat :
    HasExactLimitsOfShape (Discrete ℕ) (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ)
    (sheafForget₂UliftIntEquivalence (S := S))

/-- **Mittag-Leffler for towers of epimorphisms of abelian pro-étale sheaves**: for a tower `F`
with epimorphic transitions, `1 - t` is an epimorphism on a product of the tower, where `t` has
components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. This is transported from sheaves of `ULift ℤ`-modules, where it
follows from the existence of covers by weakly contractible objects. -/
lemma epi_one_sub_of_epi {F : ℕᵒᵖ ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1}}
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op))
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) :
    Epi (𝟙 P.pt - t) := by
  let e := sheafForget₂UliftIntEquivalence (S := S)
  let G := e.inverse
  have : e.functor.Additive :=
    inferInstanceAs (ProEtale.sheafForget₂ (ULift.{u + 1} ℤ) S).Additive
  have : G.Additive := e.toAdjunction.right_adjoint_additive
  have hP' : IsLimit (Fan.mk (G.obj P.pt) fun n ↦ G.map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit G _ _
      (IsLimit.ofIsoLimit hP (Cone.ext (Iso.refl _) fun ⟨_⟩ ↦ (Category.id_comp _).symm))
  have h := GrothendieckTopology.epi_one_sub_of_forall_exists
    (fun W : S.ProEt ↦ (topology S).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ by
      obtain ⟨ι, W, f, hW, hcov⟩ := exists_isWeaklyContractible_cover.{u + 1} V
      exact ⟨ι, W, f, fun i ↦ (hW i).2, hcov⟩)
    (fun _ h ↦ h) (F := F ⋙ G) hP' (G.map t)
    (fun n ↦ by simpa using congrArg G.map (ht n))
    (fun n ↦ G.map_epi _)
  have : Epi (G.map (𝟙 P.pt - t)) := by
    rw [G.map_sub, G.map_id]
    exact h
  exact G.epi_of_epi_map this

/-- **Cohomology of the limit of a tower of abelian pro-étale sheaves.** Let `F` be a tower of
epimorphisms of abelian sheaves on `S_proét` with limit `c`. If `Hᵠ(Fₙ) = 0` for all `n` and
`q > N`, and the transition maps `H^N(Fₙ₊₁) ⟶ H^N(Fₙ)` are surjective, then `Hᵠ(lim Fₙ) = 0`
for `q > N`: the Milnor sequence `0 ⟶ lim Fₙ ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0` is exact by repleteness, and
cohomology commutes with countable products. -/
theorem subsingleton_H_of_isLimit_tower
    {F : ℕᵒᵖ ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1}}
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) {c : Cone F} (hc : IsLimit c) (N : ℕ)
    (hvan : ∀ n q, N < q → Subsingleton (Sheaf.H (F.obj (op n)) q))
    (hsurj : ∀ n : ℕ, Function.Surjective (Sheaf.H.map (F.map (homOfLE n.le_succ).op) N))
    (q : ℕ) (hq : N < q) : Subsingleton (Sheaf.H c.pt q) :=
  Abelian.Ext.subsingleton_of_isLimit_tower _
    (fun _ hP t ht ↦ epi_one_sub_of_epi hF hP t ht) hc N hvan hsurj q hq

end AlgebraicGeometry.Scheme.ProEt

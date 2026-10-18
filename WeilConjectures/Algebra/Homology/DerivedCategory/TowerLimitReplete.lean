/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Derived limits of towers of epimorphisms in a replete abelian category

Let `C` be an abelian category in which, for every tower of epimorphisms `⋯ ⟶ X₁ ⟶ X₀`, the
projection `lim Xₙ ⟶ X₀` is an epimorphism (`CategoryTheory.EpiπAppZeroOfEpi`), for instance
sheaves on a replete topos such as the pro-étale site (Bhatt–Scholze, *The pro-étale topology for
schemes*, §3.1). Then `lim¹` of a tower of epimorphisms vanishes
(`CategoryTheory.Limits.epi_one_sub_of_epiπAppZeroOfEpi`), so that, if moreover countable
products are exact, the limit of a tower of epimorphisms is its derived limit:

- `DerivedCategory.isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi`: for towers of complexes with
  degreewise epimorphic transitions, generalising
  `DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi` from modules;
- `DerivedCategory.isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi`: for towers of
  objects placed in degree `0`.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite
namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-- **`lim¹` of a tower of epimorphisms vanishes** in an abelian category in which sequential
limits of epimorphisms project epimorphically onto the first term (a replete topos): for a tower
`F` with epimorphic transitions, `1 - t : ∏ Fₙ ⟶ ∏ Fₙ` is an epimorphism, where `t` has
components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`.

Over `P = ∏ Fₙ`, the objects `Gₙ` of partial solutions `(p, x₀, …, xₙ)` of
`xᵢ - t(xᵢ₊₁) = pᵢ` (with `x₀ = 0`) form a tower of epimorphisms, each `Gₙ₊₁` being the pullback
of the epimorphism `Fₙ₊₁ ⟶ Fₙ` along `(p, x) ↦ xₙ - pₙ`. Its limit maps epimorphically onto
`G₀ = P`, and this map factors through `1 - t`. -/
lemma epi_one_sub_of_epiπAppZeroOfEpi (hC : EpiπAppZeroOfEpi C) {F : ℕᵒᵖ ⥤ C}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 P.pt - t) := by
  let stage : (n : ℕ) → Σ G : C, (G ⟶ P.pt) × (G ⟶ F.obj (op n)) := fun n ↦
    Nat.rec ⟨P.pt, 𝟙 _, 0⟩ (fun n s ↦ ⟨pullback (s.2.2 - s.2.1 ≫ P.proj n)
      (F.map (homOfLE n.le_succ).op), pullback.fst _ _ ≫ s.2.1, pullback.snd _ _⟩) n
  let π (n : ℕ) : (stage (n + 1)).1 ⟶ (stage n).1 := pullback.fst _ _
  have hπ (n : ℕ) : Epi (π n) := Abelian.epi_pullback_of_epi_g _ _
  have ha (n : ℕ) : (stage (n + 1)).2.1 = π n ≫ (stage n).2.1 := rfl
  have hb (n : ℕ) : (stage (n + 1)).2.2 ≫ F.map (homOfLE n.le_succ).op =
      π n ≫ ((stage n).2.2 - (stage n).2.1 ≫ P.proj n) :=
    (pullback.condition).symm
  let G : ℕᵒᵖ ⥤ C := Functor.ofOpSequence (X := fun n ↦ (stage n).1) π
  let c := limit.cone G
  have hc : IsLimit c := limit.isLimit G
  have h0 : Epi (c.π.app ⟨0⟩) := hC hc fun n ↦ by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact hπ n
  have hcπ (n : ℕ) : c.π.app (op (n + 1)) ≫ π n = c.π.app (op n) := by
    have := c.w (homOfLE n.le_succ).op
    rwa [Functor.ofOpSequence_map_homOfLE_succ] at this
  have hca (n : ℕ) : c.π.app (op n) ≫ (stage n).2.1 = c.π.app (op 0) := by
    induction n with
    | zero => exact comp_id _
    | succ n ih => rw [ha, ← assoc, hcπ, ih]
  let x : c.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ c.π.app (op n) ≫ (stage n).2.2
  have hx : x ≫ (𝟙 P.pt - t) = c.π.app (op 0) := by
    refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    rw [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, ht, ← assoc x,
      Fan.IsLimit.fac, Fan.IsLimit.fac, assoc, hb, ← assoc, hcπ, Preadditive.comp_sub,
      ← assoc, hca]
    abel
  have : Epi (x ≫ (𝟙 P.pt - t)) := by
    rw [hx]
    exact h0
  exact epi_of_epi x _

end CategoryTheory.Limits

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- **Derived limits of towers of epimorphisms in a replete abelian category**: in an abelian
category with exact countable products in which sequential limits of epimorphisms project
epimorphically onto the first term, the image in the derived category of a limit cone `c` of a
tower `T` of complexes whose transitions are degreewise epimorphisms is a homotopy limit cone:
in each degree `0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact
(`CategoryTheory.Limits.epi_one_sub_of_epiπAppZeroOfEpi`), and the attached triangle is the
Milnor triangle. -/
theorem isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi (hC : EpiπAppZeroOfEpi C)
    {T : ℕᵒᵖ ⥤ CochainComplex C ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) :
    IsHomotopyLimit (Q.mapCone c) := by
  let K (n : ℕ) : CochainComplex C ℤ := T.obj (op n)
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hP : IsLimit P := productIsProduct K
  let t : P.pt ⟶ P.pt := Pi.lift fun n ↦ Pi.π K (n + 1) ≫ T.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ P.proj n = P.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op :=
    Pi.lift_π _ _
  let S := ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      exact epi_one_sub_of_epiπAppZeroOfEpi hC (F := T ⋙ HomologicalComplex.eval _ _ i)
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hP) (t.f i)
        (fun n ↦ (HomologicalComplex.comp_f _ _ i).symm.trans
          ((congrArg (fun φ ↦ φ.f i) (ht n)).trans (HomologicalComplex.comp_f _ _ i)))
        fun n ↦ hT n i
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  let hQ := isLimitFanQ K
  refine ⟨_, hQ, triangleOfSESδ hS, isomorphic_distinguished _ (triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      Triangle.mk_mor₁, Iso.refl_hom, comp_id, fan_mk_proj, triangleOfSES_mor₁, id_comp]
    exact (Fan.IsLimit.fac hQ (fun n ↦ Q.map (c.π.app (op n))) n).trans (congrArg Q.map
      (Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n).symm |>.trans (Q.map_comp _ _))
  · refine Fan.IsLimit.hom_ext hQ _ _ fun n ↦ ?_
    simp only [Functor.mapCone_pt, Functor.comp_obj, Fan.mk_pt, Functor.mapCone_π_app,
      towerShift, fan_mk_proj, Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.comp_map,
      triangleOfSES, Triangle.mk_mor₂, ← Functor.map_comp, Iso.refl_hom, comp_id,
      Preadditive.sub_comp, Functor.map_sub, CategoryTheory.Functor.map_id,
      Preadditive.comp_sub, id_comp, sub_right_inj, S, P]
    exact (Fan.IsLimit.fac hQ _ n).trans (congrArg Q.map (ht n).symm)
  · simp [triangleOfSES]

/-- **Derived limits of towers of epimorphisms in a replete abelian category**, for objects
placed in degree `0`: for a tower `F` with epimorphic transitions and a limit cone `c`, the
image of `c` in the derived category is a homotopy limit cone, that is
`lim Fₙ ≅ R lim Fₙ`. -/
theorem isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi (hC : EpiπAppZeroOfEpi C)
    {F : ℕᵒᵖ ⥤ C} (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) {c : Cone F}
    (hc : IsLimit c) :
    IsHomotopyLimit ((singleFunctor C 0).mapCone c) := by
  have h := isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi hC
    (T := F ⋙ HomologicalComplex.single C (ComplexShape.up ℤ) 0) (fun n i ↦ ?_)
    (isLimitOfPreserves (HomologicalComplex.single C (ComplexShape.up ℤ) 0) hc)
  · refine IsHomotopyLimit.of_iso (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (singleFunctorIsoCompQ C 0).symm) h _
      ((singleFunctorIsoCompQ C 0).symm.app c.pt) fun n ↦ ?_
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.id_comp, Iso.app_hom]
    exact ((singleFunctorIsoCompQ C 0).inv.naturality (c.π.app (op n)))
  · by_cases hi : i = 0
    · subst hi
      rw [Functor.comp_map, HomologicalComplex.single_map_f_self]
      have := hF n
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _

end DerivedCategory

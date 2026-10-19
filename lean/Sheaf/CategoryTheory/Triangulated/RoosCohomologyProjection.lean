/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.CategoryTheory.Triangulated.RoosCohomologyBoundary
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The epimorphic projection from Roos cohomology to the inverse limit

Source: Stacks Project, Tag 07KY, the kernel extraction in the proof of the Milnor
sequence (blueprint: lem-weil-pbc-roos-cohomology-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w vC uC vD uD vS uS r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasCountableProducts (DerivedCategory C)]
  {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]

private def roosProjectionCone
    (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C)) (G : C ⥤ (S ⥤ AddCommGrpCat.{r}))
    [G.Additive] (RF : D ⥤ DerivedCategory C) (p : RF ⟶ roosCohomologyProduct K)
    (δ : roosCohomologyProduct K ⟶ RF ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ))
    (hT : ∀ M : D, IsDerivedLimitTriangle
      (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)
      (RF.obj M) (p.app M) (δ.app M)) (i : ℤ) (M : D) (U : S) :
    Cone (((roosCohomologyTowers K G i).obj M).obj U) where
  pt := ((DerivedCategory.homologyFunctor C i ⋙ G).obj (RF.obj M)).obj U
  π := NatTrans.ofOpSequence
    (fun n ↦ ((DerivedCategory.homologyFunctor C i ⋙ G).map
      (p.app M ≫ Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).app U) (by
      intro n
      let H := DerivedCategory.homologyFunctor C i ⋙ G
      simp only [Functor.const_obj_map]
      symm
      change (H.map (p.app M ≫ Pi.π _ (n + 1))).app U ≫
        (H.map ((K.obj M).map (homOfLE (Nat.le_succ n)).op)).app U = _
      rw [← NatTrans.comp_app, ← H.map_comp]
      congr 2
      have hzero := Pretriangulated.comp_distTriang_mor_zero₁₂ _ (hT M)
      have hn := congrArg (fun f ↦ f ≫ Pi.π
        (fun n : ℕ ↦ (K.obj M).obj (op n)) n) hzero
      simp only [zero_comp] at hn
      change (p.app M ≫ towerTransitionEndomorphism _) ≫ Pi.π _ n = 0 at hn
      simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
        Category.id_comp, Pi.lift_π, Preadditive.comp_sub, Category.assoc] at hn
      simpa only [Category.assoc] using (sub_eq_zero.mp hn).symm)

/-- The projection half of the Milnor sequence, retaining both naturalities.
Source: Stacks Project, Tags 07KC and 07KY, proof of the Milnor sequence
(blueprint: lem-weil-pbc-roos-cohomology-projection).

Proof: the zero composite p(1-s) gives the successor compatibility of the maps
H^i(p followed by the nth product projection). They form a cone over the cohomology
tower. Its unique map to the inverse limit defines b. The cone equations and
naturality of p give naturality in M; restriction maps give naturality in S.
To prove surjectivity, take an element of the inverse limit and its tuple of
coordinates. The product comparison is invertible, so this tuple comes from an
element x of H^i of the derived product. The limit compatibility equations make
H^i(1-s)(x) zero after every projection, hence zero. Apply the long exact homology
sequence, preserved by G and evaluation, to lift x to H^i(RF). The lift maps to the
original limit element because all its limit coordinates agree. Thus b is epi.
This applies also to zero towers and to every integer degree. -/
theorem roosCohomology_projection
    (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C)) (G : C ⥤ (S ⥤ AddCommGrpCat.{r}))
    [G.Additive] [G.PreservesHomology]
    (hH : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j ⋙ G))
    (RF : D ⥤ DerivedCategory C) (p : RF ⟶ roosCohomologyProduct K)
    (δ : roosCohomologyProduct K ⟶ RF ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ))
    (hT : ∀ M : D, IsDerivedLimitTriangle
      (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)
      (RF.obj M) (p.app M) (δ.app M)) (i : ℤ) :
    ∃ b : RF ⋙ DerivedCategory.homologyFunctor C i ⋙ G ⟶ roosCohomologyRight K G i,
      ∀ (M : D) (U : S), Epi ((b.app M).app U) ∧
        ∀ n : ℕ, (b.app M).app U ≫
            limit.π (((roosCohomologyTowers K G i).obj M).obj U) (op n) =
          ((DerivedCategory.homologyFunctor C i ⋙ G).map
            (p.app M ≫ Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).app U  := by
  let b₀ (M : D) (U : S) :
      ((DerivedCategory.homologyFunctor C i ⋙ G).obj (RF.obj M)).obj U ⟶
        limit (((roosCohomologyTowers K G i).obj M).obj U) :=
    limit.lift _ (roosProjectionCone K G RF p δ hT i M U)
  have hπ (M : D) (U : S) (n : ℕ) : b₀ M U ≫
      limit.π (((roosCohomologyTowers K G i).obj M).obj U) (op n) =
      ((DerivedCategory.homologyFunctor C i ⋙ G).map
        (p.app M ≫ Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).app U := by
    simp only [b₀, limit.lift_π, roosProjectionCone, NatTrans.ofOpSequence_app]
  let b : RF ⋙ DerivedCategory.homologyFunctor C i ⋙ G ⟶ roosCohomologyRight K G i :=
    { app := fun M ↦
        { app := b₀ M
          naturality := by
            intro U V f
            apply limit.hom_ext
            intro ⟨n⟩
            change _ ≫ (b₀ M V ≫ _) = b₀ M U ≫ limMap _ ≫ _
            rw [hπ, limMap_π, ← Category.assoc, hπ]
            exact ((DerivedCategory.homologyFunctor C i ⋙ G).map
              (p.app M ≫ Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).naturality f }
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext U
        apply limit.hom_ext
        intro ⟨n⟩
        change (((DerivedCategory.homologyFunctor C i ⋙ G).map (RF.map f)).app U ≫
            b₀ N U) ≫ _ = (b₀ M U ≫
              limMap (((roosCohomologyTowers K G i).map f).app U)) ≫ _
        rw [Category.assoc, hπ, Category.assoc, limMap_π, ← Category.assoc, hπ]
        change ((DerivedCategory.homologyFunctor C i ⋙ G).map (RF.map f)).app U ≫
            ((DerivedCategory.homologyFunctor C i ⋙ G).map
              (p.app N ≫ Pi.π _ n)).app U =
          ((DerivedCategory.homologyFunctor C i ⋙ G).map
              (p.app M ≫ Pi.π _ n)).app U ≫
            ((DerivedCategory.homologyFunctor C i ⋙ G).map ((K.map f).app (op n))).app U
        rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp,
          ← Functor.map_comp]
        congr 2
        rw [← Category.assoc, p.naturality]
        simp [Category.assoc] }
  refine ⟨b, fun M U ↦ ⟨?_, hπ M U⟩⟩
  let H := (DerivedCategory.homologyFunctor C i ⋙ G) ⋙
    (evaluation S AddCommGrpCat.{r}).obj U
  have := hH i
  have hc : IsIso (roosCohomologyComparison K G i M U) := by
    change IsIso (piComparison H (fun n : ℕ ↦ (K.obj M).obj (op n)))
    infer_instance
  let e := asIso (roosCohomologyComparison K G i M U)
  let A := ((roosCohomologyTowers K G i).obj M).obj U
  let j : limit A ⟶ ∏ᶜ fun n : ℕ ↦ A.obj (op n) :=
    Pi.lift (fun n ↦ limit.π A (op n))
  let t := Triangle.mk (p.app M)
    (towerTransitionEndomorphism
      (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)) (δ.app M)
  have hex := ((DerivedCategory.HomologySequence.exact₂ t (hT M) i).map G).map
    ((evaluation S AddCommGrpCat.{r}).obj U)
  have hd : H.map t.mor₂ ≫ e.hom = e.hom ≫ roosMap A := by
    change H.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)) ≫
          piComparison H (fun n : ℕ ↦ (K.obj M).obj (op n)) =
        piComparison H (fun n : ℕ ↦ (K.obj M).obj (op n)) ≫
          towerTransitionEndomorphism
            (fun n : ℕ ↦ H.map ((K.obj M).map (homOfLE (Nat.le_succ n)).op))
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, towerTransitionEndomorphism,
      towerProductShift, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [← H.map_comp]
    simp only [Preadditive.sub_comp, Category.id_comp, Pi.lift_π, H.map_sub, H.map_comp,
      piComparison_comp_π_assoc, piComparison_comp_π]
  have hj : j ≫ roosMap A = 0 := by
    apply Pi.hom_ext
    intro n
    simp [j, roosMap, towerTransitionEndomorphism, towerProductShift, Category.assoc]
  change Epi (b₀ M U)
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  let y := e.inv (j x)
  have hy : e.hom y = j x := by
    change (e.inv ≫ e.hom) (j x) = j x
    simp
  have hz : (H.map t.mor₂) y = 0 := by
    apply ((AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance)
    rw [map_zero]
    change (H.map t.mor₂ ≫ e.hom) y = 0
    rw [hd]
    change (roosMap A) (e.hom y) = 0
    rw [hy]
    change (j ≫ roosMap A) x = 0
    rw [hj]
    rfl
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp hex y hz
  change (H.map t.mor₁) z = y at hz
  refine ⟨z, Concrete.limit_ext A _ _ ?_⟩
  intro ⟨n⟩
  have hbπ := ConcreteCategory.congr_hom (hπ M U n) z
  change (limit.π A (op n)) ((b₀ M U) z) = (limit.π A (op n)) x
  have hf : H.map t.mor₁ ≫ e.hom ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n =
      H.map (p.app M ≫ Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n) := by
    change H.map t.mor₁ ≫ piComparison H _ ≫ Pi.π _ n = _
    rw [piComparison_comp_π, ← H.map_comp]
    rfl
  calc
    _ = (Pi.π (fun n : ℕ ↦ A.obj (op n)) n) (e.hom ((H.map t.mor₁) z)) :=
      hbπ.trans (ConcreteCategory.congr_hom hf z).symm
    _ = (Pi.π (fun n : ℕ ↦ A.obj (op n)) n) (j x) := by rw [hz, hy]
    _ = _ := ConcreteCategory.congr_hom (Pi.lift_π _ n) x

end CategoryTheory

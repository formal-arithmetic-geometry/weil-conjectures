/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Boundary factorization for an exact presheaf-valued realization of a Roos triangle

Source: Stacks Project, Tags 07KW and 07KY; the boundary-extraction step of
`prop-weil-pbc-roos-triangle` (blueprint: lem-weil-pbc-roos-cohomology-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w vC uC vD uD vS uS r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasCountableProducts (DerivedCategory C)]
  {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]

/-- The product of the evaluated tower. Source: Stacks 08TC
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
abbrev roosCohomologyProduct (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C)) :
    D ⥤ DerivedCategory C where
  obj M := ∏ᶜ fun n : ℕ ↦ (K.obj M).obj (op n)
  map f := Limits.Pi.map (fun n : ℕ ↦ (K.map f).app (op n))
  map_id := by intros; apply Pi.hom_ext; intro n; simp
  map_comp := by intros; apply Pi.hom_ext; intro n; simp

/-- The cohomology tower of a presheaf-valued exact realization. Source: Stacks 07KY
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
def roosCohomologyTowers (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C))
    (G : C ⥤ (S ⥤ AddCommGrpCat.{r})) (i : ℤ) : D ⥤ (S ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{r})) :=
  K ⋙ (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory C) (S ⥤ AddCommGrpCat.{r})).obj
    (DerivedCategory.homologyFunctor C i ⋙ G) ⋙ flipFunctor ℕᵒᵖ S AddCommGrpCat.{r}

/-- The actual first right derived inverse limit. Source: Stacks 07KW
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
abbrev roosCohomologyFirstLimit :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r} :=
  let := roosTowerEnoughInjectives.{r}
  let := roosLimitAdditive.{r}
  (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).rightDerived 1

/-- The left term in the Milnor sequence. Source: Stacks 07KY
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
def roosCohomologyLeft (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C))
    (G : C ⥤ (S ⥤ AddCommGrpCat.{r})) (i : ℤ) : D ⥤ (S ⥤ AddCommGrpCat.{r}) :=
  roosCohomologyTowers K G (i - 1) ⋙
    (Functor.whiskeringRight S (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) AddCommGrpCat.{r}).obj
      roosCohomologyFirstLimit

/-- The right term in the Milnor sequence. Source: Stacks 07KY
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
def roosCohomologyRight (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C))
    (G : C ⥤ (S ⥤ AddCommGrpCat.{r})) (i : ℤ) : D ⥤ (S ⥤ AddCommGrpCat.{r}) :=
  roosCohomologyTowers K G i ⋙
    (Functor.whiskeringRight S (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) AddCommGrpCat.{r}).obj lim

/-- The comparison given by the derived product projections. Source: Stacks 07KC
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
def roosCohomologyComparison (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C))
    (G : C ⥤ (S ⥤ AddCommGrpCat.{r})) (i : ℤ) (M : D) (U : S) :
    ((DerivedCategory.homologyFunctor C i ⋙ G).obj
      ((roosCohomologyProduct K).obj M)).obj U ⟶
      ∏ᶜ fun n : ℕ ↦ (((roosCohomologyTowers K G i).obj M).obj U).obj (op n) :=
  Pi.lift (fun n ↦ ((DerivedCategory.homologyFunctor C i ⋙ G).map
    (Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).app U)

/-- The connecting map after exact realization. Source: Stacks 07KY
(blueprint: lem-weil-pbc-roos-cohomology-boundary). -/
def roosCohomologyConnecting (G : C ⥤ (S ⥤ AddCommGrpCat.{r})) (i : ℤ)
    {P L : DerivedCategory C} (δ : P ⟶ L⟦(1 : ℤ)⟧) (U : S) :
    ((DerivedCategory.homologyFunctor C (i - 1) ⋙ G).obj P).obj U ⟶
      ((DerivedCategory.homologyFunctor C i ⋙ G).obj L).obj U :=
  (G.map ((DerivedCategory.homologyFunctor C 0).shiftMap δ (i - 1) i (by omega))).app U

@[reassoc]
private theorem roosBoundary_comparison_transition
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (K : ℕ → C) [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n) :
    F.map (towerTransitionEndomorphism f) ≫ piComparison F K =
      piComparison F K ≫ towerTransitionEndomorphism (fun n => F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Functor.map_id, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    piComparison_comp_π, Limits.Pi.lift_π, Category.id_comp]
  rw [← F.map_comp, Limits.Pi.lift_π]
  rw [← Category.assoc, piComparison_comp_π, ← F.map_comp]

@[reassoc]
private theorem roosBoundary_comparison_natural
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (K K' : ℕ → C) [HasProduct K] [HasProduct K']
    [HasProduct (fun n => F.obj (K n))] [HasProduct (fun n => F.obj (K' n))]
    (φ : ∀ n, K n ⟶ K' n) :
    F.map (Limits.Pi.map φ) ≫ piComparison F K' =
      piComparison F K ≫ Limits.Pi.map (fun n => F.map (φ n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
  rw [← F.map_comp, Limits.Pi.map_π]
  rw [← Category.assoc, piComparison_comp_π, ← F.map_comp]

private theorem roosBoundary_cokernel_exact {C : Type*} [Category C] [Abelian C]
    {X Y Z W : C} (f : X ⟶ Y) (d : Y ⟶ Z) (q : Z ⟶ W)
    (hfd : f ≫ d = 0) (hdq : d ≫ q = 0)
    (hex : (ShortComplex.mk d q hdq).Exact) :
    ∃ hz : cokernel.desc f d hfd ≫ q = 0,
      (ShortComplex.mk (cokernel.desc f d hfd) q hz).Exact := by
  have hz : cokernel.desc f d hfd ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π f)]
    simpa using hdq
  refine ⟨hz, ?_⟩
  let φ : ShortComplex.mk d q hdq ⟶
      ShortComplex.mk (cokernel.desc f d hfd) q hz :=
    ShortComplex.homMk (cokernel.π f) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : Epi φ.τ₁ := by change Epi (cokernel.π f); infer_instance
  have : IsIso φ.τ₂ := by change IsIso (𝟙 Z); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 W); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex


set_option backward.isDefEq.respectTransparency false in
/-- The boundary half of the Milnor sequence, with its canonical cokernel factorization.
Source: Stacks Project, Tags 07KW and 07KY, proof of the Milnor sequence
(blueprint: lem-weil-pbc-roos-cohomology-boundary).

Proof: apply the long exact homology sequence to each specified distinguished triangle.
The exact functor G, followed by evaluation at U, preserves its three-term exact segments.
Preservation of countable products identifies the product cohomology with the product
of the cohomologies via the displayed comparison; checking after each projection sends
1-s to the Roos map. Exactness therefore makes the cokernel descent of the connecting
map monic. The natural Roos isomorphism from R¹lim to this cokernel gives a. Exactness
at the middle cohomology identifies its image with the kernel of the product projection.
The cokernel projection and product comparison are epi, so the factorization is unique.
Naturality of the connecting map and of the Roos isomorphism gives naturality in M;
restriction maps in S give the same commuting square and hence naturality in U. The
zero tower and all integer degrees are included; no boundedness is used. -/
theorem roosCohomology_boundary
    (K : D ⥤ (ℕᵒᵖ ⥤ DerivedCategory C)) (G : C ⥤ (S ⥤ AddCommGrpCat.{r}))
    [G.Additive] [G.PreservesHomology]
    (hH : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j ⋙ G))
    (RF : D ⥤ DerivedCategory C) (p : RF ⟶ roosCohomologyProduct K)
    (δ : roosCohomologyProduct K ⟶ RF ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ))
    (hT : ∀ M : D, IsDerivedLimitTriangle
      (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)
      (RF.obj M) (p.app M) (δ.app M)) (i : ℤ) :
    ∃ a : roosCohomologyLeft K G i ⟶ RF ⋙ DerivedCategory.homologyFunctor C i ⋙ G,
      ∀ (M : D) (U : S),
        Mono ((a.app M).app U) ∧
        (∃ hz : (a.app M).app U ≫
            (((DerivedCategory.homologyFunctor C i ⋙ G).map (p.app M)).app U ≫
              roosCohomologyComparison K G i M U) = 0,
          (ShortComplex.mk ((a.app M).app U)
            (((DerivedCategory.homologyFunctor C i ⋙ G).map (p.app M)).app U ≫
              roosCohomologyComparison K G i M U) hz).Exact) ∧
        (∃ e : roosCohomologyFirstLimit.obj
            (((roosCohomologyTowers K G (i - 1)).obj M).obj U) ≅
              cokernel (roosMap (((roosCohomologyTowers K G (i - 1)).obj M).obj U)),
          roosCohomologyComparison K G (i - 1) M U ≫
            cokernel.π (roosMap (((roosCohomologyTowers K G (i - 1)).obj M).obj U)) ≫
            e.inv ≫ (a.app M).app U = roosCohomologyConnecting G i (δ.app M) U) := by
  classical
  let := roosTowerEnoughInjectives.{r}
  let := roosLimitAdditive.{r}
  obtain ⟨_, _, e₁, he, _⟩ := derivedLimitRoosAbelianGroups.{r}
  let T (M : D) := Triangle.mk (p.app M)
    (towerTransitionEndomorphism
      (fun n : ℕ ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)) (δ.app M)
  let H (j : ℤ) (U : S) := (DerivedCategory.homologyFunctor C j ⋙ G) ⋙
    (evaluation S AddCommGrpCat.{r}).obj U
  let A (M : D) (U : S) := ((roosCohomologyTowers K G (i - 1)).obj M).obj U
  let c (M : D) (U : S) := roosCohomologyComparison K G (i - 1) M U
  have hc (M : D) (U : S) : IsIso (c M U) := by
    have := hH (i - 1)
    change IsIso (piComparison (H (i - 1) U) (fun n : ℕ ↦ (K.obj M).obj (op n)))
    infer_instance
  let d (M : D) (U : S) := inv (c M U) ≫ roosCohomologyConnecting G i (δ.app M) U
  have hfd (M : D) (U : S) : roosMap (A M U) ≫ d M U = 0 := by
    rw [← cancel_epi (c M U)]
    dsimp only [d]
    have ht := roosBoundary_comparison_transition (H (i - 1) U)
      (fun n : ℕ ↦ (K.obj M).obj (op n))
      (fun n ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)
    change (H (i - 1) U).map (T M).mor₂ ≫ c M U =
      c M U ≫ roosMap (A M U) at ht
    rw [← Category.assoc, ← ht, Category.assoc, IsIso.hom_inv_id_assoc]
    have hz := DerivedCategory.HomologySequence.comp_δ (T M) (hT M)
      (i - 1) i (by omega)
    change (G.map ((DerivedCategory.homologyFunctor C (i - 1)).map (T M).mor₂)).app U ≫
      (G.map (DerivedCategory.HomologySequence.δ (T M) (i - 1) i (by omega))).app U = 0
    rw [← NatTrans.comp_app, ← G.map_comp, hz, G.map_zero]
    rfl
  let a₀ (M : D) (U : S) := (e₁ (A M U)).hom ≫
    cokernel.desc (roosMap (A M U)) (d M U) (hfd M U)
  have hfac (M : D) (U : S) : c M U ≫ cokernel.π (roosMap (A M U)) ≫
      (e₁ (A M U)).inv ≫ a₀ M U = roosCohomologyConnecting G i (δ.app M) U := by
    simp [a₀, d]
  have hpoint (M : D) (U : S) : Mono (a₀ M U) ∧
      ∃ hz : a₀ M U ≫ ((H i U).map (p.app M) ≫
          roosCohomologyComparison K G i M U) = 0,
        (ShortComplex.mk (a₀ M U) ((H i U).map (p.app M) ≫
          roosCohomologyComparison K G i M U) hz).Exact := by
    let q := (H i U).map (p.app M) ≫ roosCohomologyComparison K G i M U
    have h₃ : (ShortComplex.mk (roosMap (A M U)) (d M U) (hfd M U)).Exact := by
      have hex := ((DerivedCategory.HomologySequence.exact₃ (T M) (hT M)
        (i - 1) i (by omega)).map G).map ((evaluation S AddCommGrpCat.{r}).obj U)
      apply ShortComplex.exact_of_iso _ hex
      refine ShortComplex.isoMk (asIso (c M U)) (asIso (c M U)) (Iso.refl _) ?_ ?_
      · exact (roosBoundary_comparison_transition (H (i - 1) U)
          (fun n : ℕ ↦ (K.obj M).obj (op n))
          (fun n ↦ (K.obj M).map (homOfLE (Nat.le_succ n)).op)).symm
      · simp [d, roosCohomologyConnecting, DerivedCategory.HomologySequence.δ, T]
    have : Mono (cokernel.desc (roosMap (A M U)) (d M U) (hfd M U)) :=
      h₃.mono_cokernelDesc
    refine ⟨inferInstanceAs (Mono (a₀ M U)), ?_⟩
    have hdq : d M U ≫ q = 0 := by
      have hz := congrArg (fun f ↦ (G.map f).app U)
        (DerivedCategory.HomologySequence.δ_comp (T M) (hT M) (i - 1) i (by omega))
      dsimp only [d, q]
      rw [Category.assoc, ← Category.assoc (roosCohomologyConnecting G i (δ.app M) U)]
      have hz' : roosCohomologyConnecting G i (δ.app M) U ≫
          (H i U).map (p.app M) = 0 := by
        simpa [H, T, roosCohomologyConnecting, DerivedCategory.HomologySequence.δ,
          Functor.map_comp, NatTrans.comp_app] using hz
      rw [hz', zero_comp, comp_zero]
    have h₁ : (ShortComplex.mk (d M U) q hdq).Exact := by
      have hex := ((DerivedCategory.HomologySequence.exact₁ (T M) (hT M)
        (i - 1) i (by omega)).map G).map ((evaluation S AddCommGrpCat.{r}).obj U)
      have : IsIso (roosCohomologyComparison K G i M U) := by
        have := hH i
        change IsIso (piComparison (H i U) (fun n : ℕ ↦ (K.obj M).obj (op n)))
        infer_instance
      apply ShortComplex.exact_of_iso _ hex
      refine ShortComplex.isoMk (asIso (c M U)) (Iso.refl _)
        (asIso (roosCohomologyComparison K G i M U)) ?_ ?_
      · simp [d, roosCohomologyConnecting, DerivedCategory.HomologySequence.δ, T]
      · rfl
    obtain ⟨hz, hex⟩ := roosBoundary_cokernel_exact _ _ _ (hfd M U) hdq h₁
    have hz' : a₀ M U ≫ q = 0 := by simp [a₀, Category.assoc, hz]
    refine ⟨hz', ?_⟩
    let e : ShortComplex.mk (cokernel.desc (roosMap (A M U)) (d M U) (hfd M U)) q hz ≅
        ShortComplex.mk (a₀ M U) q hz' :=
      ShortComplex.isoMk (e₁ (A M U)).symm (Iso.refl _) (Iso.refl _)
        (by simp [a₀]) (by simp)
    exact ShortComplex.exact_of_iso e hex
  have hnat (M N : D) (U V : S) (φ : A M U ⟶ A N V)
      (f : (H (i - 1) U).obj ((roosCohomologyProduct K).obj M) ⟶
        (H (i - 1) V).obj ((roosCohomologyProduct K).obj N))
      (g : (H i U).obj (RF.obj M) ⟶ (H i V).obj (RF.obj N))
      (hcomp : f ≫ c N V = c M U ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)))
      (hconn : f ≫ roosCohomologyConnecting G i (δ.app N) V =
        roosCohomologyConnecting G i (δ.app M) U ≫ g) :
      roosCohomologyFirstLimit.map φ ≫ a₀ N V = a₀ M U ≫ g := by
    obtain ⟨h, _, hn⟩ := he (A M U) (A N V) φ
    dsimp only [a₀]
    rw [← Category.assoc, hn, Category.assoc, Category.assoc]
    apply congrArg ((e₁ (A M U)).hom ≫ ·)
    apply cokernel.map_desc
    change (inv (c M U) ≫ roosCohomologyConnecting G i (δ.app M) U) ≫ g =
      Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫
        inv (c N V) ≫ roosCohomologyConnecting G i (δ.app N) V
    rw [← cancel_epi (c M U)]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc (c M U), ← hcomp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hconn.symm
  let a : roosCohomologyLeft K G i ⟶ RF ⋙ DerivedCategory.homologyFunctor C i ⋙ G :=
    { app := fun M ↦
        { app := a₀ M
          naturality := by
            intro U V f
            apply hnat M M U V (((roosCohomologyTowers K G (i - 1)).obj M).map f)
              (((DerivedCategory.homologyFunctor C (i - 1) ⋙ G).obj
                ((roosCohomologyProduct K).obj M)).map f)
            · apply Pi.hom_ext
              intro n
              simp only [Category.assoc, c, roosCohomologyComparison,
                Pi.lift_π]
              rw [Pi.map_π, ← Category.assoc, Pi.lift_π]
              exact ((DerivedCategory.homologyFunctor C (i - 1) ⋙ G).map
                (Pi.π (fun n : ℕ ↦ (K.obj M).obj (op n)) n)).naturality f
            · exact (G.map ((DerivedCategory.homologyFunctor C 0).shiftMap
                (δ.app M) (i - 1) i (by omega))).naturality f }
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext U
        apply hnat M N U U (((roosCohomologyTowers K G (i - 1)).map f).app U)
          ((H (i - 1) U).map ((roosCohomologyProduct K).map f))
        · exact roosBoundary_comparison_natural (H (i - 1) U)
            (fun n : ℕ ↦ (K.obj M).obj (op n))
            (fun n : ℕ ↦ (K.obj N).obj (op n))
            (fun n ↦ (K.map f).app (op n))
        · have hs := congrArg (fun k ↦ (DerivedCategory.homologyFunctor C 0).shiftMap
              k (i - 1) i (by omega)) (δ.naturality f)
          change _ = (DerivedCategory.homologyFunctor C 0).shiftMap
            (δ.app M ≫ (RF.map f)⟦(1 : ℤ)⟧') (i - 1) i (by omega) at hs
          rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at hs
          have hs' := congrArg (fun k ↦ (G.map k).app U) hs
          simp only [DerivedCategory.shift_homologyFunctor,
            Functor.map_comp, NatTrans.comp_app] at hs'
          exact hs'  }
  refine ⟨a, fun M U ↦ ?_⟩
  obtain ⟨hm, hz, hex⟩ := hpoint M U
  exact ⟨hm, ⟨hz, hex⟩, ⟨e₁ (A M U), hfac M U⟩⟩

end CategoryTheory

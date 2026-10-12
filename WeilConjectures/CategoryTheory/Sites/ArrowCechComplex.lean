/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The Čech complex of a morphism with coefficients in a presheaf

Let `f : U ⟶ V` be a morphism in a category `C` whose Čech nerve
`U ×_V U ×_V ⋯ ×_V U` exists, and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in a
preadditive category `A`. The Čech complex `Č(f, P)` is the alternating coface map complex of
the cosimplicial object `n ↦ P(U ×_V ⋯ ×_V U)` (`n + 1` factors).

The main result is that `Č(f, P)` is exact in positive degrees when `A` is abelian and `P` is an
injective presheaf (`CategoryTheory.Arrow.exactAt_cechComplex_of_injective`), for every
morphism `f`. The argument is element-free, so that it applies to any abelian `A` with
coproducts: a cocycle `c : T ⟶ P(U^{q + 2})` is the same as a morphism of presheaves
`φ : ∐_{(-) ⟶ U^{q + 2}} T ⟶ P` killing the boundaries, and the complex of presheaves
`n ↦ ∐_{(-) ⟶ U^{n + 1}} T` is exact in positive degrees: evaluated at `W` it is the complex of
`T`-valued chains on the Čech nerve of the map of sets `Hom(W, U) → Hom(W, V)`, which has an
extra degeneracy given by a choice of lifts. Injectivity of `P` then extends `φ` along the
differential.

## Main definitions

- `CategoryTheory.Arrow.cechComplexFunctor`: the Čech complex `Č(f, P)`, as a functor of `P`.
- `CategoryTheory.Arrow.copowerYoneda`: the presheaf `W ↦ ∐_{W ⟶ Z} T`, as a functor of `Z`.

## Main statements

- `CategoryTheory.Arrow.exactAt_cechComplex_of_injective`: the Čech complex of an injective
  presheaf is exact in positive degrees.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  {A : Type w} [Category A]

section Preadditive

variable [Preadditive A]

/-- The Čech complex `Č(f, P)` of a morphism `f : U ⟶ V` with values in a presheaf `P`: the
alternating coface map complex of the cosimplicial object `n ↦ P(U ×_V ⋯ ×_V U)`, as a functor
of `P`. -/
noncomputable def cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  (Functor.whiskeringLeft _ _ _).obj f.cechNerve.rightOp ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A

/-- The Čech complex `Č(f, P)` of a morphism `f` with values in a presheaf `P`. -/
noncomputable abbrev cechComplex (P : Cᵒᵖ ⥤ A) : CochainComplex A ℕ :=
  f.cechComplexFunctor.obj P

lemma cechComplex_X (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (f.cechComplex P).X n = P.obj (op (f.cechNerve.obj (op ⦋n⦌))) := rfl

lemma cechComplex_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (f.cechComplex P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (f.cechNerve.δ i).op :=
  CochainComplex.of_d _ (AlgebraicTopology.AlternatingCofaceMapComplex.objD
    (f.cechNerve.rightOp ⋙ P)) n

lemma cechComplexFunctor_map_f {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) (n : ℕ) :
    (f.cechComplexFunctor.map φ).f n = φ.app (op (f.cechNerve.obj (op ⦋n⦌))) := rfl

instance : f.cechComplexFunctor (A := A).Additive where
  map_add := rfl

end Preadditive

section Yoneda

variable [Preadditive A] [HasCoproducts.{v} A] (T : A)

/-- The presheaf `W ↦ ∐_{W ⟶ Z} T` of copies of `T` indexed by the morphisms into `Z`, as a
functor of `Z`. Morphisms from it to a presheaf `P` are the morphisms `T ⟶ P(Z)`
(`CategoryTheory.Arrow.copowerYonedaHom`). -/
noncomputable abbrev copowerYoneda : C ⥤ (Cᵒᵖ ⥤ A) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (sigmaConst.obj T)

variable {T}

/-- The morphism `T ⟶ P(Z)` attached to a morphism of presheaves `∐_{(-) ⟶ Z} T ⟶ P`: its
restriction to the summand indexed by `𝟙 Z`. -/
noncomputable def copowerYonedaHom {Z : C} {P : Cᵒᵖ ⥤ A} :
    ((copowerYoneda T).obj Z ⟶ P) →+ (T ⟶ P.obj (op Z)) where
  toFun ψ := Sigma.ι (fun _ : (Z ⟶ Z) ↦ T) (𝟙 Z) ≫ ψ.app (op Z)
  map_zero' := by simp
  map_add' _ _ := by simp

omit [Preadditive A] in
lemma ι_copowerYoneda_obj_map {Z W W' : C} (g : W' ⟶ W) (h : W ⟶ Z) :
    Sigma.ι (fun _ : (W ⟶ Z) ↦ T) h ≫ ((copowerYoneda T).obj Z).map g.op =
      Sigma.ι (fun _ : (W' ⟶ Z) ↦ T) (g ≫ h) := by
  simp

omit [Preadditive A] in
lemma ι_copowerYoneda_map_app {Z Z' W : C} (g : Z ⟶ Z') (h : W ⟶ Z) :
    Sigma.ι (fun _ : (W ⟶ Z) ↦ T) h ≫ ((copowerYoneda T).map g).app (op W) =
      Sigma.ι (fun _ : (W ⟶ Z') ↦ T) (h ≫ g) := by
  simp

lemma ι_comp_app_eq {Z W : C} {P : Cᵒᵖ ⥤ A} (ψ : (copowerYoneda T).obj Z ⟶ P) (h : W ⟶ Z) :
    Sigma.ι (fun _ : (W ⟶ Z) ↦ T) h ≫ ψ.app (op W) = copowerYonedaHom ψ ≫ P.map h.op := by
  have := ψ.naturality h.op
  rw [copowerYonedaHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc, ← this,
    ← Category.assoc, ι_copowerYoneda_obj_map, Category.comp_id]

lemma copowerYonedaHom_injective {Z : C} {P : Cᵒᵖ ⥤ A} :
    Function.Injective (copowerYonedaHom (T := T) (Z := Z) (P := P)) := by
  intro ψ ψ' h
  ext W
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  rw [ι_comp_app_eq, ι_comp_app_eq, h]

lemma copowerYonedaHom_map_comp {Z Z' : C} {P : Cᵒᵖ ⥤ A} (g : Z ⟶ Z')
    (ψ : (copowerYoneda T).obj Z' ⟶ P) :
    copowerYonedaHom ((copowerYoneda T).map g ≫ ψ) = copowerYonedaHom ψ ≫ P.map g.op := by
  rw [copowerYonedaHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, NatTrans.comp_app,
    ← Category.assoc, ι_copowerYoneda_map_app, Category.id_comp, ι_comp_app_eq]

/-- The morphism of presheaves `∐_{(-) ⟶ Z} T ⟶ P` attached to a morphism `x : T ⟶ P(Z)`. -/
@[simps]
noncomputable def copowerYonedaDesc {Z : C} {P : Cᵒᵖ ⥤ A} (x : T ⟶ P.obj (op Z)) :
    (copowerYoneda T).obj Z ⟶ P where
  app W := Sigma.desc fun h : (W.unop ⟶ Z) ↦ x ≫ P.map h.op
  naturality W W' g := by
    refine Sigma.hom_ext _ _ fun h ↦ ?_
    change Sigma.ι (fun _ : (W.unop ⟶ Z) ↦ T) h ≫ ((copowerYoneda T).obj Z).map g.unop.op ≫ _ = _
    rw [← Category.assoc, ι_copowerYoneda_obj_map, Sigma.ι_desc, Sigma.ι_desc_assoc,
      Category.assoc, ← P.map_comp]
    rfl

@[simp]
lemma copowerYonedaHom_desc {Z : C} {P : Cᵒᵖ ⥤ A} (x : T ⟶ P.obj (op Z)) :
    copowerYonedaHom (copowerYonedaDesc x) = x := by
  simp [copowerYonedaHom]

end Yoneda

section ExtraDegeneracy

variable (W : C)

/-- The morphisms `W ⟶ f.right` which lift along `f`. -/
abbrev LiftableHom : Type v := {a : W ⟶ f.right // ∃ l : W ⟶ f.left, l ≫ f.hom = a}

variable {f W} in
/-- A chosen lift of a liftable morphism. -/
noncomputable def LiftableHom.lift (a : f.LiftableHom W) : W ⟶ f.left := a.2.choose

variable {f W} in
omit [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom] in
@[reassoc (attr := simp)]
lemma LiftableHom.lift_hom (a : f.LiftableHom W) : a.lift ≫ f.hom = a.1 := a.2.choose_spec

/-- A point `W ⟶ U ×_V ⋯ ×_V U` of the Čech nerve, viewed as a liftable morphism `W ⟶ V`. -/
noncomputable def cechNerveToLiftableHom (n : SimplexCategoryᵒᵖ)
    (x : W ⟶ f.cechNerve.obj n) : f.LiftableHom W :=
  ⟨x ≫ WidePullback.base _, x ≫ WidePullback.π _ 0, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The Čech nerve of `f` evaluated at `W`, augmented by the liftable morphisms `W ⟶ V`. It is
the Čech nerve of the map of sets `Hom(W, U) → Hom(W, V)`, corestricted to its image. -/
@[simps]
noncomputable def augmentedCechNerveHom : SimplicialObject.Augmented (Type v) where
  left := f.cechNerve ⋙ coyoneda.obj (op W)
  right := f.LiftableHom W
  hom :=
    { app n := ↾(f.cechNerveToLiftableHom W n)
      naturality n m g := by
        ext x
        exact Subtype.ext (by simp [cechNerveToLiftableHom]) }

lemma augmentedCechNerveHom_left_map_apply {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m)
    (x : (f.augmentedCechNerveHom W).left.obj n) :
    (f.augmentedCechNerveHom W).left.map g x = (x : W ⟶ _) ≫ f.cechNerve.map g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extra degeneracy of the Čech nerve of `f` evaluated at `W`: it inserts, as first
coordinate, the chosen lift of the common image in `V`. -/
noncomputable def augmentedCechNerveHom.extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (f.augmentedCechNerveHom W) where
  s' := ↾fun (a : f.LiftableHom W) ↦
    (WidePullback.lift a.1 (fun _ ↦ a.lift) (fun _ ↦ by simp) :
      W ⟶ f.cechNerve.obj (op ⦋0⦌))
  s n := ↾fun (x : W ⟶ f.cechNerve.obj (op ⦋n⦌)) ↦
    (WidePullback.lift (x ≫ WidePullback.base _)
      (Fin.cases (f.cechNerveToLiftableHom W _ x).lift (fun i ↦ x ≫ WidePullback.π _ i))
      (fun i ↦ by
        cases i using Fin.cases
        · simp [cechNerveToLiftableHom]
        · simp) : W ⟶ f.cechNerve.obj (op ⦋n + 1⦌))
  s'_comp_ε := by
    refine ConcreteCategory.hom_ext _ _ fun a ↦ Subtype.ext ?_
    simp [cechNerveToLiftableHom]
  s₀_comp_δ₁ := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    simp only [types_comp_apply, SimplicialObject.δ, augmentedCechNerveHom_left_map_apply,
      TypeCat.ofHom_apply, augmentedCechNerveHom_hom_app]
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      simp [cechNerveToLiftableHom, SimplexCategory.δ]
    · simp [cechNerveToLiftableHom]
  s_comp_δ₀ n := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    simp only [types_comp_apply, SimplicialObject.δ, augmentedCechNerveHom_left_map_apply,
      TypeCat.ofHom_apply, types_id_apply]
    apply WidePullback.hom_ext
    · intro j
      simp [SimplexCategory.δ]
    · simp
  s_comp_δ n i := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    simp only [types_comp_apply, SimplicialObject.δ, augmentedCechNerveHom_left_map_apply,
      TypeCat.ofHom_apply]
    apply WidePullback.hom_ext
    · intro j
      induction j using Fin.cases
      · simp only [Arrow.cechNerve_map, Category.assoc, WidePullback.lift_π]
        have h0 : (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i.succ).op.unop) 0 = 0 := by
          simp [SimplexCategory.δ]
        rw [h0, Fin.cases_zero, Fin.cases_zero]
        congr 1
        exact Subtype.ext (by simp [cechNerveToLiftableHom])
      · simp [SimplexCategory.δ]
    · simp
  s_comp_σ n i := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    simp only [types_comp_apply, SimplicialObject.σ, augmentedCechNerveHom_left_map_apply,
      TypeCat.ofHom_apply]
    apply WidePullback.hom_ext
    · intro j
      induction j using Fin.cases
      · simp only [Arrow.cechNerve_map, Category.assoc, WidePullback.lift_π]
        have h0 : (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i.succ).op.unop) 0 = 0 := by
          simp [SimplexCategory.σ]
        rw [h0, Fin.cases_zero, Fin.cases_zero]
        congr 1
        exact Subtype.ext (by simp [cechNerveToLiftableHom])
      · simp [SimplexCategory.σ]
    · simp

end ExtraDegeneracy

section Exact

variable [Abelian A] [HasCoproducts.{v} A]

/-- The simplicial presheaf `n ↦ ∐_{(-) ⟶ U^{n + 1}} T`. -/
noncomputable abbrev copowerCechNerve (T : A) : SimplicialObject (Cᵒᵖ ⥤ A) :=
  f.cechNerve ⋙ copowerYoneda T

/-- The complex of presheaves `n ↦ ∐_{(-) ⟶ U^{n + 1}} T` is exact in positive degrees. -/
lemma exactAt_alternatingFaceMapComplex_copowerCechNerve (T : A) (q : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj (f.copowerCechNerve T)).ExactAt
      (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp),
    ShortComplex.exact_iff_evaluation]
  intro W
  let E := (f.augmentedCechNerveHom W.unop)
  let ed := (augmentedCechNerveHom.extraDegeneracy f W.unop).map (sigmaConst.obj T)
  have e := ed.homotopyEquiv
  have h₁ : ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj (sigmaConst.obj T)).obj E)))).ExactAt
      (q + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine IsZero.of_iso ?_ (e.toHomologyIso (q + 1))
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by simp)
  have h₂ := congrArg (fun F ↦ F.obj (f.copowerCechNerve T))
    (AlgebraicTopology.map_alternatingFaceMapComplex ((evaluation Cᵒᵖ A).obj W))
  dsimp only [Functor.comp_obj] at h₂
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp)] at h₁
  convert h₁ using 1
  exact congrArg (fun K ↦ HomologicalComplex.sc' K (q + 2) (q + 1) q) h₂

/-- **Čech complexes of injective presheaves are exact.** For every morphism `f` (with a Čech
nerve) and every injective presheaf `P` with values in an abelian category with coproducts,
the Čech complex `Č(f, P)` is exact in positive degrees. -/
theorem exactAt_cechComplex_of_injective (P : Cᵒᵖ ⥤ A) [Injective P] (q : ℕ) :
    (f.cechComplex P).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.exact_iff_exact_up_to_refinements]
  intro T c hc
  change T ⟶ (f.cechComplex P).X (q + 1) at c
  change c ≫ (f.cechComplex P).d (q + 1) (q + 1 + 1) = 0 at hc
  -- the cocycle `c` as a morphism of presheaves, killing the boundaries
  let K := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.copowerCechNerve T)
  have hK := (f.exactAt_alternatingFaceMapComplex_copowerCechNerve T q)
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp)] at hK
  have hd (n : ℕ) : K.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (copowerYoneda T).map (f.cechNerve.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ n
  have key (n : ℕ) (ψ : K.X n ⟶ P) : copowerYonedaHom (K.d (n + 1) n ≫ ψ) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (copowerYonedaHom ψ ≫ P.map (f.cechNerve.δ i).op) := by
    rw [hd, Preadditive.sum_comp, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, map_zsmul, copowerYonedaHom_map_comp]
  have key' (n : ℕ) (x : T ⟶ (f.cechComplex P).X n) : x ≫ (f.cechComplex P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (x ≫ P.map (f.cechNerve.δ i).op) :=
    (congrArg (x ≫ ·) (f.cechComplex_d P n)).trans ((Preadditive.comp_sum _ _ _).trans
      (Finset.sum_congr rfl fun i _ ↦ Preadditive.comp_zsmul _ _ _))
  let φ : K.X (q + 1) ⟶ P := copowerYonedaDesc c
  have hφc : copowerYonedaHom φ = c := copowerYonedaHom_desc c
  have hφ : K.d (q + 1 + 1) (q + 1) ≫ φ = 0 := by
    refine copowerYonedaHom_injective ?_
    rw [key, map_zero, hφc]
    exact (key' (q + 1) c).symm.trans hc
  let ψ : K.X q ⟶ P := hK.descToInjective φ hφ
  have hψ : K.d (q + 1) q ≫ ψ = φ := hK.comp_descToInjective φ hφ
  refine ⟨T, 𝟙 T, inferInstance, copowerYonedaHom ψ, ?_⟩
  refine (Category.id_comp c).trans ?_
  have h₁ := key q ψ
  rw [hψ, hφc] at h₁
  exact h₁.trans (key' q (copowerYonedaHom ψ)).symm

end Exact

end CategoryTheory.Arrow

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Projective.TowerClassProjective

import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal

/-! # Finite for canonical tower classes

## Implementation details

`forgetEvaluatedArrow`, `finiteBoundaryEquality` and `kummerComposite` are stated for general
categories before specializing the coefficient rings, so that the finite normalization formulas
share the same category, single-functor and shift witnesses. `finiteBoundaryEquality` relates
its arrows through heterogeneous equalities that record the endpoint transports.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary forgetful functor at a finite coefficient level. -/
abbrev finiteForget (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.toSheaf.{u + 1}
    (SemilinearSections.ring.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))

/-- Forgetting the action retains the underlying sheaf kernels and sheafified
cokernels. -/
theorem finiteForget_exact (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (finiteForget l E T n) ∧
      PreservesFiniteColimits (finiteForget l E T n) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Exactness on kernels, with the stated independent site sizes. -/
instance finiteForgetLimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (finiteForget l E T n) := (finiteForget_exact l E T n).1

/-- Exactness on cokernels, with the stated independent site sizes. -/
instance finiteForgetColimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (finiteForget l E T n) := (finiteForget_exact l E T n).2

/-- The positive-level evaluation of a tower of abelian sheaves. -/
abbrev abEvaluation (T : Scheme.{u}) (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ (DiagonalAb T)).obj (op n)

/-- The finite integer quotient is uniquely fixed on the constant generators. -/
theorem finiteQuotient_existsUnique (T : Scheme.{u}) (n : ℕ) :
    ∃! q : (abEvaluation T n).obj (integers T) ⟶
      (finiteForget l E T n).obj
        ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))),
      ∀ (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
        HEq (q.hom.app U ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k))
          (k.down : (SpTowerShriek.B l E T n).obj.obj U) := by
  let M := (finiteForget l E T n).obj
    ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))
  let p : (Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ M.obj :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        ((Int.castAddHom ((SpTowerShriek.B l E T n).obj.obj U)).comp
          AddEquiv.ulift.toAddMonoidHom)
      naturality := by
        intro U V f
        ext k
        exact (map_intCast
          ((SemilinearSections.ringPresheaf.{u + 1, u, u + 1}
            (Scheme.ProEt.topology T)
            (fun m ↦ (Arings l E T).obj (op m))
            (fun m ↦ (Arings l E T).map (homOfLE (Nat.le_succ m)).op)).map
              (Prod.mkHom (𝟙 n) f.unop).op).hom k.down).symm }
  let q : (abEvaluation T n).obj (integers T) ⟶ M :=
    ⟨sheafifyLift (Scheme.ProEt.topology T) p M.property⟩
  have hq (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
      HEq (q.hom.app U ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k))
        (k.down : (SpTowerShriek.B l E T n).obj.obj U) := by
    exact (congrArg (fun a ↦ a.app U k)
      (toSheafify_sheafifyLift (Scheme.ProEt.topology T) p M.property)).heq
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _ M.property
  ext U k
  exact eq_of_heq ((hq' U k).trans (hq U k).symm)

/-- The canonical positive-level integer quotient. -/
def finiteQuotient (T : Scheme.{u}) (n : ℕ) :=
  (finiteQuotient_existsUnique l E T n).exists.choose

/-- The finite root-to-coefficient-line map sends z to 1 tensor z, on every chart. -/
theorem finiteRootMap_existsUnique (T : Scheme.{u}) (n : ℕ) :
    ∃! r : (roots l T).obj (op n) ⟶
      (finiteForget l E T n).obj (finiteLine l E T n),
      ∀ (U : T.ProEtᵒᵖ) (z : (roots l T).obj (op n) |>.obj.obj U),
        r.hom.app U z =
          Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop 1 z := by
  obtain ⟨Ψ, _, hΨ⟩ :=
    finiteTateLine_universal T l (FiniteRing l E n) n (finiteScalar l E n)
  let r := Ψ (finiteLine l E T n) (𝟙 (finiteLine l E T n))
  have hr (U : T.ProEtᵒᵖ) (z : ((roots l T).obj (op n)).obj.obj U) :
      r.hom.app U z =
        Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
          U.unop 1 z := by
    simpa only [one_smul, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hΨ (finiteLine l E T n) (𝟙 _) U 1 z
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  apply Sheaf.hom_ext
  ext U z
  exact (hr' U z).trans (hr U z).symm

/-- The canonical coefficient-linearization of finite roots on underlying sheaves. -/
def finiteRootMap (T : Scheme.{u}) (n : ℕ) :=
  (finiteRootMap_existsUnique l E T n).exists.choose

/-- Evaluation of c1 in the concrete finite Tate-line presentation, using the
exact single/shift comparisons and the pure-tensor-normalized line comparison. -/
def evaluatedChern {T : Scheme.{u}} (c : Chern l E T) (L : T.Pic) (n : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj (finiteLine l E T n))⟦(2 : ℤ)⟧ :=
  mapSingleArrow (SpTowerShriek.ev l E T n) (2 : ℤ) (firstChern l E c L) ≫
    ((DerivedCategory.singleFunctor _ 0).map (lineEvaluation l E c n).hom)⟦(2 : ℤ)⟧'

/-- Evaluate and forget an arrow: successive exact evaluation, the target-line comparison,
and forgetting scalars. -/
def forgetEvaluatedArrow {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [HasDerivedCategory.{w₃} H]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {Z : D} (e : F.obj Y ≅ Z)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj X)) ⟶
      ((DerivedCategory.singleFunctor H 0).obj (G.obj Z))⟦(2 : ℤ)⟧ :=
  mapSingleArrow G (2 : ℤ)
    (mapSingleArrow F (2 : ℤ) a ≫
      ((DerivedCategory.singleFunctor D 0).map e.hom)⟦(2 : ℤ)⟧')

/-- The finite boundary comparison: the coefficient-linear arrow after the integer quotient
agrees with the integral boundary after the root-to-tensor map. -/
def finiteBoundaryEquality {D : Type u₁} [Category.{v₁} D]
    {X X' Y Y' : D} (q : X ⟶ X') (r : Y ⟶ Y')
    {A B : Type v₁} (a : A) (beta : B) : Prop :=
  ∃ (a' : X' ⟶ Y') (beta' : X ⟶ Y),
    HEq a' a ∧ HEq beta' beta ∧ q ≫ a' = beta' ≫ r

/-- Compose an integral extension with the Kummer boundary. -/
def kummerComposite {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] (s : ShortComplex C) (hs : s.ShortExact)
    {X : C} (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)⟦(2 : ℤ)⟧ :=
  f ≫ hs.singleδ⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)

/-- Concrete finite Kummer normalization: forget scalars, evaluate on the integer
quotient, and obtain exactly the finite Kummer boundary followed by z -> 1 tensor z.
Source: Stacks 03PL. -/
def FiniteChernNormalization {T : Scheme.{u}} (c : Chern l E T) : Prop :=
  ∀ (L : T.Pic) (n : ℕ),
    let a := mapSingleArrow (finiteForget l E T n) (2 : ℤ) (evaluatedChern l E c L n)
    let beta := mapSingleArrow (abEvaluation T n) (2 : ℤ)
      (kummerComposite (C := Ab T)
        (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
        c.kummer.exact (lineBundleClass T L))
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n))⟦(2 : ℤ)⟧') a beta

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

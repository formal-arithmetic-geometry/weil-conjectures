/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Additive

/-! # Normalized tensor and derived adjunction data

Source: Stacks 06YN, 07A4, 07A6, 0B56, 0D6E
(blueprint: def-sf-coefficient-projection-adjunction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u a b v w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

section TensorAdjunction
variable {A : Type a} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasCoproducts.{0} A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{c} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive B] [HasCoproducts.{0} B] [HasDerivedCategory.{d} B]

/-- The actual signed total tensor on cochain complexes.
Source: Stacks 06YN (blueprint: def-sf-coefficient-projection-adjunction-data). -/
abbrev total : CochainComplex A ℤ × CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- Universal localization data for the existing unbounded tensor.
The comparison is a left-derived counit, not a free comparison isomorphism.
Source: Stacks 06YT, 07A4 (blueprint: def-sf-coefficient-projection-adjunction-data). -/
structure TensorLocalization (T : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    where
  comparison : (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ T ⟶ total ⋙ DerivedCategory.Q
  universal : T.IsLeftDerivedFunctor comparison
    ((HomologicalComplex.quasiIso A (.up ℤ)).prod (HomologicalComplex.quasiIso A (.up ℤ)))

/-- An ordinary module adjunction and its simultaneous derived adjunction.
The right functor is prescribed, and the chain-transpose equation fixes the derived
adjunction relative to its universal left and right comparisons.
Source: Stacks 07A6 (blueprint: def-sf-coefficient-projection-adjunction-data). -/
structure AdjointLocalization (R : B ⥤ A) [R.Additive]
    (RD : DerivedCategory B ⥤ DerivedCategory A)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RD) where
  ordinaryLeft : A ⥤ B
  [additive : ordinaryLeft.Additive]
  ordinaryAdjunction : ordinaryLeft ⊣ R
  left : DerivedCategory A ⥤ DerivedCategory B
  counit : DerivedCategory.Q ⋙ left ⟶
    ordinaryLeft.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : left.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso A (.up ℤ))
  adjunction : left ⊣ RD
  normalization : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj I),
    (adjunction.homEquiv _ _).symm (DerivedCategory.Q.map f ≫ η.app I) =
      counit.app P ≫ DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm f)

attribute [instance] AdjointLocalization.additive

/-- Normalization of strong tensor pullback by the ordinary adjunction and signed total.
`lax` is the actual direct-image tensor map, fixed separately on local pure tensors.
No invertibility of the resulting projection mate is imposed.
Source: Stacks 07A4, 0B56 (blueprint: def-sf-coefficient-projection-adjunction-data). -/
structure TensorAdjunction
    (TA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (TB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (tA : TensorLocalization TA) (tB : TensorLocalization TB)
    (R : B ⥤ A) [R.Additive] (RD : DerivedCategory B ⥤ DerivedCategory A)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RD)
    (lax : ∀ M N : B, R.obj M ⊗ R.obj N ⟶ R.obj (M ⊗ N))
    (F : AdjointLocalization R RD η) where
  ordinary : ∀ M N : A,
    F.ordinaryLeft.obj (M ⊗ N) ≅ F.ordinaryLeft.obj M ⊗ F.ordinaryLeft.obj N
  ordinary_naturality : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
    F.ordinaryLeft.map (f ⊗ₘ g) ≫ (ordinary M' N').hom =
      (ordinary M N).hom ≫ (F.ordinaryLeft.map f ⊗ₘ F.ordinaryLeft.map g)
  ordinary_unit : ∀ M N : A,
    F.ordinaryAdjunction.homEquiv _ _ (ordinary M N).hom =
      (F.ordinaryAdjunction.unit.app M ⊗ₘ F.ordinaryAdjunction.unit.app N) ≫
        lax (F.ordinaryLeft.obj M) (F.ordinaryLeft.obj N)
  comparison : TA ⋙ F.left ≅ (F.left.prod F.left) ⋙ TB
  representative : ∀ P Q : CochainComplex A ℤ,
    comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        F.left.map (tA.comparison.app (P, Q)) ≫ F.counit.app (total.obj (P, Q)) =
      TB.map (Prod.mkHom (F.counit.app P) (F.counit.app Q)) ≫
        tB.comparison.app
          ((F.ordinaryLeft.mapHomologicalComplex (.up ℤ)).obj P,
            (F.ordinaryLeft.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map
          (tensorPullbackTotal F.ordinaryLeft ordinary ordinary_naturality P Q)

/-- The counit-defined projection mate, in precisely the recorded orientation.
Source: Stacks 0B56 (blueprint: def-sf-coefficient-projection-adjunction-data). -/
def projection
    {TA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A}
    {TB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B}
    {tA : TensorLocalization TA} {tB : TensorLocalization TB}
    {R : B ⥤ A} [R.Additive] {RD : DerivedCategory B ⥤ DerivedCategory A}
    {η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RD}
    {lax : ∀ M N : B, R.obj M ⊗ R.obj N ⟶ R.obj (M ⊗ N)}
    {F : AdjointLocalization R RD η} (m : TensorAdjunction TA TB tA tB R RD η lax F)
    (V : DerivedCategory B) (L : DerivedCategory A) :
    TA.obj (RD.obj V, L) ⟶ RD.obj (TB.obj (V, F.left.obj L)) :=
  derivedProjectionFormulaMate F.left RD F.adjunction TA TB m.comparison V L
end TensorAdjunction


/-- The derived-unit transformation on cochain complexes.
Source: Stacks 079P (blueprint: def-sf-coefficient-projection-adjunction-data). -/
def rightUnit {A : Type a} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category.{c} B] [Abelian B] [HasDerivedCategory.{d} B]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app P := F.rightDerivedFunctorUnitQ P
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

/-- The unit equation for derived direct-image composition, written before site
specialization so that no concrete module functor is unfolded to state it.
Source: Stacks 0D6E (blueprint: def-sf-coefficient-projection-adjunction-data). -/
def DerivedCompositionNormalization
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type b} [Category.{c} B] [Abelian B] [HasDerivedCategory.{d} B]
    {C : Type e} [Category.{f} C] [Abelian C] [HasDerivedCategory.{g} C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] (H : A ⥤ C) [H.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory B ⥤ DerivedCategory C)
    (RH : DerivedCategory A ⥤ DerivedCategory C)
    (εF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (εG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (εH : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)
    (ordinary : F ⋙ G ≅ H) (derived : RF ⋙ RG ≅ RH) : Prop :=
  ∀ I : CochainComplex A ℤ,
    εG.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫ RG.map (εF.app I) ≫
        derived.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (F := F) (G := G) ordinary (.up ℤ)).hom.app I) ≫
        εH.app I


/-- Transport of a strong tensor comparison through the uniquely adjoint-compatible
identification of two left adjoints. This introduces no freely chosen tensor map.
Source: Stacks 07A4, 07A6 (blueprint: def-sf-coefficient-projection-adjunction-data). -/
def transportTensor {A : Type a} [Category.{v} A] {B : Type b} [Category.{c} B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {F G : A ⥤ B} (e : F ≅ G)
    (μ : TA ⋙ F ≅ (F.prod F) ⋙ TB) : TA ⋙ G ≅ (G.prod G) ⋙ TB :=
  Functor.isoWhiskerLeft TA e.symm ≪≫ μ ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) TB


end WeilConjectures.CoefProjectionEvaluation

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare

/-! # Scalar pullback square coherence

Source: Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapHomotopyCategory
  AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private instance module_tensor_two
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B : GradedObject ℤ (Modules R T)) : A.HasTensor B := by
  intro j
  infer_instance

private instance module_tensor_four
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C E : GradedObject ℤ (Modules R T)) :
    GradedObject.HasTensor₄ObjExt A B C E := by
  intro i j
  infer_instance

private instance module_tensor_left
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

private instance module_tensor_right
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

private instance module_kflat_derivable
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure
      (HomotopyCategory.quasiIso (Modules R T) (.up ℤ)).localizerMorphismKFlat := by
  infer_instance

private instance extension_kflat (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u}) :
    (extension φ T).PreservesKFlatQuasiIso := by
  exact Mod.preservesKFlatQuasiIso (coefficientMap φ T)

/-- The canonical geometric compositor with the scalar interface exposed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackComposition
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    L R (h ≫ k) ≅ L R k ⋙ L R h := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp R h k

/-- The canonical geometric pullback square with the scalar interface exposed.
Source: Stacks 07A7 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    L R c ⋙ L R f' ≅ L R f ⋙ L R a :=
  (scalarPullbackComposition R f' c).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ L R h) sq.toCommSq.w.symm) ≪≫
    scalarPullbackComposition R a f

set_option maxHeartbeats 300000 in
-- Specializing the categorical lemma searches instances on categories of module objects.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStar Mod.extendScalars
  CondensedRing.upperStarComp CondensedRing.pullIso
  scalarCounit pullCounit

end AlgebraicGeometry.ProEtale.QuotientChange

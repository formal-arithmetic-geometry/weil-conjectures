/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedLeftAdjoint
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Direct image and evaluation of strict coefficient systems

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and Lemma 4.10, printed pp. 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

The index `n` denotes the positive exponent `n+1`. All systems, evaluation functors,
scalar extensions and adjoint transitions are the recorded coefficient-evaluation
interface. The structures below specify the geometric lifts and the comparison,
including their normalizations; they are conclusions, not hypotheses of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d a b av bv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

universe p pv q qv

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

section DerivedAdjunction
variable {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)

end DerivedAdjunction

section AbstractImages
universe ga gb gal gbl gav gbv galv gblv
variable {A : Type ga} [Category.{gav} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type gb} [Category.{gbv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {MA : ℕ → Type gal} [∀ n, Category.{galv} (MA n)] [∀ n, Abelian (MA n)]
  [∀ n, HasDerivedCategory.{d} (MA n)]
  {MB : ℕ → Type gbl} [∀ n, Category.{gblv} (MB n)] [∀ n, Abelian (MB n)]
  [∀ n, HasDerivedCategory.{d} (MB n)]

variable
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (Flevel : ∀ n, MA n ⥤ MB n) (Glevel : ∀ n, MB n ⥤ MA n)
    [∀ n, (Flevel n).Additive] [∀ n, (Glevel n).Additive]
    (adjLevel : ∀ n, Flevel n ⊣ Glevel n)
    (eA : ∀ n, A ⥤ MA n) (eB : ∀ n, B ⥤ MB n)
    [∀ n, (eA n).Additive] [∀ n, (eB n).Additive]
    (EA : ∀ n, DerivedCategory A ⥤ DerivedCategory (MA n))
    (EB : ∀ n, DerivedCategory B ⥤ DerivedCategory (MB n))
    (factorsA : ∀ n, DerivedCategory.Q ⋙ EA n ≅
      (eA n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (factorsB : ∀ n, DerivedCategory.Q ⋙ EB n ≅
      (eB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (alpha : ∀ n, F ⋙ eB n ≅ eA n ⋙ Flevel n)

end AbstractImages

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

attribute [instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

namespace CoefficientSystemDerivedImage
variable {O ell L V adj}
  {S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj}
  {PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)}
  {PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)}

end CoefficientSystemDerivedImage

end SheafOfModules

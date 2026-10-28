/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import Sheaf.SixFunctors.DualizingOpenMate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
public import Sheaf.CategoryTheory.CounitMateTransport
import all Sheaf.Paper.ExceptionalCoefficientComparison
import all Sheaf.SixFunctors.DualizingOpenMate
import all Sheaf.SixFunctors.CoefficientDualizingClosedAssembly
import Sheaf.SixFunctors.OpenClosedCompactScalar
import all Sheaf.CategoryTheory.CounitMateTransport

/-! # Counit normalization through an open and a closed chart

Source: the finite dualizing proof, paragraphs 2--3
(blueprint: dualizing-open-closed-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver in
theorem scalarMap_eq_globalMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] :
    ExceptionalCoefficients.dualizingScalarMap φ f =
      DualizingOpenMate.globalMate φ (HasCompactification.compactification f)
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f) := by
  rw [ExceptionalCoefficients.dualizingScalarMap_eq]
  unfold ExceptionalCoefficients.mateMap DualizingOpenMate.globalMate
  exact transpose_three_maps
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f)
    (X := (scalarExtension φ X).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
        (𝟙_ (DerivedCategoryModule A S))))
    (ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
        (𝟙_ (DerivedCategoryModule A S))))
    ((scalarExtension φ S).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app
        (𝟙_ (DerivedCategoryModule A S))))
    (ExceptionalCoefficients.unitIso φ S).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The closed coefficient mate in the ordinary direct-image adjunction.
Its inverse direct-image comparison exists by proper finite coefficient extension.
Source: finite dualizing proof, paragraph 3
(blueprint: dualizing-open-closed-mate-normalization). -/
def closedDualizingCoefficientMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] (M : DerivedCategoryModule A P) :
    (scalarExtension φ V).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) i).obj M) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) i).obj
        ((scalarExtension φ P).obj M) :=
  let a := rightDerivedLowerStarUpperShriekAdjunctionOfIsProper A i
  let b := rightDerivedLowerStarUpperShriekAdjunctionOfIsProper B i
  let N := (rightDerivedUpperShriek (ModuleCat.{u + 1} A) i).obj M
  letI : IsIso ((scalarMate φ i).app N) := (properFiniteCoefficientExtension φ i).1 N
  b.homEquiv ((scalarExtension φ V).obj N) ((scalarExtension φ P).obj M)
    (inv ((scalarMate φ i).app N) ≫
      (scalarExtension φ P).map (a.counit.app M))


end AlgebraicGeometry.Etale

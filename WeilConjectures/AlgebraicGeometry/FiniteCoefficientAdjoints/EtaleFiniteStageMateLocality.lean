/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateProperty
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineProjectionCoefficientMate
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteAdjointMateCompatibility
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.AlgebraicGeometry.Sf.SfAffineChartFactorizationGluing
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-! # Finite affine chart reduction of the finite-stage mate

Source: ordinary etale reduction-exceptional argument and the parent mate proof.
(blueprint: lem-pur-etale-finite-stage-mate-locality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- The unbounded compactification scalar squares give the chosen compositor square.
No boundedness assumption is needed here. -/
private theorem scalar_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : Etale.DerivedCategoryModule A X) :
    (Etale.scalarExtension φ Z).map
        ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      (Etale.compactScalarChosenMap φ (f ≫ g)).app M =
    (Etale.compactScalarChosenMap φ g).app
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
        ((Etale.compactScalarChosenMap φ f).app M) ≫
      (Etale.unboundedEtaleLowerShriekCompIso B f g).hom.app
        ((Etale.scalarExtension φ X).obj M) := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    e.restrict
  apply Etale.composition_scalar_transport
    (Etale.scalarExtension φ X) (Etale.scalarExtension φ Y) (Etale.scalarExtension φ Z)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (Etale.rightDerivedLowerShriekIso A e.restrict) (Etale.rightDerivedLowerShriekIso A d)
    (Etale.rightDerivedLowerShriekIso A (d.comp e))
    (Etale.rightDerivedLowerShriekIso B e.restrict) (Etale.rightDerivedLowerShriekIso B d)
    (Etale.rightDerivedLowerShriekIso B (d.comp e))
    (Etale.unboundedEtaleLowerShriekCompIso A f g)
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (Etale.unboundedEtaleLowerShriekCompIso B f g)
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (Etale.unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (Etale.unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (Etale.compactScalarChosenMap φ f) (Etale.compactScalarMap φ e.restrict)
    (Etale.compactScalarChosenMap φ g) (Etale.compactScalarMap φ d)
    (Etale.compactScalarChosenMap φ (f ≫ g))
    (Etale.compactScalarMap φ (d.comp e)) M
  · exact Etale.ordinaryChartCompactificationScalar φ e.restrict
      (HasCompactification.compactification f) M
  · exact Etale.ordinaryChartCompactificationScalar φ d
      (HasCompactification.compactification g) (F.obj M)
  · exact Etale.ordinaryChartCompactificationScalar φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M
  · exact Etale.ordinaryChartCompactTowerScalar φ f g d e M

private theorem mate_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : Etale.DerivedCategoryModule A Z) :
    (Etale.scalarExtension φ X).map
        ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
          ((Etale.rightDerivedUpperShriekAdjunction A f).comp
            (Etale.rightDerivedUpperShriekAdjunction A g))
          (Etale.unboundedEtaleLowerShriekCompIso A f g)).hom.app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f
        ((Etale.rightDerivedUpperShriek A g).obj K) ≫
      (Etale.rightDerivedUpperShriek B f).map
        (Etale.ExceptionalCoefficients.mateMap φ g K) =
    Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K ≫
      (conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
        ((Etale.rightDerivedUpperShriekAdjunction B f).comp
          (Etale.rightDerivedUpperShriekAdjunction B g))
        (Etale.unboundedEtaleLowerShriekCompIso B f g)).hom.app
          ((Etale.scalarExtension φ Z).obj K) := by
  have hc := scalar_composition φ f g
    ((Etale.rightDerivedUpperShriek A (f ≫ g)).obj K)
  rw [← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ g,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ (f ≫ g)] at hc
  exact finiteMate_composition
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A g)
    (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction B f)
    (Etale.rightDerivedUpperShriekAdjunction B g)
    (Etale.rightDerivedUpperShriekAdjunction B (f ≫ g))
    (Etale.unboundedEtaleLowerShriekCompIso A f g)
    (Etale.unboundedEtaleLowerShriekCompIso B f g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ (f ≫ g)) K _ _ _
    (Etale.ExceptionalCoefficients.mateMap_counit φ f _)
    (Etale.ExceptionalCoefficients.mateMap_counit φ g K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ (f ≫ g) K) hc

section StageProperty
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {s t : Stage l E} (a : Arrow s t)

end StageProperty

end AlgebraicGeometry.FiniteCoefficientAdjoints

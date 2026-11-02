/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-! # Tensor and dual fibres of condensed Weil sheaves

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations).

All modules, point sections and local operators are the recorded condensed constructions.
The comparison maps are normalized by tensoring sections and evaluating functionals.
Finite direct sums are represented by finite products in the abelian module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedFibreLinearCurrent

open NativeCondensedModule

/-- Tensor the two Weil data using the inverse pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (F L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (F.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) _ _).symm ≪≫
        tensorIso F.str L.str)

/-- The ordinary internal dual, with its evaluation-transpose contragredient datum.
Source: latest blueprint, realified-kernel proof Step 1, and the contragredient composite
of sk-def-sf-weil-complexes (blueprint: lem-fd-condensed-fibre-linear-operations). -/
def dualWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk ((ihom L.carrier).obj (𝟙_ (Modules l T)))
    (Functor.Monoidal.ihomObjIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) L.carrier (𝟙_ _) ≪≫
      (ihom _).mapIso
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso L.str.symm.op).app (𝟙_ _))

/-- A finite direct sum with the direct sum of the Weil data, using the finite product model.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def sumWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T) (n : ℕ)
    (F : Fin n → IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (∏ᶜ fun i ↦ (F i).carrier)
    (PreservesProduct.iso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      (fun i ↦ (F i).carrier) ≪≫ Pi.mapIso (fun i ↦ (F i).str))

/-- The section obtained by tensoring two sections and applying the pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorSection (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (v : fibre l D F z) (w : fibre l D L z) : fibre l D (F ⊗ L) z :=
  (λ_ (𝟙_ (Modules l (Spec (.of D.k))))).inv ≫ (v ⊗ₘ w) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) F L

/-- Evaluation of a fibre functional on a fibre vector, with the coefficient-unit comparison.
Source: latest blueprint, realified-kernel proof Step 1
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def evaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (f : fibre l D ((ihom L).obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    ULift.{u + 1} (PadicAlgCl l) :=
  (NativeCondensedModule.pointSectionsUnitIso l D.k).inv
    ((NativeCondensedModule.pointSections l D.k).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
        ((ihom.ev L).app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)).inv)
      (tensorSection l D z L _ v f))

set_option maxHeartbeats 800000 in
-- The dependent fibre tensor-section equation needs this elaboration budget.
end WeilConjectures.CondensedFibreLinearCurrent

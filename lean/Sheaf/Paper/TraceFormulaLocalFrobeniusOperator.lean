/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.IteratedWeilMap
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The finite-coefficient local Frobenius operator

Source: Weil conjectures blueprint, main-20261015, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators).

This supplements the recorded etale cohomological operator with the local operator
on the intrinsic pro-etale ordinary-module complex, retaining rho, the specified kappa,
and the iterated Weil isomorphism separately. Point evaluation is exactly the ambient
functor whose constructible restriction is `pointFiniteFibre`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- Exact evaluation at the point, with precisely the localization universe of the
recorded point fibre. The sheaf category retains its standard larger localization.
Source: blueprint def-trf-frobenius-operators, clause 2, and def-weil-finite-coefficient-point
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalSections (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  @Functor.mapDerivedCategory
    (proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections T.datum.k T.coefficientRing)
    (pointFiniteSectionsAdditive T.datum.k T.coefficientRing)
    (pointFibreFiniteLimits T.datum T.coefficientRing)
    (pointFibreFiniteColimits T.datum T.coefficientRing)

/-- The stalk complex `Fib_s(Lz^*K)`, using exact sections at `s`.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFibre (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :=
  proEtaleConstantRingDerivedPullback T.coefficientRing z ⋙
    T.finiteLocalSections

/-- The canonical fixed-point identification rho. Only equality of the scheme-Frobenius
translate is used; raw geometric Galois Frobenius need not fix z.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalRho (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :=
  T.finiteLocalSections.mapIso
    (eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      hz.symm) ≪≫
      (proEtaleConstantRingPullbackComposition z
        (T.datum.schemeFrobeniusIterate T.X₀ m) T.coefficientRing).symm.app K.obj.carrier)

/-- The local geometric Frobenius `Fib_s(Lz^* phi^[m])` after `Fib_s(Lz^* kappa)`
after rho, on the actual ordinary-module fibre complex. This formula applies to the
scalar-extended point of every rational point; no arbitrary transport is supplied.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    (T.finiteLocalFibre z).obj K.obj.carrier ⟶ (T.finiteLocalFibre z).obj K.obj.carrier :=
  (T.finiteLocalRho K m z hz).hom ≫
    (T.finiteLocalFibre z).map (T.iteratedWeilSchemeFrobenius K m hm).hom

end WeilConjectures.TraceFormulaCoefficientConventions

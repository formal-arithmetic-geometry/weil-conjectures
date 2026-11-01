/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.ZetaWeil.CondensedLocalReturn.CondensedLocalReturn
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ZetaSeries
import WeilConjectures.CategoryTheory.Exact.ExactDerivedCohomologyCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Strict-pair heart realization and coherent local return powers

Source: latest blueprint, sec-zeta-weil/sk-thm-weil-final/prop-every-iterate-trace,
local-operator and choice-independence clauses
(blueprint: lem-zl-iterate-local-trace-choice-independence).

## Main definitions and statement

- `heartModule`, `cohomologyIso`: the induced heart pair and canonical fibre comparison.
- `nativeSingleIso`, `strictSingleStructure`, `NativeSingleCompatibility`: degree zero.
- `IsLift`, `HeartAssertions`, `ReturnAssertions`: the explicit conclusion predicates.
- `ReturnEquations` and the four lift-comparison predicates: the return clauses in full.
- `LinearReturnConjugacy`: the displayed intertwining equation on abstract modules.
- `strictWeil_localReturn_powers`: heart realization, coherent powers and trace independence.

Only the degree-zero heart realization is used. All operators are the actual condensed
module returns and their exact derived functors, with the canonical cohomology comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace WeilConjectures.StrictWeilLocalReturn
open CondensedLocalReturn
open AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.Endofunctor.IsoAlgebra

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The displayed linear intertwining equation, with abstract fibre modules.
Source: node statement, displayed T_j equation
(blueprint: lem-zl-iterate-local-trace-choice-independence). -/
@[irreducible] def LinearReturnConjugacy {A B : ModuleCat.{u + 1} (Γ Λ)}
    (f : End A) (g : End B) : Prop :=
  ∃ T : A ≅ B, f ≫ T.hom = T.hom ≫ g

end WeilConjectures.StrictWeilLocalReturn

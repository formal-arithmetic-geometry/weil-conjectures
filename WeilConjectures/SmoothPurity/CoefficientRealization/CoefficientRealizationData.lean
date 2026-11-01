/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.ConstantPurityFrobeniusSquare
public import WeilConjectures.SmoothPurity.NativePairCohomology.NativePairCohomology
public import WeilConjectures.WeilSheaf.Constant

/-! # Input data for cohomology of an equivariant coefficient realization

The constructions accept a realization as an argument. They do not choose data from
an existence theorem. In particular, every cohomology functor below is the actual
composite of ordinary realization, transport of the action, and ordinary cohomology.

(blueprint: def-sf-coefficient-realization-cohomology-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.CoefficientRealization

variable (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

/-- The ordinary coefficient category, before imposing a Frobenius structure. -/
abbrev Source := generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
  P.coefficients.Qbar (P.field.geometricFiber X₀).left

/-- The coefficient Frobenius-pair category. -/
abbrev Pairs := IsoAlgebra (sourceFrobenius P.field P.coefficients.l
  P.coefficients.different P.coefficients.Qbar X₀)

/-- Ordinary native adic sheaves on the native geometric fibre. -/
abbrev Native := ProEtale.AdicSheaf P.coefficients.l
  (X₀.left ↘ Spec (.of P.field.k₀)).geometricFiber

/-- The data needed to realize cohomology: an additive ordinary realization with
shift-compatible Frobenius, constructible cohomology and scalar-unit normalization. -/
structure Data where
  functor : Source P X₀ ⥤ DerivedCategory (Native P X₀)
  [additive : functor.Additive]
  [shift : functor.CommShift ℤ]
  frobenius : functor ⋙
      (WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l X₀.left).mapDerivedCategory ≅
    sourceFrobenius P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar X₀ ⋙ functor
  [frobeniusShift : NatTrans.CommShift frobenius.hom ℤ]
  constructible : ∀ (K : Source P X₀) (n : ℤ),
    ProEtale.IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor (Native P X₀) n).obj (functor.obj K))
  unit : Nonempty
    ((NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left).obj
        (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)) ≅
      (IsoAlgebra.mapOfNatIso frobenius).obj
        (constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
          P.coefficients.different X₀ P.coefficients.Qbar))

attribute [instance] Data.additive Data.shift Data.frobeniusShift

/-- Transport the Frobenius structure through the given ordinary realization. -/
def pairs (R : Data P X₀) :
    Pairs P X₀ ⥤ NativePairCohomology.Pairs P.field.k₀ P.coefficients.l X₀.left :=
  IsoAlgebra.mapOfNatIso R.frobenius

/-- The actual composite before restricting its image to constructible Weil sheaves. -/
def pairCohomology (R : Data P X₀) (n : ℤ) :
    Pairs P X₀ ⥤ ProEtaleWeilSheaf P.field.k₀ P.coefficients.l X₀.left :=
  pairs P X₀ R ⋙ NativePairCohomology.homology P.field.k₀ P.coefficients.l X₀.left n

omit [IsSeparated X₀.hom] in
/-- Cohomology of a constructible coefficient object remains constructible. -/
theorem pairCohomology_mem (R : Data P X₀) (n : ℤ) (K : Pairs P X₀) :
    WeilSheaf.objectProperty P.field.k₀ P.coefficients.l X₀.left
      ((pairCohomology P X₀ R n).obj K) :=
  R.constructible K.carrier n

/-- Cohomology with its realized action, restricted to the native constructible category. -/
def cohomology (R : Data P X₀) (n : ℤ) :
    Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left :=
  (WeilSheaf.objectProperty P.field.k₀ P.coefficients.l X₀.left).lift
    (pairCohomology P X₀ R n) (pairCohomology_mem P X₀ R n)

end WeilConjectures.CoefficientRealization

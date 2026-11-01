/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-scalar-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Bundle a recorded coefficient without changing its internal ring.
Source: scalar-six coefficient list (blueprint: def-pur-transport-scalar-coordinates). -/
abbrev Coefficient.bundled (c : Coefficient ell) : ScalarSixRing.{u} := ⟨c.obj ell⟩

/-- Scalar extension of the first Tate line, fixed by scalar associativity.
Source: coefficient compatibility (blueprint: def-pur-transport-scalar-coordinates). -/
def scalarFirst {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :=
  (Mod.extendScalarsComp (coefficientMap (c.integralMap ell) X)
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).symm.app (tateModule X ell) ≪≫
  (Mod.extendScalarsIsoOfEq
    ((coefficientMap_comp (c.integralMap ell) a.hom.hom X).symm.trans
      (congrArg (fun k ↦ coefficientMap k X) ha))).app (tateModule X ell)

/-- The canonical tensorator on unbounded derived extension of scalars.
The ordinary tensorator is fixed on balanced tensors; its derived structure is
fixed on K-flat representatives. Source: Stacks 07A4
(blueprint: def-pur-transport-scalar-coordinates). -/
def scalarTensor {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (K L : c.derived ell X) :=
  let φ : condensedRingObj (c.obj ell) X ⟶ condensedRingObj (c'.obj ell) X :=
    coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
  letI := (Mod.exists_extendScalarsMonoidal φ).choose
  letI := Mod.extendScalars_preservesFlat φ
  letI := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  Functor.Monoidal.μIso (Mod.extendScalars φ).leftDerivedFunctor K L

/-- Derived coefficient-line map obtained as the adjunct of the ordinary line map.
This construction needs no flatness assumption on a coefficient ring homomorphism.
Source: coefficient compatibility (blueprint: def-pur-transport-scalar-coordinates). -/
def scalarLineZero {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (d : ℕ)
    (e : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
      (c.line ell X d) ≅ c'.line ell X d) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X d))
    ((DerivedCategory.singleFunctor _ 0).obj (c'.line ell X d)) |>.symm <|
    (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction
        (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).homEquiv _ _ e.hom) ≫
    ((Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1})
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
        a.hom.hom X)).mapDerivedCategorySingleFunctor 0).inv.app (c'.line ell X d)

/-- Shift the specified degree-zero scalar line map by the fixed derived-adjunction
shift comparison. Source: coefficient compatibility
(blueprint: def-pur-transport-scalar-coordinates). -/
def scalarLineMap {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (d : ℕ)
    (e : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
      (c.line ell X d) ≅ c'.line ell X d) :=
  (Functor.commShiftIso (scalarSixChange a X)
    (self := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).leftAdjointCommShift ℤ)
      (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map (scalarLineZero ell a X d e)

end AlgebraicGeometry.ProEtale.PurityTransport

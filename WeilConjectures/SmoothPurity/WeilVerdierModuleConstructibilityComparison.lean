/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Weil internal Hom and equivariance of evaluation

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/`
`sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/`
`sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`, internal-Hom sentences
and the final evaluation paragraph.
(blueprint: lem-sf-weil-verdier-module-constructibility-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures

open MonoidalClosed

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]

/-- The specified evaluation transpose for geometric-automorphism pullback, using the
recorded strong monoidal structure and the recorded derived internal Hom.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/`
`sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/`
`sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`, internal-Hom sentences
(blueprint: lem-sf-weil-verdier-module-constructibility-comparison). -/
def weilVerdierHomComparison
    (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj (((derivedHom Λ X).obj (op K)).obj L) ⟶
      ((derivedHom Λ X).obj (op (((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj K))).obj
      (((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj L) :=
  (Functor.LaxMonoidal.ihomComparison ((CondensedRing.upperStar Λ g).leftDerivedFunctor)
      K).natTrans.app L

/-- Transport the recorded strict-pair structure from exact termwise pullback to total
left derived pullback along its canonical comparison isomorphism.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/`
`sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/`
`sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`, internal-Hom sentences
(blueprint: lem-sf-weil-verdier-module-constructibility-comparison). -/
def weilVerdierDerivedStructure (K : condensedStrictWeilComplex Λ g) :
    ((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj K.obj.carrier ≅ K.obj.carrier :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K.obj.carrier ≪≫ K.obj.str

/-- The canonical Hom Weil arrow: compare pullback with Hom, precompose by the inverse
of the first transported Weil isomorphism, and postcompose by the second transported
Weil isomorphism. The inputs belong to the recorded strict Weil category.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/`
`sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/`
`sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`, inverse in the contravariant
argument (blueprint: lem-sf-weil-verdier-module-constructibility-comparison). -/
def weilVerdierHomTheta (K L : condensedStrictWeilComplex Λ g) :
    ((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj
      (((derivedHom Λ X).obj (op K.obj.carrier)).obj L.obj.carrier) ⟶
      ((derivedHom Λ X).obj (op K.obj.carrier)).obj L.obj.carrier :=
  weilVerdierHomComparison Λ g K.obj.carrier L.obj.carrier ≫
    ((derivedHom Λ X).map (weilVerdierDerivedStructure Λ g K).inv.op).app
      (((CondensedRing.upperStar Λ g).leftDerivedFunctor).obj L.obj.carrier) ≫
    ((derivedHom Λ X).obj (op K.obj.carrier)).map (weilVerdierDerivedStructure Λ g L).hom

end Ambient

section Geometric

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [hsep : IsSeparated Y₀.hom] (c : WeilCoefficient ell)

include hell hsep

set_option maxHeartbeats 1600000 in
-- The expanded geometric/coefficient expressions require extra typeclass elaboration steps.
end Geometric

end WeilConjectures

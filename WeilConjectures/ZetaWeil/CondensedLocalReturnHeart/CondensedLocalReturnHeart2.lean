/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Cohomology hearts and local returns with condensed coefficients

Source: latest blueprint, `prop-every-iterate-trace`, local operators and its opening
proof sentence, expanded by the cohomology-heart comparison
(blueprint: lem-zl-local-return-heart-part).

All objects are modules over the actual pulled-back condensed coefficient ring.
The fibre comparison is the composite of the normalized exact-functor comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedLocalReturnHeart

open CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The same strict structure on the total left derived inverse image.
Source: Lg^*=g^* in the setup (blueprint: lem-zl-local-return-heart-part). -/
def derivedStructure {T : Scheme.{u}} (g : T ⟶ T) [IsIso g]
    (K : condensedStrictWeilComplex Λ g) :
    (L Λ g).obj K.obj.carrier ≅ K.obj.carrier :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K.obj.carrier ≪≫
    K.obj.str

/-- Reparametrize the geometric point before taking derived sections, by insertion
and the inverse pullback compositor. This is the canonical map used in the return.
Source: clause 2 (blueprint: lem-zl-local-return-heart-part). -/
def derivedReparam {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (z : Spec (.of k) ⟶ T) (β : End (Spec (.of k))) (K : D Λ T) :=
  (insertion Λ β).app ((L Λ z).obj K) ≪≫
    (Γ Λ (Spec (.of k))).mapIso
      ((CondensedRing.leftDerivedUpperStarComp Λ β z).app K).symm

section SingleCompatibility

universe uA vA wA uB vB wB

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end SingleCompatibility

set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
set_option maxHeartbeats 1600000 in
-- Kernel conversion compares independently synthesized concrete module-category instances.
end WeilConjectures.CondensedLocalReturnHeart

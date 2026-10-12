/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso

/-! # Restriction stability of a local chain map

Source: lem-pc-perfect-locus, finite matrix extension argument, expanded in
lem-pc-finite-free-stalk-chain-map-lift.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift-restrict)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Restriction stability of a local chain map.

Source: lem-pc-finite-free-stalk-chain-map-lift, proof step 4, expanding
lem-pc-perfect-locus's extension of the finite calculation. The comparison uses
Mathlib's restrictFunctorComp, restrictFunctorIsoPullback, pullbackComp, and
pseudofunctor_associativity.

Proof: Fix V <= U containing y and let j : V.toScheme -> U.toScheme be the open
inclusion. Let R_U, R_V and R_j denote termwise restriction. The identity
j >> U.ι = V.ι and restrictFunctorComp give a natural isomorphism
C : R_V ~= R_U >> R_j. Define
fV = C(P).hom >> R_j.map fU >> C(Q).inv.
Write S_U and S_V for the corresponding termwise stalk pullbacks. Since the
map Spec O_{Y,y} -> U factors through V, restriction followed by stalk pullback
gives a natural isomorphism D : R_j >> S_V ~= S_U (with the same source Spec).
The composite S_V.mapIso C(M) followed by D(R_U M) equals E_V(M) followed by
E_U(M).symm. Indeed replace each restriction by pullback using
restrictFunctorIsoPullback, use pullback composition, and apply
pseudofunctor_associativity to the three scheme maps from the stalk through V
and U to Y. The equality of their composites is fromSpecStalkOfMem_ι;
compatibility of restrictFunctorIsoPullback with composition follows from the
uniqueness of left adjoints to the composite pushforward, or its adjunction units.
Naturality of D gives
S_V.map fV = E_V(P).hom >> E_U(P).inv >> S_U.map fU >>
  E_U(Q).hom >> E_V(Q).inv.
Substitute the hypothesis h and cancel the E_U inverse/hom pairs to obtain the
required equation. For V = U this is the same cancellation; zero complexes need
no additional hypotheses. No boundedness or finite freeness is used.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift-restrict) -/
theorem restrict_chainMap_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ) (y : Y) (U : Y.Opens)
    (hyU : y ∈ U)
    (f : ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P ⟶
      ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q)
    (fU : ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (h : ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map fU =
      ((stalkRestrictionComplexIso U y hyU).app P).hom ≫ f ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).inv) :
    ∀ (V : Y.Opens) (hyV : y ∈ V), V ≤ U →
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let eP := (stalkRestrictionComplexIso V y hyV).app P
      let eQ := (stalkRestrictionComplexIso V y hyV).app Q
      ∃ (fV : R.obj P ⟶ R.obj Q), S.map fV = eP.hom ≫ f ≫ eQ.inv := by sorry
end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback

/-! # Transport of a bottom chain model through derived pullback

Source: Stacks Project, Tags 06YD, 06YJ and 08DW.
(blueprint: lem-sc-bottom-chain-model-pullback-transport).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Pulling back a local strictly perfect chain representative gives a local
cohomology square with the pulled-back chain map. Zero bottom differentials
and an invertible bottom component persist. This asserts the square for the
specified arrow, rather than an unrelated isomorphism between its endpoints.

Source: Stacks Project, Tags 06YD and 06YJ (termwise flat pullback),
08DW (restriction compatibility); Tag 0BDL, canonical pullback clause.
(blueprint: lem-sc-bottom-chain-model-pullback-transport).

Proof: Let V be the inverse image of U. The point hypothesis gives y in V.
Use the equivalence of module sheaves on the localized open site with modules
on U.toScheme to transport A, B and alpha there. Strictly perfect terms are
retracts of finite free modules, hence flat, and the complexes are bounded
above. The flat-complex derived-pullback counit therefore computes their
pullbacks termwise along V.toScheme -> U.toScheme. Use this one natural counit
for both complexes: its naturality transports the given square for f to the
termwise pulled-back alpha. Ordinary tensor pullback preserves zero objects,
zero differentials and isomorphisms. Thus the resulting P and Q have zero
term in degree -1 and zero differential 0 -> 1, and beta.f 0 is invertible.
Transport P and Q back to the localized site over V. Exact open restriction
commutes with homology, and derived pullback commutes with open restriction.
Apply homology to the naturality square and compose with these comparison
isomorphisms and the homology factorization of the localization Q. This gives
eP, eQ and the displayed equality for the restriction of H0(Lk*f).
The constructions preserve zero objects also on the empty open and in rank zero. -/
theorem bottom_chain_model_pullback_transport
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (X Z : schemeDerivedCategory S) (f : X ⟶ Z) (U : S.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect S U A) (hB : IsStrictlyPerfect S U B)
    (hAzero : ∀ i : ℤ, i ≠ 0 → IsZero (A.X i))
    (hBnegative : ∀ i : ℤ, i < 0 → IsZero (B.X i))
    (hBzero : B.d 0 1 = 0) (α : A ⟶ B) (hα : IsIso (α.f 0))
    (eA : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj X ≅
          DerivedCategory.Q.obj A)
    (eB : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj Z ≅
          DerivedCategory.Q.obj B)
    (hsquare : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.map f ≫ eB.hom =
          eA.hom ≫ DerivedCategory.Q.map α)
    {Y : Scheme.{u}} (k : Y ⟶ S) (y : Y) (hy : k.base y ∈ U) :
    ∃ V : Y.Opens, y ∈ V ∧
      ∃ P Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) ℤ,
        IsZero (P.X (-1)) ∧ IsZero (Q.X (-1)) ∧
        P.d 0 1 = 0 ∧ Q.d 0 1 = 0 ∧
        ∃ β : P ⟶ Q, IsIso (β.f 0) ∧
          ∃ (eP : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback k).obj X)).over V ≅ P.homology 0)
            (eQ : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback k).obj Z)).over V ≅ Q.homology 0),
            (((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
                ((derivedPullback k).map f)).over V) ≫ eQ.hom =
                  eP.hom ≫ HomologicalComplex.homologyMap β 0 := by sorry

end AlgebraicGeometry.Scheme

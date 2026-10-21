/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeInvariantForgetting
public import Sheaf.CategoryTheory.RelativeBarData



/-! # RelativeTrivialCyclicMap

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-trivial-cyclic-map)

## Main definitions and statements

The primary declaration is `trivialCyclicMap`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
variable {A G}

/-- The trivial coefficient module, restricted from H to the cyclic group with residual 1.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialInput (v : Z.{u} →ₜ* H) : Equivariant A (PUnit.{u + 1} × Z.{u}) :=
  (inflate (R := A.toMon) (productMap (G := PUnit.{u + 1}) v)).obj
    (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H))

/-- The relative two-column total of the restricted trivial regular module.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialTotal (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :=
  K.functor.obj (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj

/-- With trivial coefficients the total has its coordinate-normalized identification with
[R -> 0 R]. The equations in degrees zero and one determine the isomorphism, since all
other terms are zero by the total coordinates.
Source: paragraph (3), step 18
(blueprint: def-sfb-relative-trivial-cyclic-map).
Proof: the restricted generator acts as identity, so T-1 is zero. Use the first biproduct
coordinate in degree zero and the second in degree one; every other summand is zero. -/
theorem trivialTotalIsoExist (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    ∃! k : ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
        (.up ℤ)).obj (trivialTotal K v) ≅ extend (trivialCyclic A),
      (k.hom.f 0 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).hom =
        (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
          ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 0).hom ≫
            biprod.fst ≫
            (retainResidual A PUnit.{u + 1} Z).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom)) ∧
      (k.hom.f 1 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
          (i := 1) (i' := 1) rfl).hom =
        (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
          ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 1).hom ≫
            biprod.snd ≫
            (retainResidual A PUnit.{u + 1} Z).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom)) := by
  sorry

/-- The unique coordinate identification of the trivial cyclic total.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialTotalIso (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).obj (trivialTotal K v) ≅ extend (trivialCyclic A) :=
  Classical.choose (trivialTotalIsoExist K v)

/-- The trivial residual group disappears by the original identity on its regular module.
Source: paragraph (3), step 18
(blueprint: def-sfb-relative-trivial-cyclic-map).
Proof: restricting a trivial action is trivial. The underlying identity is equivariant,
natural and invertible; faithfulness fixes the displayed isomorphism uniquely. -/
theorem forgetTrivialExist :
    ∃! e : (forgetResidual A PUnit.{u + 1} H).obj
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H)) ≅
      CondensedDerivedRestriction.regularTrivial A H,
      e.hom.val = 𝟙 (Mod.regular A.X) := by
  sorry

/-- The identity-normalized trivial-group comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def forgetTrivial := Classical.choose (forgetTrivialExist (A := A) (H := H))

/-- The canonical identification of relative invariants of trivial coefficients with the
scalar derived invariants, with exact restriction and single-complex identifications.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialSourceIso :
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategory.obj
      ((derived A PUnit.{u + 1} H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H)))) ≅
      (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A H)) :=
  (forgetDerived A PUnit.{u + 1} (J := H)).app _ ≪≫
    (CondensedDerivedRestriction.derived A H).mapIso
      (((forgetResidual A PUnit.{u + 1} H).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (forgetTrivial (A := A) (H := H)))

/-- The scalar map c obtained by forgetting the trivial residual action in the relative map.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialCyclicMap {K : TotalModel A PUnit.{u + 1}}
    (C : HasComparison A PUnit.{u + 1} K) (v : Z.{u} →ₜ* H) :
    (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A H)) ⟶
      DerivedCategory.Q.obj (extend (trivialCyclic A)) :=
  (trivialSourceIso (A := A) (H := H)).inv ≫
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategory.map
      (cyclicMap A PUnit.{u + 1} C v
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H))) ≫
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategoryFactors.hom.app
      (trivialTotal K v) ≫ DerivedCategory.Q.map (trivialTotalIso K v).hom


end CategoryTheory.RelativeCyclic

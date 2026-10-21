/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeCyclicTotal



/-! # RelativeInvariantForgetting

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-invariant-forgetting)

## Main definitions and statements

The primary declaration is `forgetDerived`.
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
/-- Forgetting residual actions commutes with ordinary invariants, with its isomorphism
fixed by the two actual invariant-submodule inclusions.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: both section modules consist of exactly the sections fixed by the second group
after every base change; compose both embeddings into the same underlying module. -/
theorem forgetInvariantsExist :
    ∃! e : (invariants A G J).functor ⋙ CondensedBar.forgetAction ≅
        forgetResidual A G J ⋙ (CondensedDerivedRestriction.invariants A J).functor,
      ∀ N, e.hom.app N ≫
          (CondensedDerivedRestriction.invariants A J).inclusion.app
            ((forgetResidual A G J).obj N) = (invariants A G J).inclusion.app N := by
  sorry

/-- The unique comparison of actual fixed submodules.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetInvariants : (invariants A G J).functor ⋙ CondensedBar.forgetAction ≅
    forgetResidual A G J ⋙ (CondensedDerivedRestriction.invariants A J).functor :=
  Classical.choose (forgetInvariantsExist A G (J := J))

/-- Exact forgetting preserves injectives, so its derived comparison is the unique
isomorphism normalized by the underived invariant-inclusion comparison and derived units.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: use the exact free-induction left adjoint to forgetting, resolve in the full
action category, and identify the two invariant complexes. Naturality of injective
resolution comparisons and the derived universal property give the displayed equation. -/
theorem forgetDerivedExist :
    ∃! e : derived A G J ⋙ (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
        (forgetResidual A G J).mapDerivedCategory ⋙ CondensedDerivedRestriction.derived A J,
      ∀ N : CochainComplex (Equivariant A (G × J)) ℤ,
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
            ((unit A G J) N) ≫
          e.hom.app (DerivedCategory.Q.obj N) ≫
          (CondensedDerivedRestriction.derived A J).map
            ((forgetResidual A G J).mapDerivedCategoryFactors.hom.app N) =
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategoryFactors.hom.app
            (((invariants A G J).functor.mapHomologicalComplex (.up ℤ)).obj N) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (forgetInvariants A G (J := J)) (.up ℤ)).hom.app N) ≫
          (scalarUnit A J)
            (((forgetResidual A G J).mapHomologicalComplex (.up ℤ)).obj N) := by
  sorry

/-- The normalized relative-to-scalar derived comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetDerived :
    derived A G J ⋙ (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
      (forgetResidual A G J).mapDerivedCategory ⋙ CondensedDerivedRestriction.derived A J :=
  Classical.choose (forgetDerivedExist A G (J := J))

variable {A G}

/-- Forgetting G and restricting J commute by the identity of the original module maps.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: both actions precompose the original action with j maps to (1,v(j)). The underlying
identity is equivariant. Faithfulness gives uniqueness and naturality. -/
theorem forgetRestrictionExist (v : J →ₜ* H) :
    ∃! e : forgetResidual A G H ⋙ inflate (R := A.toMon) v ≅
        inflate (R := A.toMon) (productMap (G := G) v) ⋙ forgetResidual A G J,
      ∀ N, (e.hom.app N).val = 𝟙 N.module := by
  sorry

/-- The uniquely normalized commutation of group restriction with residual forgetting.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetRestriction (v : J →ₜ* H) :
    forgetResidual A G H ⋙ inflate (R := A.toMon) v ≅
      inflate (R := A.toMon) (productMap (G := G) v) ⋙ forgetResidual A G J :=
  Classical.choose (forgetRestrictionExist (A := A) (G := G) v)

/-- Localization of the actual residual-forgetting commutation square.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetRestrictionDerived (v : J →ₜ* H) :
    (forgetResidual A G H).mapDerivedCategory ⋙ (inflate (R := A.toMon) v).mapDerivedCategory ≅
      (inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory ⋙
        (forgetResidual A G J).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (forgetResidual A G H) (inflate v)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (forgetRestriction (A := A) (G := G) v) ≪≫
    Functor.mapDerivedCategoryCompIso
      (inflate (R := A.toMon) (productMap (G := G) v)) (forgetResidual A G J)

/-- Forgetting residual actions carries the actual derived restriction to scalar restriction.
Source: paragraph (3), steps 6 and 12
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: use an equivariant K-injective resolution in the Grothendieck action category.
Forgetting preserves K-injectives because its free-induction left adjoint is exact,
also on complexes. The invariant inclusions agree, so both paths have the same
normalized derived-unit equation. The right-derived universal property identifies them. -/
theorem forgetBeta (v : J →ₜ* H)
    (N : DerivedCategory.{u + 1} (Equivariant A (G × H))) :
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
        ((beta (A := A) (G := G) v).app N) ≫
      (forgetDerived A G (J := J)).hom.app
        ((inflate (productMap (G := G) v)).mapDerivedCategory.obj N) =
    (forgetDerived A G (J := H)).hom.app N ≫
      (CondensedDerivedRestriction.groupMap A v).app
        ((forgetResidual A G H).mapDerivedCategory.obj N) ≫
      (CondensedDerivedRestriction.derived A J).map
        ((forgetRestrictionDerived (A := A) (G := G) v).hom.app N) := by
  sorry



variable (A G)

/-- Forgetting the relative cyclic comparison gives the scalar ordinary derived comparison,
with exact-functor localization identifications included in the actual formula.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgottenLambda {K : TotalModel A G} (C : HasComparison A G K)
    (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    DerivedCategory.Q.obj
        (((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
          (K.functor.obj N.obj)) ≅
      (CondensedDerivedRestriction.derived A Z).obj
        (DerivedCategory.Q.obj
          (((forgetResidual A G Z).mapHomologicalComplex (.up ℤ)).obj N.obj)) :=
  ((CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategoryFactors.app
      (K.functor.obj N.obj)).symm ≪≫
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.mapIso
      (lambda A G C N) ≪≫
    (forgetDerived A G (J := Z)).app (DerivedCategory.Q.obj N.obj) ≪≫
    (CondensedDerivedRestriction.derived A Z).mapIso
      ((forgetResidual A G Z).mapDerivedCategoryFactors.app N.obj)

/-- Forgetting comparisons commute with the canonical shifts and triangle boundaries.
Source: paragraph (3), steps 6 and 12
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: forgetting takes equivariant injective resolutions to injective resolutions, and
the same invariant complexes and cone diagrams compute both sides. The canonical
resolution comparisons commute with their signed shifts; apply their uniqueness. -/
theorem forgetDerivedShift : NatTrans.CommShift (forgetDerived A G (J := J)).hom ℤ := by
  sorry


/-- Inflate a scalar cyclic action to a trivial residual action, on the same module.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def addTrivialResidual : Equivariant A Z.{u} ⥤ Equivariant A (PUnit.{u + 1} × Z.{u}) :=
  inflate (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains addition of maps.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualAdditive : (addTrivialResidual A).Additive :=
  CondensedDerivedRestriction.restrictionAdditive (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains kernels.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualLimits : PreservesFiniteLimits (addTrivialResidual A) :=
  CondensedDerivedRestriction.restrictionLimits (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains cokernels.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualColimits : PreservesFiniteColimits (addTrivialResidual A) :=
  CondensedDerivedRestriction.restrictionColimits (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Adding and then forgetting the trivial residual action is the original action,
with its isomorphism fixed by the identity of every underlying module map.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting).
Proof: projection after inclusion is identity on every generalized cyclic section.
The original module identity and its inverse are equivariant and natural; faithfulness
of underlying modules gives uniqueness. -/
theorem unitResidualIsoExist :
    ∃! e : addTrivialResidual A ⋙ forgetResidual A PUnit.{u + 1} Z ≅
        𝟭 (Equivariant A Z), ∀ M, (e.hom.app M).val = 𝟙 M.module := by
  sorry

/-- The identity-normalized forgetting isomorphism for a trivial residual action.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def unitResidualIso : addTrivialResidual A ⋙ forgetResidual A PUnit.{u + 1} Z ≅
    𝟭 (Equivariant A Z) := Classical.choose (unitResidualIsoExist A)

/-- The same normalization on every bounded-below scalar action complex.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def scalarizationIso (N : CochainComplex.Plus (Equivariant A Z.{u})) :
    ((forgetResidual A PUnit.{u + 1} Z).mapHomologicalComplex (.up ℤ)).obj
        ((addTrivialResidual A).mapCochainComplexPlus.obj N).obj ≅ N.obj :=
  (NatIso.mapHomologicalComplex (unitResidualIso A) (.up ℤ)).app N.obj

end CategoryTheory.RelativeCyclic

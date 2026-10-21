/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeCyclicTotal
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution



/-! # RelativeLatticeBridge

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-lattice-bridge)

## Main definitions and statements

The primary declaration is `DiscreteBridge`.
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

/-- The recorded standard scalar localization, with its universe supplied explicitly.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
abbrev LargeDerived := @DerivedCategory.{u + 2} (Modules A) inferInstance inferInstance
  (largeModulesDerived A)

/-- The identical cochain localization into the recorded standard universe.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
def largeQ : CochainComplex (Modules A) ℤ ⥤ LargeDerived A :=
  @DerivedCategory.Q.{u + 2} (Modules A) inferInstance inferInstance (largeModulesDerived A)

/-- The explicit larger-universe Q retains its existing localization structure.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
instance largeQLocalization : (largeQ A).IsLocalization
    (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) := by
  let : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  change (DerivedCategory.Q.{u + 2}).IsLocalization _
  infer_instance

/-- Canonical transport from the lattice module's standard localization universe to the
small-Hom scalar localization, induced by the identical localization functor on complexes.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
def lowerDerived : LargeDerived A ⥤ DerivedCategory.{u + 1} (Modules A) :=
  Localization.lift (DerivedCategory.Q.{u + 1} (C := Modules A))
    (Localization.inverts (DerivedCategory.Q.{u + 1} (C := Modules A))
      (HomologicalComplex.quasiIso (Modules A) (.up ℤ)))
    ((largeQ A))

/-- The localization-unit comparison fixing universe transport on every complex.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
def lowerQ : (largeQ A) ⋙ lowerDerived A ≅
    DerivedCategory.Q.{u + 1} (C := Modules A) :=
  Localization.fac (DerivedCategory.Q.{u + 1} (C := Modules A))
    (Localization.inverts (DerivedCategory.Q.{u + 1} (C := Modules A))
      (HomologicalComplex.quasiIso (Modules A) (.up ℤ)))
    ((largeQ A))

/-- The equivalence between the discrete condensed cyclic action and the recorded lattice
rank-one action. The underlying module and positive-generator equation fix the equivalence;
its invariant comparison is fixed by the two actual inclusions.
Source: paragraph (3), steps 9 and 12
(blueprint: def-sfb-relative-lattice-bridge). -/
structure DiscreteBridge where
  equivalence : Equivariant A Z.{u} ≌ Profinite.DiscreteLattice.Equivariant A.toMon 1
  underlying : equivalence.functor ⋙ Action.forget _ _ ≅ CondensedBar.forgetAction
  generator : ∀ (N : Equivariant A Z.{u}) (S : Profinite.{u})
    (x : sections A (equivalence.functor.obj N).V S),
    ((underlying.hom.app N).hom.hom.app (op S))
        ((((equivalence.functor.obj N).ρ
          (Profinite.DiscreteLattice.generator (0 : Fin 1))).hom.hom.app (op S)) x) =
      (N.act S (ContinuousMap.const S RelativeCyclic.generator)).toFun
        (((underlying.hom.app N).hom.hom.app (op S)) x)
  additive : equivalence.functor.Additive
  limits : PreservesFiniteLimits equivalence.functor
  colimits : PreservesFiniteColimits equivalence.functor
  invariants : equivalence.functor ⋙ Profinite.DiscreteLattice.invariants A.toMon 1 ≅
    (CondensedDerivedRestriction.invariants A Z).functor
  inclusion : ∀ N, invariants.hom.app N ≫
      (CondensedDerivedRestriction.invariants A Z).inclusion.app N =
    limit.π ((Action.functorCategoryEquivalence (Modules A)
        (Profinite.DiscreteLattice.Group 1)).functor.obj (equivalence.functor.obj N))
      PUnit.unit ≫ underlying.hom.app N

attribute [instance] DiscreteBridge.additive DiscreteBridge.limits DiscreteBridge.colimits

/-- The lattice-to-scalar derived transport is pinned on every complex by the invariant
comparison and the two computation units. Thus it cannot insert an arbitrary higher-degree
automorphism while fixing H-zero.
Source: paragraph (3), steps 9 and 12
(blueprint: def-sfb-relative-lattice-bridge). -/
structure DiscreteDerivedBridge (B : DiscreteBridge A) where
  iso : B.equivalence.functor.mapDerivedCategory ⋙
      Profinite.DiscreteLattice.derivedInvariants A.toMon 1 ⋙ lowerDerived A ≅
    CondensedDerivedRestriction.derived A Z
  normalization : ∀ N : CochainComplex (Equivariant A Z.{u}) ℤ,
    (lowerDerived A).map (Profinite.DiscreteLattice.derivedUnit A.toMon 1
        ((B.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj N)) ≫
      (lowerDerived A).map ((Profinite.DiscreteLattice.derivedInvariants A.toMon 1).map
        (B.equivalence.functor.mapDerivedCategoryFactors.inv.app N)) ≫
      iso.hom.app (DerivedCategory.Q.obj N) =
    (lowerQ A).hom.app
        (((Profinite.DiscreteLattice.invariants A.toMon 1).mapHomologicalComplex (.up ℤ)).obj
          ((B.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj N)) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex B.invariants (.up ℤ)).hom.app N) ≫
      (scalarUnit A Z) N

variable {A G}

/-- Projection to the degree-zero module coordinate of the forgotten relative total.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
def zeroCoordinate (K : TotalModel A G) (M : Equivariant A (G × Z.{u})) :
    (((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
      (K.functor.obj (single A (G × Z) M).obj)).X 0 ⟶ M.module :=
  (CondensedBar.forgetAction (A := A) (G := G)).map
      ((K.coordinates (single A (G × Z) M).obj 0).hom ≫ biprod.fst) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom.val

/-- Projection to the degree-one module coordinate of the forgotten relative total.
Source: paragraph (3) (blueprint: def-sfb-relative-lattice-bridge). -/
def oneCoordinate (K : TotalModel A G) (M : Equivariant A (G × Z.{u})) :
    (((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
      (K.functor.obj (single A (G × Z) M).obj)).X 1 ⟶ M.module :=
  (CondensedBar.forgetAction (A := A) (G := G)).map
      ((K.coordinates (single A (G × Z) M).obj 1).hom ≫ biprod.snd) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom.val


end CategoryTheory.RelativeCyclic

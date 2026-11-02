/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration

/-! # Lisse finite-projective étale sheaves have local scalar models

Source: blueprint scalar-six-ctf (1), finite-projective local models.
(blueprint: lem-sfb-finite-scalar-etale-lisse-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- Realization of a lisse finite-projective étale sheaf is locally perfect over the
specified condensed coefficient ring.

Source: blueprint scalar-six-ctf (1), finite projective local models; Stacks 00NX, 099Y.
(blueprint: lem-sfb-finite-scalar-etale-lisse-model).

Proof: Choose an étale trivializing cover for L. On a nonempty member a geometric stalk
identifies the constant module with a finite projective module; replace empty members
by zero models. Regard the cover as a pro-étale cover. Each finite projective module
splits a finite free surjection. The sectionwise constant-ring equivalence identifies
finite free modules with finite sums of the scalar regular module and lifts the splitting
by full faithfulness. Restriction along e identifies the regular scalar modules and
carries this splitting to the Λ scalar category. Put the resulting scalar module in
degree zero, with bounds [0,0] and rank-zero splittings in every other degree. The
constant-model and coefficient-pullback comparisons identify its scalar realization with
the pullback of the realized L. Exact functors commute with the single-complex functor,
so these are the isomorphisms required by IsLocallyPerfectScalarModel. The same proof
handles the zero ring, empty covers and rank zero. -/
theorem sfbFiniteScalarEtaleLisseModel (S : Scheme.{u}) [IsNoetherian S]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hL : FlatModelEtaleLisseProjective (ULift.{u + 1} A) L) :
    IsLocallyPerfectScalarModel Λ.X S
      ((sfbFiniteScalarRealization A e eR S).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing

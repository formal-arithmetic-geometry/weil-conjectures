/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.Paper.InternalScalarPullbackNormalization
public import Sheaf.Paper.InternalScalarMateProjection

/-! # Flat scalar and geometric comparison coherence

Source: Stacks 0D6E, 07A6 and 0B65; the comparison and conjugacy steps of the
rational proper-base-change coefficient square.
(blueprint: lem-sfb-flat-scalar-geometric-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]

set_option maxHeartbeats 800000 in
-- The statement retains the complete K-injective normalization and section comparison square.
/-- The actual derived scalar/geometric comparisons have the balanced and
sectionwise computation normalizations for any normalized section scalar models.

Source: Stacks 0D6E, 07A6 and 0B65; steps 3--5 of
lem-sfb-flat-coefficient-square-normalization.
(blueprint: lem-sfb-flat-scalar-geometric-coherence).

Proof: derive the ordinary restriction/direct-image isomorphism. At a K-injective
complex its three defining comparison factors identify its component with the
ordinary comparison. Flatness makes restriction preserve K-injectives, so both
sides are computed by these complexes. The section equivalence preserves the
specified computation units and the ordinary map fixes every section. Thus the
section direct-image comparison has the asserted normalization, and the displayed
comparison with the internal map holds on K-injective models and hence everywhere.
The mate of the inverse ordinary restriction/pullback comparison is that same
ordinary direct-image comparison: both adjuncts are the unit followed by the
common underlying pushforward. Exact inverse image and flat scalar extension
allow the pullback comparison to descend termwise. The derived mate computation
therefore identifies the actual direct-image map with scalarRestrictionPush.
For the two composite derived adjunctions, conjugacy says that the scalar
transpose of the inverse actual theta is the inverse restriction/pullback map
composed with pullback of the scalar unit. The ordinary balancing map has exactly
this transpose, since both insert 1 and then preserve the balanced generator.
Localize this equality; injectivity of the scalar adjunction Hom bijection
identifies the actual theta with the universally normalized balancing map.
Its computation-counit equation is PullNormalized. Transport the equation through
the given normalized section models. Agreement on generators and uniqueness of
universal derived comparison maps give SectionPullNormalized. This uses neither
finite-type hypotheses nor a nonzero coefficient ring, so identity maps, zero
rings and empty schemes are included. -/
theorem flat_scalar_geometric_coherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (hsX : SectionScalarNormalized a X sX) (hsY : SectionScalarNormalized a Y sY)
    (theta : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (d0 : F S f ⋙ V a Y ≅ V a X ⋙ F R f)
    (htheta : theta = by
      unfold D L CondensedRing.moduleObjectDerivedPullback
      exact (CondensedRing.derivedPullIso a f).symm)
    (hd0 : d0 = by
      unfold F CondensedRing.moduleObjectDerivedPushforward
      exact CondensedRing.derivedComapLowerStarIso a f) :
    d0.hom = scalarRestrictionPush a f ∧ PullNormalized a f theta ∧
      SectionPullNormalized a f sX sY theta ∧
    ∃ d : ModuleRingedComparison.derivedPushforward S f ⋙
          SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
          ModuleRingedComparison.derivedPushforward R f,
      (∃ r : ModuleRingedComparison.pushforward S f ⋙
            SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
              (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
                (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
          SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
              (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
                (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward R f,
        (∀ (N : ModuleRingedComparison.modules S X) (W : Y.ProEtᵒᵖ)
          (x : ((ModuleRingedComparison.pushforward S f).obj N).val.obj W),
          (r.hom.app N).val.app W x = x) ∧
        ∀ (I : CochainComplex (ModuleRingedComparison.modules S X) ℤ), I.IsKInjective →
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y) (coefficientMap a Y))).map
              ((ModuleRingedComparison.pushforward S f).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
            d.hom.app (DerivedCategory.Q.obj I) ≫
            (ModuleRingedComparison.derivedPushforward R f).map
              (((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
                (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
                  (Scheme.ProEt.topology X)
                    (coefficientMap a X))).mapHomologicalComplexUpToQuasiIsoFactorsh
                    (.up ℤ)).hom.app
                    ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
          ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y)
                (coefficientMap a Y))).mapHomologicalComplexUpToQuasiIsoFactorsh
                    (.up ℤ)).hom.app
                (((ModuleRingedComparison.pushforward S f).mapHomotopyCategory (.up ℤ)).obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso r (.up ℤ)).hom.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
            (ModuleRingedComparison.pushforward R f).rightDerivedFunctorUnit.app
              (((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
                (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
                  (Scheme.ProEt.topology X) (coefficientMap a X))).mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
      ) ∧
      ∀ N : DerivedCategory (Modules S X),
        (ModuleRingedComparison.derivedEquivalence R Y).functor.map
            (d0.hom.app N) ≫
          (scalarSectionPushComparison R f).hom.app ((V a X).obj N) ≫
          (ModuleRingedComparison.derivedPushforward R f).map
            ((sectionScalarRestriction a X sX).hom.app N) =
        (sectionScalarRestriction a Y sY).hom.app ((F S f).obj N) ≫
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y) (coefficientMap a Y))).map
                ((scalarSectionPushComparison S f).hom.app N) ≫
          d.hom.app ((ModuleRingedComparison.derivedEquivalence S X).functor.obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientChange

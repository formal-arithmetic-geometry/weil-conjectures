/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCompletedArrowTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction

/-! # Supported endpoint transport with arbitrary coefficients

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Transport the supported inverse-image endpoint, keeping the coefficient ring
arbitrary. Its realization equation is proved separately below.

Source: blueprint coefficient changes (3), supported-source realization.
(blueprint: lem-diagonal-supported-endpoint-transport).

Construction: use the exact single pullback comparison, then the single of the
ordinary supported endpoint. Fully faithful preimage transports this composite
through the realization comparison; its normalization is the generic preimage
normalization equation. No completed diagonal class is used. -/
@[irreducible] def diagonalSupportedEndpointTransport
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {C C' : Type*} [Category C] [Category C']
    (P : C ⥤ C')
    (F : C ⥤ DerivedCategory (Modules R (diagonalSurface Y)))
    (F' : C' ⥤ DerivedCategory (Modules R (diagonalSurface Y')))
    [F'.Full] [F'.Faithful]
    (e : P ⋙ F' ≅ F ⋙ derivedUpper R (baseW g))
    {X : C} {X' : C'}
    (s : F.obj X ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y))
    (s' : F'.obj X' ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y'))
    (b : (CondensedRing.upperStar R (baseW g)).obj (source R Y) ≅ source R Y') :
    P.obj X ≅ X' :=
  diagonalTransportedEndpoint P F F' (derivedUpper R (baseW g)) e s s'
    (singlePullback R (baseW g) (source R Y) ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso b)

/-- The supported transport satisfies the named full realization equation.
Source: blueprint coefficient changes (3), supported-source realization.
(blueprint: lem-diagonal-supported-endpoint-transport).
Proof: use generic preimage normalization for the exact single pullback followed
by the single of the ordinary supported comparison. -/
theorem diagonalSupportedEndpointTransport_normalization
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {C C' : Type*} [Category C] [Category C']
    (P : C ⥤ C')
    (F : C ⥤ DerivedCategory (Modules R (diagonalSurface Y)))
    (F' : C' ⥤ DerivedCategory (Modules R (diagonalSurface Y')))
    [F'.Full] [F'.Faithful]
    (e : P ⋙ F' ≅ F ⋙ derivedUpper R (baseW g))
    {X : C} {X' : C'}
    (s : F.obj X ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y))
    (s' : F'.obj X' ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y'))
    (b : (CondensedRing.upperStar R (baseW g)).obj (source R Y) ≅ source R Y') :
    DiagonalTransportedEndpointMapProperty P F F' (derivedUpper R (baseW g)) e
      s (DerivedCategory.singleFunctor _ 0) s'
      (singlePullback R (baseW g) (source R Y)) b
      (diagonalSupportedEndpointTransport R g P F F' e s s' b) := by
  simpa only [diagonalSupportedEndpointTransport] using
    diagonalTransportedEndpointMap_normalization P F F' (derivedUpper R (baseW g)) e
      s (DerivedCategory.singleFunctor _ 0) s'
      (singlePullback R (baseW g) (source R Y)) b

/-- Canonical realization of an ordinary single object with a prescribed ordinary
endpoint. Source: blueprint coefficient changes (3).
(blueprint: lem-diagonal-supported-endpoint-transport).
Construction: compose the exact single comparison with the single of the
ordinary endpoint isomorphism. -/
@[irreducible] def diagonalRealizedSingleSource
    {C : Type*} [Category C] [Abelian C]
    {E : Type*} [Category E] [Abelian E]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X : C} {A : E} (s : F.obj X ≅ A) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor E 0).obj A :=
  (F.mapDerivedCategorySingleFunctor 0).app X ≪≫
    (DerivedCategory.singleFunctor E 0).mapIso s

/-- Canonical realization of a shifted single object with a prescribed ordinary
endpoint. Source: blueprint coefficient changes (3).
(blueprint: lem-diagonal-supported-endpoint-transport).
Construction: compose the canonical shift comparison with the shift of the
exact single comparison and the ordinary endpoint isomorphism. -/
@[irreducible] def diagonalRealizedSingleTarget
    {C : Type*} [Category C] [Abelian C]
    {E : Type*} [Category E] [Abelian E]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {T : C} {B : E} (n : ℤ) (t : F.obj T ≅ B) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj T)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor E 0).obj B)⟦n⟧ :=
  (F.mapDerivedCategory.commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app T ≪≫
        (DerivedCategory.singleFunctor E 0).mapIso t)

private theorem realizedSingleArrow_normalization
    {C : Type*} [Category C] [Abelian C]
    {E : Type*} [Category E] [Abelian E]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₃} E]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {A B : E} (s : F.obj X ≅ A) (t : F.obj Y ≅ B) (n : ℤ)
    (δ : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    ((diagonalRealizedSingleSource F s).inv ≫ F.mapDerivedCategory.map δ ≫
      (diagonalRealizedSingleTarget F n t).hom) =
      (DerivedCategory.singleFunctor E 0).map s.inv ≫
        SpTowerClasses.mapSingleArrow F n δ ≫
        ((DerivedCategory.singleFunctor E 0).map t.hom)⟦n⟧' := by
  simp only [diagonalRealizedSingleSource, diagonalRealizedSingleTarget,
    Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    SpTowerClasses.mapSingleArrow]


/-- Realize a completed square of single arrows over arbitrary abelian categories.

Source: blueprint coefficient changes (3), final exact realization.
(blueprint: lem-diagonal-supported-endpoint-transport).

Proof: use the mapped-source realization chase on the canonical single and shifted
single isomorphisms. Their abstract normalization rewrites the two conjugated
arrows as mapSingleArrow. Reassociate the ordinary source map. -/
theorem diagonalCompletedSingleArrow_realize
    {C C' E E' : Type*}
    [Category C] [Abelian C] [Category C'] [Abelian C']
    [Category E] [Abelian E] [Category E'] [Abelian E']
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} C']
    [HasDerivedCategory.{w₃} E] [HasDerivedCategory.{w₄} E']
    {P : DerivedCategory C ⥤ DerivedCategory C'}
    {F : C ⥤ E} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {F' : C' ⥤ E'} [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    {V : DerivedCategory E ⥤ DerivedCategory E'}
    (e : P ⋙ F'.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ V)
    {X T : C} {X' T' : C'} {A B : E} {A' B' M : E'}
    (n : ℤ) (s : F.obj X ≅ A) (t : F.obj T ≅ B)
    (s' : F'.obj X' ≅ A') (t' : F'.obj T' ≅ B')
    (a : P.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor C' 0).obj X')
    (b : P.obj (((DerivedCategory.singleFunctor C 0).obj T)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor C' 0).obj T')⟦n⟧)
    (q : V.obj ((DerivedCategory.singleFunctor E 0).obj A) ≅
      (DerivedCategory.singleFunctor E' 0).obj M)
    (r : M ≅ A')
    (β : V.obj (((DerivedCategory.singleFunctor E 0).obj B)⟦n⟧) ⟶
      ((DerivedCategory.singleFunctor E' 0).obj B')⟦n⟧)
    (hs : DiagonalTransportedEndpointMapProperty P F.mapDerivedCategory F'.mapDerivedCategory
      V e (diagonalRealizedSingleSource F s) (DerivedCategory.singleFunctor E' 0)
      (diagonalRealizedSingleSource F' s') q r a)
    (ht : e.hom.app (((DerivedCategory.singleFunctor C 0).obj T)⟦n⟧) ≫
        V.map (diagonalRealizedSingleTarget F n t).hom ≫ β =
      F'.mapDerivedCategory.map b.hom ≫ (diagonalRealizedSingleTarget F' n t').hom)
    (δ : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj T)⟦n⟧)
    (δ' : (DerivedCategory.singleFunctor C' 0).obj X' ⟶
      ((DerivedCategory.singleFunctor C' 0).obj T')⟦n⟧)
    (hδ : P.map δ ≫ b.hom = a.hom ≫ δ') :
    V.map ((DerivedCategory.singleFunctor E 0).map s.inv ≫
        SpTowerClasses.mapSingleArrow F n δ ≫
          ((DerivedCategory.singleFunctor E 0).map t.hom)⟦n⟧') ≫ β =
      q.hom ≫ (DerivedCategory.singleFunctor E' 0).map r.hom ≫
        (DerivedCategory.singleFunctor E' 0).map s'.inv ≫
          SpTowerClasses.mapSingleArrow F' n δ' ≫
            ((DerivedCategory.singleFunctor E' 0).map t'.hom)⟦n⟧' := by
  have h := diagonalCompletedMappedArrow_realize P F.mapDerivedCategory F'.mapDerivedCategory
    V e (diagonalRealizedSingleSource F s) (diagonalRealizedSingleTarget F n t)
    (DerivedCategory.singleFunctor E' 0) (diagonalRealizedSingleSource F' s')
    (diagonalRealizedSingleTarget F' n t') a b q r β hs ht δ δ' hδ
  simpa only [realizedSingleArrow_normalization, Category.assoc] using h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

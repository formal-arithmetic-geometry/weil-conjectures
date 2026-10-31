/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import all WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import WeilConjectures.SixFunctors.ScalarInterchangeRestrictionSquare
import all WeilConjectures.SixFunctors.ScalarRefinementPasting

/-! # Scalar extension and normalized proper/open interchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate derivedOpenImmersionShriekIso
attribute [local implicit_reducible] CommMon.toMon scalarSixPull moduleObjectDerivedPushforward

private instance normalizedInterchangeRing_comm (Λ : ScalarSixRing.{u}) :
    IsCommMonObj Λ.X := Λ.comm

private instance normalizedInterchangeMap_isMonHom {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') : IsMonHom a.hom.hom := a.hom.isMonHom_hom

private theorem normalizedSquare
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {J : A ⥤ C} {U : C ⥤ A} {I : B ⥤ D} {V : D ⥤ B}
    {J' : A' ⥤ C'} {U' : C' ⥤ A'} {I' : B' ⥤ D'} {V' : D' ⥤ B'}
    {P : A ⥤ B} {R : C ⥤ D} {P' : A' ⥤ B'} {R' : C' ⥤ D'}
    (aj : J ⊣ U) (ai : I ⊣ V) (aj' : J' ⊣ U') (ai' : I' ⊣ V')
    (TA : A ⥤ A') (TB : B ⥤ B') (TC : C ⥤ C') (TD : D ⥤ D')
    (di : I ⋙ TD ≅ TB ⋙ I') (dj : J ⋙ TC ≅ TA ⋙ J')
    (ti : V ⋙ TB ≅ TD ⋙ V') (tj : U ⋙ TA ≅ TC ⋙ U')
    (gp : P ⋙ TB ⟶ TA ⋙ P') (gr : R ⋙ TD ⟶ TC ⋙ R')
    (rho : R ⋙ V ⟶ U ⋙ P) (rho' : R' ⋙ V' ⟶ U' ⋙ P')
    (hui : ∀ N, TB.map (ai.unit.app N) ≫ ti.hom.app (I.obj N) =
      ai'.unit.app (TB.obj N) ≫ V'.map (di.inv.app N))
    (huj : ∀ N, TA.map (aj.unit.app N) ≫ tj.hom.app (J.obj N) =
      aj'.unit.app (TA.obj N) ≫ U'.map (dj.inv.app N))
    (hr : ∀ N, V'.map (gr.app N) ≫ rho'.app (TC.obj N) ≫ P'.map (tj.inv.app N) =
      ti.inv.app (R.obj N) ≫ TB.map (rho.app N) ≫ gp.app (U.obj N))
    (K : A) [IsIso (rho'.app (J'.obj (TA.obj K)))]
    (m : I.obj (P.obj K) ⟶ R.obj (J.obj K))
    (m' : I'.obj (P'.obj (TA.obj K)) ⟶ R'.obj (J'.obj (TA.obj K)))
    (hm : (ai.homEquiv _ _) m ≫ rho.app (J.obj K) = P.map (aj.unit.app K))
    (hm' : (ai'.homEquiv _ _) m' ≫ rho'.app (J'.obj (TA.obj K)) =
      P'.map (aj'.unit.app (TA.obj K))) :
    TD.map m ≫ gr.app (J.obj K) ≫ R'.map (dj.hom.app K) =
      di.hom.app (P.obj K) ≫ I'.map (gp.app K) ≫ m' := by
  have hr' (N : C) : V'.map (gr.app N) ≫ rho'.app (TC.obj N) =
      ti.inv.app (R.obj N) ≫ TB.map (rho.app N) ≫ gp.app (U.obj N) ≫
        P'.map (tj.hom.app N) := by
    apply (cancel_mono (P'.map (tj.inv.app N))).mp
    simp only [Category.assoc]
    rw [← P'.map_comp, Iso.hom_inv_id_app]
    erw [P'.map_id, Category.comp_id]
    exact hr N
  have hju : TA.map (aj.unit.app K) ≫ tj.hom.app (J.obj K) ≫
      U'.map (dj.hom.app K) = aj'.unit.app (TA.obj K) := by
    rw [← Category.assoc, huj]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [U'.map_id, Category.comp_id]
  apply (cancel_epi (di.inv.app (P.obj K))).mp
  apply (ai'.homEquiv _ _).injective
  apply (cancel_mono (rho'.app (J'.obj (TA.obj K)))).mp
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hui (P.obj K))]
  rw [← reassoc_of% (ti.hom.naturality m)]
  have hn := rho'.naturality (dj.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  rw [reassoc_of% (hr' (J.obj K))]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [Adjunction.homEquiv_unit] at hm hm'
  rw [← TB.map_comp_assoc, ← TB.map_comp_assoc, hm]
  rw [reassoc_of% (gp.naturality (aj.unit.app K))]
  rw [← P'.map_comp, ← P'.map_comp, hju]
  rw [← V'.map_comp_assoc, Iso.inv_hom_id_app]
  erw [V'.map_id, Category.id_comp]
  simp only [Category.assoc] at hm'
  rw [← reassoc_of% (ai'.unit.naturality (gp.app K)), hm']


set_option maxHeartbeats 8000000 in
-- Identify the geometric derived adjunctions with their exact presentations.
/-- Scalar change respects the uniquely normalized proper/open interchange.
Source: latest blueprint, scalar-six compact-support proof, Independence and Composition.
(blueprint: lem-sfb-scalar-normalized-interchange-square).

Proof: the restriction comparisons are components of canonical mate transformations, so are
natural. Precompose with the inverse open scalar comparison and take the new open adjoint. Follow it
with
the invertible restriction exchange; these operations detect equality. The open mate identity
replaces the new unit followed by that inverse comparison with scalar extension of the old unit
followed by theta. Naturality of theta and the restriction exchange, and the scalar restriction
rectangle, then replace the old normalized interchange by scalar extension of the proper image
of the source open unit. Naturality of the proper scalar mate moves that unit past the mate. The
source open-unit identity gives the new source open unit. Normalization of the new interchange
and naturality of the target open unit give the same result on the other path. Cancel the
detecting isomorphism and transpose. -/
theorem scalarNormalizedInterchangeSquare {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ W)
    [IsOpenImmersion i] [IsProper p]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (A : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (m : (openImmersionLowerShriek Λ.X i).mapDerivedCategory.obj
        ((RootCoordinateFace.lower Λ.X p).obj A) ⟶
      (RootCoordinateFace.lower Λ.X c.obj.obj.g).obj
        ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A))
    (m' : (openImmersionLowerShriek Λ'.X i).mapDerivedCategory.obj
        ((RootCoordinateFace.lower Λ'.X p).obj ((scalarSixChange a X).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        ((openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.obj
          ((scalarSixChange a X).obj A)))
    (hm : compositionInterchangeIsNormalized Λ.X p i c A m)
    (hm' : compositionInterchangeIsNormalized Λ'.X p i c ((scalarSixChange a X).obj A) m') :
    (scalarSixChange a W).map m ≫
      (scalarDirectImageMate a c.obj.obj.g).app
        ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A) ≫
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).map
        ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _ c.obj.obj.i _).hom.app A) =
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom _ _ i _).hom.app
        ((RootCoordinateFace.lower Λ.X p).obj A) ≫
      (openImmersionLowerShriek Λ'.X i).mapDerivedCategory.map
        ((scalarDirectImageMate a p).app A) ≫ m' := by
  let rho : RootCoordinateFace.lower Λ.X c.obj.obj.g ⋙ scalarSixPull Λ i ⟶
        scalarSixPull Λ c.obj.obj.i ⋙ RootCoordinateFace.lower Λ.X p :=
      { app := compositionInterchangeRestriction Λ.X p i c
        naturality := by
          intro M N t
          have h := (Adjunction.exchangeRight
            ((derivedUpperStarLowerStarAdjunction Λ.X c.obj.obj.g).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ.X c.obj.obj.g))
            ((derivedUpperStarLowerStarAdjunction Λ.X p).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ.X p))
            (compositionInterchangePullback Λ.X p i c)).naturality t
          simpa only [compositionInterchangeRestriction, Adjunction.homEquiv_unit,
            RootCoordinateFace.lower, moduleObjectDerivedPushforward, scalarSixPull,
            Functor.comp_map, Functor.map_comp, Category.assoc,
            Adjunction.exchangeRight_app] using h }
  let rho' : RootCoordinateFace.lower Λ'.X c.obj.obj.g ⋙ scalarSixPull Λ' i ⟶
        scalarSixPull Λ' c.obj.obj.i ⋙ RootCoordinateFace.lower Λ'.X p :=
      { app := compositionInterchangeRestriction Λ'.X p i c
        naturality := by
          intro M N t
          have h := (Adjunction.exchangeRight
            ((derivedUpperStarLowerStarAdjunction Λ'.X c.obj.obj.g).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X c.obj.obj.g))
            ((derivedUpperStarLowerStarAdjunction Λ'.X p).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X p))
            (compositionInterchangePullback Λ'.X p i c)).naturality t
          simpa only [compositionInterchangeRestriction, Adjunction.homEquiv_unit,
            RootCoordinateFace.lower, moduleObjectDerivedPushforward, scalarSixPull,
            Functor.comp_map, Functor.map_comp, Category.assoc,
            Adjunction.exchangeRight_app] using h }
  have : IsIso (rho'.app
        ((openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.obj
          ((scalarSixChange a X).obj A))) :=
      interchange_restriction_iso Λ'.X p i c _
  exact normalizedSquare
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X c.obj.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X c.obj.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X i)
      (scalarSixChange a X) (scalarSixChange a Y)
      (scalarSixChange a c.obj.obj.Z) (scalarSixChange a W)
      (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i)
      (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X)
        a.hom.hom c.obj.obj.i)
      (scalarDirectImagePullbackData.theta a i)
      (scalarDirectImagePullbackData.theta a c.obj.obj.i)
      (scalarDirectImageMate a p) (scalarDirectImageMate a c.obj.obj.g) rho rho'
      (fun N ↦ (x5_condensed_open_scalar_unit a i N).symm)
      (fun N ↦ (x5_condensed_open_scalar_unit a c.obj.obj.i N).symm)
      (scalarInterchangeRestrictionSquare a p i c) A m m' hm hm'

end AlgebraicGeometry.ProEtale.CondensedRing

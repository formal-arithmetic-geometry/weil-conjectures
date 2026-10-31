/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import WeilConjectures.SixFunctors.ScalarInterchangeRestrictionSquare
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Coefficient comparison and normalized proper/open interchange

Source: latest blueprint, `det-prop-scalar-six-compact-support.proof.md`,
Composition paragraph, restriction calculation for the normalized interchange map
(blueprint: lem-sfb-scalar-proper-open-interchange-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate derivedOpenImmersionShriekIso
attribute [local implicit_reducible] CommMon.toMon scalarSixPull moduleObjectDerivedPushforward

private theorem interchangeScalarRing_comm (Λ : ScalarSixRing.{u}) :
    IsCommMonObj Λ.X := Λ.comm

private theorem interchangeScalarMap_isMonHom {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') : IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local instance] interchangeScalarRing_comm interchangeScalarMap_isMonHom


set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private abbrev interchange_open_scalar_iso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ scalarSixChange a Z ≅
      scalarSixChange a X ⋙ (openImmersionLowerShriek Λ'.X j).mapDerivedCategory := by
  with_unfolding_all
    exact @derivedOpenImmersionShriekIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom X Z j inferInstance

private theorem interchange_open_scalar_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {TX : A ⥤ C} {RX : C ⥤ A} {TZ : B ⥤ D} {RZ : D ⥤ B}
    (a : J ⊣ P) (b : J' ⊣ P') (c : TX ⊣ RX) (d : TZ ⊣ RZ)
    (e : P' ⋙ RX ≅ RZ ⋙ P) (K : A) :
    b.unit.app (TX.obj K) ≫ P'.map
        (((conjugateIsoEquiv (c.comp b) (a.comp d)).symm e).inv.app K) =
      TX.map (a.unit.app K) ≫ (Adjunction.pushHomOfComapIso d c e).app (J.obj K) := by
  let δ := (conjugateIsoEquiv (c.comp b) (a.comp d)).symm e
  have he : conjugateEquiv (a.comp d) (c.comp b) δ.inv = e.inv := by
    exact congrArg Iso.inv ((conjugateIsoEquiv (c.comp b) (a.comp d)).apply_symm_apply e)
  have hm : (mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans =
      Adjunction.pushHomOfComapIso d c e := by
    have ht := iterated_mateEquiv_conjugateEquiv a b c d (.mk _ _ _ _ δ.inv)
    rw [he] at ht
    have hs : mateEquiv d c (mateEquiv a b (.mk _ _ _ _ δ.inv)) =
        .mk _ _ _ _ e.inv := by
      ext N
      exact congr_app ht N
    exact congrArg TwoSquare.natTrans ((mateEquiv d c).eq_symm_apply.mpr hs)
  have hu := unit_mateEquiv a b (.mk _ _ _ _ δ.inv) K
  change TX.map (a.unit.app K) ≫
      ((mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans).app (J.obj K) =
    b.unit.app (TX.obj K) ≫ P'.map (δ.inv.app K) at hu
  rw [hm] at hu
  exact hu.symm

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem interchange_condensed_open_scalar_unit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j).unit.app
        ((scalarSixChange a X).obj K) ≫
      (scalarSixPull Λ' j).map
        ((interchange_open_scalar_iso a j).inv.app K) =
      (scalarSixChange a X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app K) ≫
      (scalarDirectImagePullbackData.theta a j).hom.app
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) := by
  with_unfolding_all
    rw [scalarDirectImagePullbackData.thetaNormalization]
    exact interchange_open_scalar_unit
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j)
      (scalarSixScalarAdjunction a X) (scalarSixScalarAdjunction a Z)
      (@derivedComapUpperStarIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom X Z j) K

private theorem interchange_normalized_square
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
-- Comparing exact and total-derived adjunction presentations needs more elaboration work.
/-- The square of `scalarProperOpenInterchangeSquare` for one object over plain schemes;
stating it here keeps the final unification away from the `Over` and constructibility
wrappers of the public statement. -/
private theorem interchange_scheme_square {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ W) [IsOpenImmersion i] [IsProper p]
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
        ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom c.obj.obj.i).hom.app A) =
    (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X)
        a.hom.hom i).hom.app
        ((RootCoordinateFace.lower Λ.X p).obj A) ≫
      (openImmersionLowerShriek Λ'.X i).mapDerivedCategory.map
        ((scalarDirectImageMate a p).app A) ≫ m' := by
  with_unfolding_all
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
    exact interchange_normalized_square
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
      (fun N ↦ (interchange_condensed_open_scalar_unit a i N).symm)
      (fun N ↦ (interchange_condensed_open_scalar_unit a c.obj.obj.i N).symm)
      (scalarInterchangeRestrictionSquare a p i c) A
      m m' hm hm'


/-- Coefficient change commutes with the normalized proper/open interchange square.

Source: latest blueprint, `det-prop-scalar-six-compact-support.proof.md`,
Composition paragraph, restriction calculation for the normalized interchange map
(blueprint: lem-sfb-scalar-proper-open-interchange-square).

The two composites are the canonical scalar extension, direct-image mate, and open
extension comparisons.  The maps `ι` and `ι'` are the identity-on-open normalized
interchange transformations over the two coefficient rings; their naturality is part
of being natural transformations.  No flatness assumption on the coefficient map is
made.

Proof:
1. Put B = Rp_* A and precompose both sides with the inverse of delta_i.
The resulting maps start at i'_! T_Y B. Listed coefficients are admissible,
so properOpenInterchange supplies the two uniquely normalized interchanges.
2. Use the exact derived open adjunction and the invertible open unit.
The cartesian restriction exchange identifies i^* Rr_* with Rp_* j'^*; it is
invertible by the proper/open interchange theorem. Equality can therefore be detected
by taking the open adjunct and then this exchange. The normalization of iota
says that this operation gives Rp_* of the j' open unit.
3. Apply lem-sfb-scalar-interchange-restriction-square to r, i, j', p: it is
the scalar exchange rectangle stated for the inverse theta defining
scalarDirectImageMate. This gives compatibility of the restriction exchange
with gamma, without inverting gamma.
4. The conjugate definition of derivedOpenImmersionShriekIso gives its open-unit
identities: restriction of delta_i inverse cancels the scalar pullback comparison,
and restriction of delta_j' carries the scalar image of the old open unit to
the new open unit. These follow by substitution and the scalar triangle identity.
5. Apply open restriction to the two composites. Naturality of the exchange,
the rectangle of step 3, the first identity of step 4, and the normalization of
iota reduce the left side to gamma_p followed by R'p_* of the primed open unit.
Naturality of gamma_p and the second identity of step 4 give that expression.
The right side gives the same expression by naturality of the primed open unit
and normalization of iota'. Detection in step 2 proves equality. All factors
are natural in A. No flatness or invertibility of gamma was used. -/
theorem scalarProperOpenInterchangeSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X Y Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsOpenImmersion i.left] [QuasiCompact i.left] [IsProper p.left]
    (c : Compactification.BoundaryCompactification (p.left ≫ i.left))
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (ι : RootCoordinateFace.lower Λ.X p.left ⋙
        (openImmersionLowerShriek Λ.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (_hι : ∀ A, compositionInterchangeIsNormalized Λ.X p.left i.left c A (ι.app A))
    (ι' : RootCoordinateFace.lower Λ'.X p.left ⋙
        (openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ'.X c.obj.obj.g)
    (_hι' : ∀ A, compositionInterchangeIsNormalized Λ'.X p.left i.left c A (ι'.app A))
    (A : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixChange a Ybar.left).map (ι.app A.obj) ≫
      (scalarDirectImageMate a c.obj.obj.g).app
        ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A.obj) ≫
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).map
        ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom c.obj.obj.i).hom.app A.obj) =
    (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X)
        a.hom.hom i.left).hom.app
        ((RootCoordinateFace.lower Λ.X p.left).obj A.obj) ≫
      (openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory.map
        ((scalarDirectImageMate a p.left).app A.obj) ≫
      ι'.app ((scalarSixChange a X.left).obj A.obj) := by
  exact interchange_scheme_square a p.left i.left c A.obj (ι.app A.obj)
    (ι'.app ((scalarSixChange a X.left).obj A.obj)) (_hι A.obj)
    (_hι' ((scalarSixChange a X.left).obj A.obj))

end AlgebraicGeometry.ProEtale.CondensedRing

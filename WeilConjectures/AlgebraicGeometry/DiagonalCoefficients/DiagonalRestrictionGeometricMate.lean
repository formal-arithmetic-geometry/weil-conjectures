/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement

/-! # The normalized diagonal restriction square is the geometric mate

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3) (blueprint: lem-sfb-diagonal-restriction-geometric-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private lemma factorsh_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (H : C ⥤ D) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (P : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      H.mapDerivedCategoryFactors.hom.app P := by
  have h := H.mapDerivedCategoryFactorsh_hom_app P
  change H.mapDerivedCategoryFactorsh.hom.app _ =
    H.mapDerivedCategory.map (𝟙 _) ≫ H.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at h
  erw [H.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at h
  repeat erw [Category.comp_id] at h
  erw [Category.id_comp] at h
  exact h

private lemma unitQ_homotopy
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (H : C ⥤ D) [H.Additive] (P : CochainComplex C ℤ) :
    H.rightDerivedFunctorUnitQ P =
      H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P) := by
  change 𝟙 _ ≫ H.rightDerivedFunctorUnit.app _ ≫
    H.rightDerivedFunctor.map (𝟙 _) = _
  erw [H.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
-- Elaborating this comparison expands several derived-functor constructions.
private theorem restriction_pull_fac
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (N : HomotopyCategory (Modules T S) (.up ℤ)) :
    (scalarRestrictionPullbackIso a f).inv.app (DerivedCategory.Qh.obj N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        ((CondensedRing.upperStar T f).leftDerivedFunctorCounit.app N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
        (((CondensedRing.upperStar T f).mapHomotopyCategory (.up ℤ)).obj N) =
    (derivedUpper R f).map
        ((Mod.comap (coefficientMap a S)).mapDerivedCategoryFactorsh.hom.app N) ≫
      (CondensedRing.upperStar R f).leftDerivedFunctorCounit.app
        (((Mod.comap (coefficientMap a S)).mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (CondensedRing.comapUpperStarIso a f).inv
          (.up ℤ)).app N) := by
  let F : Modules T S ⥤ Modules R S := Mod.comap (coefficientMap a S)
  let G := CondensedRing.upperStar R f
  let H := CondensedRing.upperStar T f
  let I : Modules T X ⥤ Modules R X := Mod.comap (coefficientMap a X)
  let e := CondensedRing.comapUpperStarIso a f
  have hG := NatTrans.congr_app G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj N)
  have hH := NatTrans.congr_app H.leftDerivedFunctorIsoMapDerivedCategory_hom_fac N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hG hH
  have hq := exactSquareFac F G H I e.symm N
  simp only [Iso.symm_hom] at hq
  have h := liftedSquareFac F.mapDerivedCategory G.mapDerivedCategory
    G.leftDerivedFunctor H.mapDerivedCategory H.leftDerivedFunctor I.mapDerivedCategory
    G.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedFunctorIsoMapDerivedCategory
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      (Functor.mapDerivedCategoryNatIso e).symm ≪≫ Functor.mapDerivedCategoryCompIso H I)
    (F.mapDerivedCategoryFactorsh.hom.app N)
    (G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.mapDerivedCategoryFactorsh.hom.app N)
    (I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N))
    (G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.leftDerivedFunctorCounit.app N) hG hH hq
  simpa only [F, G, H, I, e, derivedUpper, scalarRestrictionPullbackIso,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    CondensedRing.derivedComapUpperStarIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using h

set_option maxHeartbeats 2000000 in
-- The concrete module categories and derived adjunctions are expensive to elaborate.
/-- The full-unit-normalized restriction/direct-image transformation supplied by a
`RestrictionSquare` is the geometric adjunction mate of the inverse pullback
comparison. Source: blueprint latest, sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3), coefficient functors commuting with geometric pullback
(blueprint: lem-sfb-diagonal-restriction-geometric-mate).

Proof. Write `U,V` for scalar restriction and `l_C,p_C` for geometric pullback and
pushforward. Substitute the canonical-model unit equations into the normalization
of the supplied square. Naturality and cancellation of the model isomorphisms give
`V(u_T K) ≫ σ_QK ≫ RF_R(x_U K) = x_V(p_T K) ≫ Q(c_K) ≫ u_R(U K)`.
The inverse pullback comparison satisfies the left-derived counit factorization:
first check the localization equation for the exact functors, then substitute the
canonical exact/left-derived comparisons. The ordinary mate of its underived
square is `c.hom`, and this remains true after passage to homotopy categories.
Apply the general derived-mate factorization with the actual left-derived counits
and right-derived units. Its derived adjunctions are precisely the specified
geometric adjunctions, so it gives the same displayed equation for their mate `m`.
On a K-injective complex `K`, both `V(u_T K)` and `RF_R(x_U K)` are isomorphisms;
cancel them to get `σ_QK = m_QK`. Every derived object is isomorphic to such a
`QK`, so naturality proves `σ = m`. No preservation of K-injectives by `U` and no
flatness assumption is used. -/
theorem restriction_geometric_mate
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (D_R : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D_T : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (e_R : D_R.R = derivedLower R f)
    (e_T : D_T.R = derivedLower T f)
    (h_R : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D_R e_R)
    (h_T : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D_T e_T)
    (r : RestrictionSquare a f D_R D_T)
    (σ : derivedLower T f ⋙
        (Mod.comap (coefficientMap a S)).mapDerivedCategory ⟶
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙ derivedLower R f)
    (hσ : ∀ N : DerivedCategory (Modules T X),
      σ.app N =
        (Mod.comap (coefficientMap a S)).mapDerivedCategory.map
            ((eqToIso e_T).inv.app N) ≫
          r.iso.hom.app N ≫
          (eqToIso e_R).hom.app
            ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj N)) :
    σ = (mateEquiv
      (CondensedRing.derivedUpperStarLowerStarAdjunction T f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso a f).inv)).natTrans := by
  let U : Modules T X ⥤ Modules R X := Mod.comap (coefficientMap a X)
  let V : Modules T S ⥤ Modules R S := Mod.comap (coefficientMap a S)
  have hnorm (K : CochainComplex (Modules T X) ℤ) :
      V.mapDerivedCategory.map ((CondensedRing.lowerStar T f).rightDerivedFunctorUnitQ K) ≫
        σ.app (DerivedCategory.Q.obj K) ≫
        (derivedLower R f).map (U.mapDerivedCategoryFactors.hom.app K) =
      V.mapDerivedCategoryFactors.hom.app
          (((CondensedRing.lowerStar T f).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (CondensedRing.comapLowerStarIso a f).hom
            (.up ℤ)).app K) ≫
        (CondensedRing.lowerStar R f).rightDerivedFunctorUnitQ
          ((U.mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [← h_T K, hσ]
    have ht : V.mapDerivedCategory.map
          ((eqToIso e_T).hom.app (DerivedCategory.Q.obj K)) ≫
        V.mapDerivedCategory.map ((eqToIso e_T).inv.app (DerivedCategory.Q.obj K)) =
          𝟙 _ := by
      rw [← V.mapDerivedCategory.map_comp, Iso.hom_inv_id_app,
        V.mapDerivedCategory.map_id]
    erw [Functor.map_comp]
    repeat' erw [Category.assoc]
    erw [reassoc_of% ht]
    have hn := (eqToIso e_R).hom.naturality (U.mapDerivedCategoryFactors.hom.app K)
    erw [← hn]
    erw [reassoc_of% (r.normalization K)]
    erw [h_R ((U.mapHomologicalComplex (.up ℤ)).obj K)]
  let m : derivedLower T f ⋙ V.mapDerivedCategory ⟶
      U.mapDerivedCategory ⋙ derivedLower R f := (mateEquiv
    (CondensedRing.derivedUpperStarLowerStarAdjunction T f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso a f).inv)).natTrans
  have hmate (K : HomotopyCategory (Modules T X) (.up ℤ)) :
      V.mapDerivedCategory.map ((CondensedRing.lowerStar T f).rightDerivedFunctorUnit.app K) ≫
        m.app (DerivedCategory.Qh.obj K) ≫
        (derivedLower R f).map (U.mapDerivedCategoryFactorsh.hom.app K) =
      V.mapDerivedCategoryFactorsh.hom.app
          (((CondensedRing.lowerStar T f).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (CondensedRing.comapLowerStarIso a f).hom
            (.up ℤ)).app K) ≫
        (CondensedRing.lowerStar R f).rightDerivedFunctorUnit.app
          ((U.mapHomotopyCategory (.up ℤ)).obj K) := by
    let l := CondensedRing.upperStar T f
    let p := CondensedRing.lowerStar T f
    let l' := CondensedRing.upperStar R f
    let p' := CondensedRing.lowerStar R f
    let d := CondensedRing.comapUpperStarIso a f
    let c := CondensedRing.comapLowerStarIso a f
    let aT := CondensedRing.upperStarLowerStarAdjunction T f
    let aR := CondensedRing.upperStarLowerStarAdjunction R f
    let s : TwoSquare (V.mapHomotopyCategory (.up ℤ))
        (l.mapHomotopyCategory (.up ℤ)) (l'.mapHomotopyCategory (.up ℤ))
        (U.mapHomotopyCategory (.up ℤ)) := TwoSquare.mk _ _ _ _
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (V ⋙ l')) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory d.inv (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (l ⋙ U)) (.up ℤ)).inv)
    have hs (N : HomotopyCategory (Modules T S) (.up ℤ)) : s.natTrans.app N =
        (NatTrans.mapHomotopyCategory d.inv (.up ℤ)).app N := by
      have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (l ⋙ U)) (.up ℤ)).inv.app N =
          𝟙 _ := by
        rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (l ⋙ U)) (.up ℤ)).hom.app N), Iso.hom_inv_id_app,
          Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
      simp only [s, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
        Functor.mapHomotopyCategoryCompIso_refl_hom_app, hi, Category.id_comp]
      erw [Category.comp_id]
    have hOrd : (mateEquiv aT aR (TwoSquare.mk _ _ _ _ d.inv)).natTrans = c.hom := by
      exact (aT.isMateSquare_iff aR d c).mp
        (CondensedRing.isMateSquare_comapUpperStarIso_comapLowerStarIso a f)
    have hOrdH : (mateEquiv (aT.mapHomotopyCategory (.up ℤ))
        (aR.mapHomotopyCategory (.up ℤ)) s).natTrans.app K =
        (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app K := by
      have hh := CategoryTheory.Adjunction.homotopyMate aT aR
        (TwoSquare.mk _ _ _ _ d.inv) K
      rw [hOrd] at hh
      simpa [mateEquiv_apply, hs] using hh.symm
    have h := (aT.mapHomotopyCategory (.up ℤ)).derived_mateEquiv_app_fac
      (aR.mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso (Modules T S) (.up ℤ))
      (HomotopyCategory.quasiIso (Modules T X) (.up ℤ))
      (HomotopyCategory.quasiIso (Modules R S) (.up ℤ))
      (HomotopyCategory.quasiIso (Modules R X) (.up ℤ))
      l.leftDerivedFunctorCounit p.rightDerivedFunctorUnit
      l'.leftDerivedFunctorCounit p'.rightDerivedFunctorUnit
      V.mapDerivedCategoryFactorsh.hom U.mapDerivedCategoryFactorsh.hom
      s (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso a f).inv) K
      (by simpa only [hs, U, V, l, p, l', p', d, derivedUpper] using
        restriction_pull_fac a f ((p.mapHomotopyCategory (.up ℤ)).obj K))
    rw [hOrdH] at h
    exact h
  have hmateQ (P : CochainComplex (Modules T X) ℤ) :
      V.mapDerivedCategory.map ((CondensedRing.lowerStar T f).rightDerivedFunctorUnitQ P) ≫
        m.app (DerivedCategory.Q.obj P) ≫
        (derivedLower R f).map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app
          (((CondensedRing.lowerStar T f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (CondensedRing.comapLowerStarIso a f).hom
            (.up ℤ)).app P) ≫
        (CondensedRing.lowerStar R f).rightDerivedFunctorUnitQ
          ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
    have h := hmate ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    erw [factorsh_hom V (((CondensedRing.lowerStar T f).mapHomologicalComplex (.up ℤ)).obj P),
      factorsh_hom U P] at h
    simp only [unitQ_homotopy]
    convert (config := { transparency := .all }) h using 1 <;> rfl
  change σ = m
  apply NatTrans.ext
  funext N
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hP
  have : IsIso ((CondensedRing.lowerStar T f).rightDerivedFunctorUnitQ P) := by
    dsimp only [Functor.rightDerivedFunctorUnitQ]
    infer_instance
  have hQ : σ.app (DerivedCategory.Q.obj P) = m.app (DerivedCategory.Q.obj P) := by
    apply (cancel_epi (V.mapDerivedCategory.map
      ((CondensedRing.lowerStar T f).rightDerivedFunctorUnitQ P))).1
    apply (cancel_mono ((derivedLower R f).map
      (U.mapDerivedCategoryFactors.hom.app P))).1
    simpa only [Category.assoc] using (hnorm P).trans (hmateQ P).symm
  apply (cancel_mono ((U.mapDerivedCategory ⋙ derivedLower R f).map e.hom)).1
  rw [← σ.naturality e.hom, ← m.naturality e.hom, hQ]

#print axioms restriction_geometric_mate

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

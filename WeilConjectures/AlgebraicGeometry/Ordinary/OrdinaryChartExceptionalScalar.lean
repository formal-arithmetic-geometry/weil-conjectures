/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartIdentityScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCounitScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumNormalization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
import all WeilConjectures.AlgebraicGeometry.Affine.AffineCounitScalar
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianDerivedExchangePlusCompatibility
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartNormalizationBoundary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumBoundaryScalar
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumScalarRepresentative
public import WeilConjectures.AlgebraicGeometry.OrdinaryChart.OrdinaryChartAdjunctionObjects
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Ordinary exceptional coefficient comparison on one coordinate chart

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] affineTraceTower
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

private theorem open_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategoryModule A V) :
    (ExceptionalCoefficients.openIso φ j).hom.app
        ((ordinaryFinitePullback A j).obj K) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarPullbackIso φ j).inv.app K) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) j).symm).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) j).symm).counit.app K) := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let v := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x v).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom)
  have he : α.natTrans = (scalarPullbackIso φ j).inv :=
    (scalarPullbackIso_inv_mate_restriction φ j).1.symm
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b v x
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom))
  change ((mateEquiv a b).symm α).natTrans = _ at h
  change ((mateEquiv a b).symm α).natTrans = (ExceptionalCoefficients.openIso φ j).inv at h
  have hc := mateEquiv_counit_symm a b α K
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
    ((mateEquiv a b).symm α).natTrans.app _ ≫
      (scalarExtension φ V).map (a.counit.app K) at hc
  rw [he, h] at hc
  have hh := congrArg (fun z ↦ (ExceptionalCoefficients.openIso φ j).hom.app
    ((ordinaryFinitePullback A j).obj K) ≫ z) hc
  simpa only [a, b, ordinaryFinitePullback, Category.assoc,
    Iso.hom_inv_id_app_assoc] using hh

/-- Scalar compatibility of the normalized identity compactification.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).

Proof: At the sheaf level identify extension by zero and inverse image for the identity by
left-adjoint uniqueness, and derive its actual counit normalization. The open coefficient mate
counit square and the normalized identity pullback comparison then determine the coefficient
square for the derived open-identity isomorphism.
For the proper identity comparison, use the direct-image scalar identity normalization; exactness
of the sheaf identity direct image supplies the required derived comparison normalization.
Expand the identity compactification coefficient arrow as the proper scalar mate followed by
direct image of the open comparison. Naturality moves the open-identity map across the proper
scalar mate; substitute the open and proper identity coefficient squares and cancel the identity
unitors. -/
private theorem chart_identity_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    let eA := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    let eB := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso B S
    (compactScalarMap φ (Compactification.ofIsProper (𝟙 S))).app K ≫
        eB.hom.app ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map (eA.hom.app K) := by
  dsimp only
  have hn := (scalarMate φ (𝟙 S)).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have ho := congrArg (fun z ↦ (rightDerivedLowerStar (ModuleCat.{u + 1} B)
    (𝟙 S)).map z) (identity_open_scalar φ S K)
  simp only [Functor.map_comp, rightDerivedLowerStar] at ho
  simp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    Compactification.ofIsProper, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% ho, ← reassoc_of% hn]
  change (scalarExtension φ S).map
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 S)).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
        (scalarMate φ (𝟙 S)).app K ≫ 𝟙 _ ≫
          (rightDerivedLowerStarIdIso B S).hom.app ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 S)).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
          (scalarExtension φ S).map (𝟙 _) ≫
          (scalarExtension φ S).map ((rightDerivedLowerStarIdIso A S).hom.app K)
  simp only [Category.id_comp]
  rw [identity_direct_scalar]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]

private theorem rightAdjointUniq_scalar_of_counits
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G J : D ⥤ C} {F' : C' ⥤ D'} {G' J' : D' ⥤ C'}
    (g : F ⊣ G) (j : F ⊣ J) (g' : F' ⊣ G') (j' : F' ⊣ J')
    (S : C ⥤ C') (T : D ⥤ D') (b : F ⋙ T ⟶ S ⋙ F')
    (K : D) (q : S.obj (G.obj K) ⟶ G'.obj (T.obj K))
    (a : S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (hq : b.app (G.obj K) ≫ F'.map q ≫ g'.counit.app (T.obj K) =
      T.map (g.counit.app K))
    (hb : Epi (b.app (G.obj K)))
    (ha : b.app (J.obj K) ≫ F'.map a ≫ j'.counit.app (T.obj K) =
      T.map (j.counit.app K)) :
    S.map ((g.rightAdjointUniq j).hom.app K) ≫ a =
      q ≫ (g'.rightAdjointUniq j').hom.app (T.obj K) := by
  have := hb
  apply (j'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (b.app (G.obj K))).mp
  rw [g'.rightAdjointUniq_hom_app_counit j']
  rw [hq]
  have hn := b.naturality ((g.rightAdjointUniq j).hom.app K)
  change T.map (F.map _) ≫ b.app (J.obj K) =
    b.app (G.obj K) ≫ F'.map (S.map _) at hn
  rw [← reassoc_of% hn, ha, ← T.map_comp, g.rightAdjointUniq_hom_app_counit j]

private def scalarComposite
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {M : D ⥤ E} {L' : C' ⥤ D'} {M' : D' ⥤ E'}
    {S : C ⥤ C'} {T : D ⥤ D'} {U : E ⥤ E'}
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M') :
    (L ⋙ M) ⋙ U ⟶ S ⋙ (L' ⋙ M') where
  app X := γ.app (L.obj X) ≫ M'.map (β.app X)
  naturality X Y f := by
    have hγ := γ.naturality (L.map f)
    have hβ := β.naturality f
    simp only [Functor.comp_map] at hγ hβ ⊢
    rw [← Category.assoc, hγ, Category.assoc, ← M'.map_comp, hβ]
    simp only [Functor.map_comp, Category.assoc]

private theorem compose_counit_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {Q : E ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {M' : D' ⥤ E'} {Q' : E' ⥤ D'}
    (a : L ⊣ R) (b : M ⊣ Q) (a' : L' ⊣ R') (b' : M' ⊣ Q')
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M')
    (K : E) (r : S.obj (R.obj (Q.obj K)) ⟶ R'.obj (T.obj (Q.obj K)))
    (q : T.obj (Q.obj K) ⟶ Q'.obj (U.obj K))
    (hr : β.app (R.obj (Q.obj K)) ≫ L'.map r ≫ a'.counit.app (T.obj (Q.obj K)) =
      T.map (a.counit.app (Q.obj K)))
    (hq : γ.app (Q.obj K) ≫ M'.map q ≫ b'.counit.app (U.obj K) =
      U.map (b.counit.app K)) :
    γ.app (L.obj (R.obj (Q.obj K))) ≫ M'.map (β.app (R.obj (Q.obj K))) ≫
      M'.map (L'.map (r ≫ R'.map q)) ≫ (a'.comp b').counit.app (U.obj K) =
      U.map ((a.comp b).counit.app K) := by
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality q
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg (fun z ↦ M'.map z) hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  have hr' := congrArg (fun z ↦ M'.map z) hr
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have hm := γ.naturality (a.counit.app (Q.obj K))
  simp only [Functor.comp_map] at hm
  rw [← reassoc_of% hm, hq, ← U.map_comp]

private theorem composite_left_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {F Fc : C ⥤ D} {G Gc : D ⥤ E}
    {F' Fc' : C' ⥤ D'} {G' Gc' : D' ⥤ E'}
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (f : F ⋙ T ⟶ S ⋙ F') (fc : Fc ⋙ T ⟶ S ⋙ Fc')
    (g : G ⋙ U ⟶ T ⋙ G') (gc : Gc ⋙ U ⟶ T ⋙ Gc')
    (a : F ≅ Fc) (a' : F' ≅ Fc') (b : G ≅ Gc) (b' : G' ≅ Gc')
    (ha : ∀ X, T.map (a.hom.app X) ≫ fc.app X = f.app X ≫ a'.hom.app (S.obj X))
    (hb : ∀ Y, U.map (b.hom.app Y) ≫ gc.app Y = g.app Y ≫ b'.hom.app (T.obj Y))
    (X : C) :
    U.map (G.map (a.hom.app X) ≫ b.hom.app (Fc.obj X)) ≫
        gc.app (Fc.obj X) ≫ Gc'.map (fc.app X) =
      g.app (F.obj X) ≫ G'.map (f.app X) ≫
        G'.map (a'.hom.app (S.obj X)) ≫ b'.hom.app (Fc'.obj (S.obj X)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hb (Fc.obj X))]
  have hn := g.naturality (a.hom.app X)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn' := b'.hom.naturality (fc.app X)
  simp only [Functor.comp_obj] at hn'
  rw [← hn']
  rw [← G'.map_comp_assoc, ha, G'.map_comp]
  simp only [Category.assoc]

private theorem transported_counit_scalar
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F H : C ⥤ D} {J : D ⥤ C} {F' H' : C' ⥤ D'} {J' : D' ⥤ C'}
    (a : H ⊣ J) (a' : H' ⊣ J') (e : H ≅ F) (e' : H' ≅ F')
    (S : C ⥤ C') (T : D ⥤ D')
    (β : F ⋙ T ⟶ S ⋙ F') (γ : H ⋙ T ⟶ S ⋙ H')
    (K : D) (r : S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (hs : ∀ X, T.map (e.hom.app X) ≫ β.app X = γ.app X ≫ e'.hom.app (S.obj X))
    (hc : γ.app (J.obj K) ≫ H'.map r ≫ a'.counit.app (T.obj K) =
      T.map (a.counit.app K)) :
    β.app (J.obj K) ≫ F'.map r ≫
      (a'.ofNatIsoLeft e').counit.app (T.obj K) =
        T.map ((a.ofNatIsoLeft e).counit.app K) := by
  apply (cancel_epi (T.map (e.hom.app (J.obj K)))).mp
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp]
  rw [reassoc_of% (hs (J.obj K))]
  have hn := e'.inv.naturality r
  rw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc, ← T.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hc

private def affineLeftScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (S : Scheme.{u}) (d : ℕ) :
    affineTraceLeft A S d ⋙ scalarExtension φ S ⟶
      scalarExtension φ (affineTraceTower S d) ⋙ affineTraceLeft B S d :=
  affineTraceExchangeTower
    (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
    (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
    (fun r ↦ scalarExtension φ (affineTraceTower S r))
    (fun r ↦ compactScalarMap φ (affineTraceLineCompactification
      (affineTraceTower S r))) d

/-- Unbounded scalar compatibility of graph-normalized etale compact support.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).

Proof: Represent the arbitrary derived input by a complex whose terms are flat and which is native
K-flat: take a K-flat homotopy representative and a termwise flat K-flat quasi-isomorphic
replacement.
On this representative paste the scalar graph-boundary square, the exact-derived sum
representative square and the two graph-normalization boundary equations. Identify the open
comparison by its prescribed inverse-unit normalization, and cancel the invertible scalar
representative.
Cancel the normalization isomorphisms to obtain the forward comparison square on the
representative. Naturality of both composite natural transformations transports the equation along
the representative isomorphism to the given derived object. -/
private theorem chart_sum_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (NA : EtaleCompactSupportNormalization A)
    (NB : EtaleCompactSupportNormalization B) (L : DerivedCategoryModule A X) :
    (compactScalarMap φ c).app L ≫
        (NB.comparison f c).hom.app ((scalarExtension φ X).obj L) =
      (scalarExtension φ Y).map ((NA.comparison f c).hom.app L) ≫
        (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app L := by
  obtain ⟨H, hH, ⟨eH⟩⟩ := DerivedCategory.exists_kFlat_iso L
  obtain ⟨H, rfl⟩ := H.quotient_obj_surjective
  obtain ⟨P, π, hπ, hf, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat H
  have := hπ
  let eP := asIso (DerivedCategory.Q.map π) ≪≫ eH
  have := scalarRepresentative_isIso φ X P hP
  have hcalc := ordinaryChartSumBoundaryScalar φ f c P hP hf
  have hsum := ordinaryChartSumScalarRepresentative φ f P
  change (scalarExtension φ Y).map _ ≫ _ ≫ _ =
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app
      (DerivedCategory.Q.obj P) ≫ _ ≫ _ at hsum
  have hNA := ordinaryChartNormalizationBoundary A NA f c P
  have hNB := ordinaryChartNormalizationBoundary B NB f c
    (coefficientExtendedComplex φ X P)
  have hmodel :
      (Etale.scalarExtension φ Y).map ((NA.comparison f c).inv.app
          (DerivedCategory.Q.obj P)) ≫ (compactScalarMap φ c).app (DerivedCategory.Q.obj P) =
        (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app
          (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).inv.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) := by
    apply (cancel_mono ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} B) c).map (Etale.scalarExtensionRepresentative φ X P))).mp
    have h := congrArg (fun z ↦
      (Etale.scalarExtension φ Y).map
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f
          inferInstance).mapDerivedCategoryFactors.hom.app
          P) ≫ z) hcalc
    dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
      properCoefficientMap] at *
    simp only [Category.assoc] at h ⊢
    rw [← Functor.map_comp_assoc, hNA] at h
    rw [reassoc_of% hsum, hNB] at h
    have hn := (NB.comparison f c).inv.naturality
      (Etale.scalarExtensionRepresentative φ X P)
    dsimp only [Functor.comp_map] at hn
    rw [hn] at h
    have hopen : (ExceptionalCoefficients.openIso φ c.i).hom.app
        (DerivedCategory.Q.obj P) =
        (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).hom := by
      have h : ((ExceptionalCoefficients.openIso φ c.i).app
          (DerivedCategory.Q.obj P)).symm =
          (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).symm := by
        apply Iso.ext
        exact compactScalarOpen_normalization φ c.i (DerivedCategory.Q.obj P)
      exact congrArg (fun e ↦ e.inv) h
    simpa only [hopen, compactScalarMap, Category.assoc,
      Etale.rightDerivedLowerShriekOfCompactification, Etale.rightDerivedLowerStar,
      Functor.comp_map] using h
  have hQP :
      (compactScalarMap φ c).app (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).hom.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) =
        (Etale.scalarExtension φ Y).map
            ((NA.comparison f c).hom.app (DerivedCategory.Q.obj P)) ≫
          (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom.app
            (DerivedCategory.Q.obj P) := by
    apply (cancel_epi ((Etale.scalarExtension φ Y).map
      ((NA.comparison f c).inv.app (DerivedCategory.Q.obj P)))).mp
    simp only [← Category.assoc, hmodel]
    simp only [Category.assoc, Iso.inv_hom_id_app,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  let α := Etale.compactScalarMap φ c ≫
    Functor.whiskerLeft (Etale.scalarExtension φ X) (NB.comparison f c).hom
  let β := Functor.whiskerRight (NA.comparison f c).hom (Etale.scalarExtension φ Y) ≫
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ f).hom
  have hQP' : α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using hQP
  have hL : α.app L = β.app L := by
    apply (cancel_epi
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c ⋙ Etale.scalarExtension φ Y).map eP.hom)).mp
    rw [α.naturality eP.hom, β.naturality eP.hom, hQP']
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using hL


attribute [local irreducible] affineLeftScalar

/- The two exact-derived adjunction presentations have the same counit.
This is checked on complex representatives using their localization formulas. -/
private theorem chart_exact_factor
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (_root_.DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        _root_.DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : _root_.DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    _root_.DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  change (𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ 𝟙 _) =
    F.mapDerivedCategoryFactors.hom.app P
  simp only [Category.id_comp, Category.comp_id]

private theorem chart_exact_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex D ℤ) :
    a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) := by
  have h := a.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  change a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) = _ at h
  rw [h]
  change F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) = _
  rw [chart_exact_factor, chart_exact_factor]

private theorem chart_derived_adj_eq (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction =
      derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  rw [chart_exact_counit]
  rw [derivedEtaleLowerShriekUpperStarAdjunction, Adjunction.localization_counit_app]
  rfl

private theorem chart_inverse_mate_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R')
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    (x : TwoSquare R H G R') (i : G ≅ G') (j : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk R H' G' R'
        (Functor.whiskerLeft R i.inv ≫ x.natTrans ≫ Functor.whiskerRight j.hom R'))).natTrans =
      Functor.whiskerRight i.inv L' ≫ ((mateEquiv a b).symm x).natTrans ≫
        Functor.whiskerLeft L j.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp]
  have hi := i.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hi
  rw [← L'.map_comp_assoc, hi, L'.map_comp]
  simp only [Category.assoc]
  have hj := b.counit.naturality (j.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hj
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hj]

private theorem chart_exact_pullback_inverse_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) :
    ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))).symm
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIsoSheaf φ e)).hom)).natTrans =
      (properOpenCoefficientPullbackIso φ e).inv := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ e).hom
  let i := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  let j := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
          i.inv ≫ x.natTrans ≫
          Functor.whiskerRight j.hom
            (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
    ext M
    dsimp only [x, i, j, scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [heq, chart_inverse_mate_transport a b x i j]
  have hm : ((mateEquiv a b).symm x).natTrans = (scalarPullbackIso φ e).inv :=
    (scalarPullbackIso_inv_mate_restriction φ e).1.symm
  rw [hm]
  ext M
  simp only [properOpenCoefficientPullbackIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, i, j,
    Category.assoc, scalarExtension, ProEtale.pbcFixedScalarExtension]

attribute [local irreducible] affineLeftScalar

private theorem sum_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] (K : DerivedCategoryModule A V) :
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app
        ((ordinaryFinitePullback A e).obj K) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
        ((scalarPullbackIso φ e).inv.app K) ≫
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) e).symm).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      (((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) e).symm).counit.app K) := by
  have h :
      (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
        (etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction.counit.app
          ((scalarExtension φ V).obj K) =
      (scalarExtension φ V).map
        ((etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction.counit.app K) := by
    let a := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction
    let b := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction
    let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
    let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
    let α := (mateEquiv x z).symm (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom)
    have hm := congrArg TwoSquare.natTrans
      (iterated_mateEquiv_conjugateEquiv_symm a b z x
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom))
    change ((mateEquiv a b).symm α).natTrans =
      (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).inv at hm
    have h := mateEquiv_counit_symm a b α K
    change (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
        (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
      ((mateEquiv a b).symm α).natTrans.app _ ≫
        (scalarExtension φ V).map (a.counit.app K) at h
    rw [hm, chart_exact_pullback_inverse_mate φ e] at h
    have hh := congrArg (fun t ↦ (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫ t) h
    simpa only [a, b, Category.assoc, Iso.hom_inv_id_app_assoc] using hh
  let jA := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  let jB := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e
  have hn := (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.naturality
    (jA.hom.app K)
  simp only [Functor.comp_map] at hn
  have hh := congrArg (fun z ↦ (scalarExtension φ V).map
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
      (jA.hom.app K)) ≫ z) h
  simp only [properOpenCoefficientPullbackIso,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, Functor.map_comp,
    Category.assoc] at hh
  rw [reassoc_of% hn] at hh
  dsimp only [jA, jB] at hh
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Adjunction.ofNatIsoRight_counit,
    chart_derived_adj_eq,
    NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, ordinaryFinitePullback,
    Iso.symm_inv, Functor.map_comp, Category.assoc, jA, jB] using hh

private theorem line_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (DB : OrdinaryFiniteP1Datum B N hB tB S hS)
    (K : DerivedCategoryModule A S) :
    (compactScalarMap φ (affineTraceLineCompactification S)).app
        ((affineTraceLineRight A N hA S).obj K) ≫
      (affineTraceLineLeft B S).map
        (ProEtale.reductionEtaleLineScalarIso φ S N hA hB hS K).hom ≫
      (affineTraceLineAdjunction B N hB tB S hS DB).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceLineAdjunction A N hA tA S hS DA).counit.app K) := by
  have h := compose_counit_scalar
    (affineTraceOpenAdjunction A S) DA.adjunction
    (affineTraceOpenAdjunction B S) DB.adjunction
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S))
    (scalarExtension φ (ProjectiveLine S)) (scalarExtension φ S)
    (ExceptionalCoefficients.openIso φ (ProjectiveLine.affineChart S)).hom
    (scalarMate φ (ProjectiveLine S ↘ S)) K
    ((scalarPullbackIso φ (ProjectiveLine.affineChart S)).inv.app
      ((ordinaryFiniteP1Right A N hA S).obj K))
    (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom
    (by simpa only [affineTraceOpenAdjunction, affineTraceOpenLeft] using
      (open_scalar_counit φ (ProjectiveLine.affineChart S)
        ((ordinaryFiniteP1Right A N hA S).obj K)))
    (ordinaryChartP1CounitScalar φ N hN hA hB S hS tA tB DA DB K)
  simpa only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    affineTraceLineCompactification, Compactification.copy, Functor.comp_map,
    ProEtale.reductionEtaleLineScalarIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, affineTraceLineAdjunction, affineTraceComposeAdjunction_eq,
    affineTraceOpenLeft, affineTraceLineRight, affineTraceLineLeft,
    rightDerivedLowerShriekOfCompactification, ordinaryFinitePushforward, rightDerivedLowerStar,
    Functor.comp_obj, Category.assoc] using h

private theorem affine_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (d : ℕ) (K : DerivedCategoryModule A S) :
    (affineLeftScalar φ S d).app ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLeft B S d).map
        (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom ≫
      (affineTraceAdjunction B N hB tB PB S hS d).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map ((affineTraceAdjunction A N hA tA PA S hS d).counit.app K) := by
  have hr : ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K =
      affineTraceRightExchangeTower
        (fun r ↦ affineTraceLineRight A N hA (affineTraceTower S r))
        (fun r ↦ affineTraceLineRight B N hB (affineTraceTower S r))
        (fun r ↦ scalarExtension φ (affineTraceTower S r))
        (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
          N hA hB (affineTraceInvertible _ S hS r)) d K := by
    unfold ProEtale.reductionEtaleAffineScalarIso
    exact right_exchange_rec_eq
      (fun r ↦ affineTraceLineRight A N hA (affineTraceTower S r))
      (fun r ↦ affineTraceLineRight B N hB (affineTraceTower S r))
      (fun r ↦ scalarExtension φ (affineTraceTower S r))
      (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
        N hA hB (affineTraceInvertible _ S hS r)) d K
  rw [hr]
  unfold affineTraceAdjunction affineLeftScalar
  apply tower_counit_scalar
  intro r
  have : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
  exact line_scalar_counit φ N hN hA hB (affineTraceTower S r)
    (affineTraceInvertible _ S hS r) tA tB _ _ _

private theorem affine_left_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (c : Compactification (affineTraceProjection S 0)) :
    OrdinaryChart.affineLeftIso A S 0 c =
      (Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
      rightDerivedLowerShriekOfCompactificationIso A
        (Compactification.ofIsProper (𝟙 S)) c := rfl

private theorem affine_left_succ
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S (d + 1))) :
    OrdinaryChart.affineLeftIso A S (d + 1) c =
      let cp := HasCompactification.compactification (affineTraceProjection S d)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationIso A
          (affineTraceLineCompactification (affineTraceTower S d)) ce.restrict) _ ≪≫
      Functor.isoWhiskerLeft _ (OrdinaryChart.affineLeftIso A S d cp) ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c := rfl

private theorem affine_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (scalarExtension φ S).map
        ((OrdinaryChart.affineLeftIso A S d c).hom.app K) ≫
      (compactScalarMap φ c).app K =
    (affineLeftScalar φ S d).app K ≫
      (OrdinaryChart.affineLeftIso B S d c).hom.app
        ((scalarExtension φ (affineTraceTower S d)).obj K) := by
  induction d with
  | zero =>
    have hi := chart_identity_scalar φ S K
    have hr := ordinaryChartCompactificationScalar φ
      (Compactification.ofIsProper (𝟙 S)) c K
    rw [affine_left_zero, affine_left_zero]
    simp only [Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
      affineLeftScalar, affineTraceExchangeTower_zero]
    rw [hr]
    apply (cancel_epi ((scalarExtension φ S).map
      ((Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
          Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).hom.app K))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← hi]
    simp only [Category.assoc, affineTraceTower]
    erw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  | succ d ih =>
    have : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
    have : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    have : IsNoetherian (affineTraceTower S (d + 1)) := affineTraceNoetherian S (d + 1)
    let cp := HasCompactification.compactification (affineTraceProjection S d)
    let ce := c.ofComp cp
    let cl := affineTraceLineCompactification (affineTraceTower S d)
    have hr := ordinaryChartCompactificationScalar φ (cp.comp ce) c K
    have ht := ordinaryChartCompactTowerScalar φ
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d) cp ce K
    have hl := ordinaryChartCompactificationScalar φ cl ce.restrict
    have hf := composite_left_scalar
      (scalarExtension φ (AffineSpace PUnit.{u + 1} (affineTraceTower S d)))
      (scalarExtension φ (affineTraceTower S d)) (scalarExtension φ S)
      (compactScalarMap φ cl) (compactScalarMap φ ce.restrict)
      (affineLeftScalar φ S d) (compactScalarMap φ cp)
      (rightDerivedLowerShriekOfCompactificationIso A cl ce.restrict)
      (rightDerivedLowerShriekOfCompactificationIso B cl ce.restrict)
      (OrdinaryChart.affineLeftIso A S d cp)
      (OrdinaryChart.affineLeftIso B S d cp) hl (ih cp) K
    have hp := congrArg (fun z ↦ z ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B cp ce).hom.app
        ((scalarExtension φ (affineTraceTower S (d + 1))).obj K) ≫
      (rightDerivedLowerShriekOfCompactificationIso B (cp.comp ce) c).hom.app
        ((scalarExtension φ (affineTraceTower S (d + 1))).obj K)) hf
    simp only [Category.assoc] at hp
    erw [← reassoc_of% ht] at hp
    erw [← hr] at hp
    simpa only [affine_left_succ, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      affineLeftScalar, affineTraceExchangeTower_succ, Category.assoc,
      affineTraceLeft, affineTraceLeftTower, affineTraceLineLeft,
      rightDerivedLowerShriekOfCompactification,
      affineTraceLineCompactification, Compactification.copy, affineTraceOpenLeft,
      ordinaryFinitePushforward, rightDerivedLowerStar, Functor.comp_obj,
      affineTraceTower, cp, ce, cl] using hp

private theorem exceptional_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [HasCompactification g] (K : DerivedCategoryModule A S) :
    (compactScalarMap φ (HasCompactification.compactification g)).app
        ((rightDerivedUpperShriek A g).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
        (ExceptionalCoefficients.mateMap φ g K) ≫
      (rightDerivedUpperShriekAdjunction B g).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((rightDerivedUpperShriekAdjunction A g).counit.app K) := by
  have hi := compactScalarMap_isIso φ (HasCompactification.compactification g)
    ((rightDerivedUpperShriek A g).obj K)
  have he := ((rightDerivedUpperShriekAdjunction B g).homEquiv _ _).symm_apply_apply
      (ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification g)
        ((rightDerivedUpperShriek A g).obj K) ≫
      (scalarExtension φ S).map
        ((rightDerivedUpperShriekAdjunction A g).counit.app K))
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
      (ExceptionalCoefficients.mateMap φ g K) ≫ _ = _ at he
  simp only [Functor.id_obj] at he
  erw [he]
  have hi' : IsIso (ExceptionalCoefficients.compactSupportMap φ
      (HasCompactification.compactification g)
      ((rightDerivedUpperShriek A g).obj K)) := hi
  simp only [ExceptionalCoefficients.comparisonInverse, dif_pos hi',
    compactScalarMap, IsIso.hom_inv_id_assoc]

private theorem chart_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A S) :
    (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom
        (affineLeftScalar φ S d)).app
        ((ordinaryFinitePullback A e).obj ((affineTraceRight A N hA S d).obj K)) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory ⋙
          affineTraceLeft B S d).map
        (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom ≫
      (OrdinaryChart.adjunction B S N hB tB PB hS d e).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((OrdinaryChart.adjunction A S N hA tA PA hS d e).counit.app K) := by
  have h := compose_counit_scalar
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm)
    (affineTraceAdjunction A N hA tA PA S hS d)
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e).symm)
    (affineTraceAdjunction B N hB tB PB S hS d)
    (scalarExtension φ U) (scalarExtension φ (affineTraceTower S d)) (scalarExtension φ S)
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom (affineLeftScalar φ S d)
    K ((scalarPullbackIso φ e).inv.app ((affineTraceRight A N hA S d).obj K))
    (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom
    (sum_scalar_counit φ e _) (affine_scalar_counit φ N hN hA hB S hS tA tB PA PB d K)
  simpa only [scalarComposite, OrdinaryChart.adjunction,
    ProEtale.reductionEtaleChartScalarIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc, ordinaryFinitePullback,
    affineTraceLeft] using h

private theorem ambient_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (MA : EtaleCompactSupportNormalization A)
    (MB : EtaleCompactSupportNormalization B)
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (e : U ⟶ V) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (f : V ⟶ S) (c : Compactification f) (d : Compactification (e ≫ f))
    (K : DerivedCategoryModule A U) :
    (scalarExtension φ S).map ((etaleAmbientLeftComparison A MA e f c d).hom.app K) ≫
      (compactScalarMap φ d).app K =
    (compactScalarMap φ c).app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K) ≫
      (etaleAmbientLeftComparison B MB e f c d).hom.app
        ((scalarExtension φ U).obj K) := by
  let ce := d.ofComp c
  have hr := ordinaryChartCompactificationScalar φ (c.comp ce) d K
  have ht := ordinaryChartCompactTowerScalar φ e f c ce K
  have hn := (compactScalarMap φ c).naturality ((MA.comparison e ce.restrict).inv.app K)
  simp only [Functor.comp_map] at hn
  have hs := chart_sum_normalization φ e ce.restrict MA MB K
  have hsi : (scalarExtension φ V).map ((MA.comparison e ce.restrict).inv.app K) ≫
      (compactScalarMap φ ce.restrict).app K =
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K ≫
      (MB.comparison e ce.restrict).inv.app ((scalarExtension φ U).obj K) := by
    apply (cancel_mono ((MB.comparison e ce.restrict).hom.app
      ((scalarExtension φ U).obj K))).mp
    simp only [Category.assoc, hs, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      ]
    erw [Category.comp_id]
  have hmap := congrArg (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} B) c).map hsi
  simp only [Functor.map_comp] at hmap
  simp only [etaleAmbientLeftComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  erw [hr, reassoc_of% ht, reassoc_of% hn]
  erw [reassoc_of% hmap]
  rfl

private theorem chart_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (MA : EtaleCompactSupportNormalization A)
    (MB : EtaleCompactSupportNormalization B)
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [HasCompactification g] (i : U ⟶ V) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g = e ≫ affineTraceProjection S d)
    (K : DerivedCategoryModule A U) :
    (scalarExtension φ S).map
        ((OrdinaryChart.leftIso A MA g i d e he
          (HasCompactification.compactification g)).hom.app K) ≫
      (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ i).hom
        (compactScalarMap φ (HasCompactification.compactification g))).app K =
    (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom
        (affineLeftScalar φ S d)).app K ≫
      (OrdinaryChart.leftIso B MB g i d e he
        (HasCompactification.compactification g)).hom.app
          ((scalarExtension φ U).obj K) := by
  have : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
  let cp := HasCompactification.compactification (affineTraceProjection S d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection S d)
  let cf := HasCompactification.compactification g
  have hi := ambient_left_scalar φ MA MB i g cf (cg.copy he) K
  have hj := ambient_left_scalar φ MA MB e (affineTraceProjection S d) cp cg K
  have ha := affine_left_scalar φ S d cp
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj K)
  have hn := (OrdinaryChart.affineLeftIso B S d cp).hom.naturality
    ((ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K)
  simp only [Functor.comp_map] at hn
  dsimp only [cp, cg, cf] at hi hj ha hn ⊢
  apply (cancel_mono ((etaleAmbientLeftComparison B MB i g cf (cg.copy he)).hom.app
    ((scalarExtension φ U).obj K))).mp
  dsimp only [scalarComposite]
  simp only [Category.assoc]
  erw [← hi]
  simp only [OrdinaryChart.leftIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  erw [hj, reassoc_of% ha, ← reassoc_of% hn]

attribute [local irreducible] ProEtale.reductionEtaleChartAdjunction
  ProEtale.reductionEtaleChartLeftIso ProEtale.reductionEtaleChartRightIso

/-- The ordinary exceptional coefficient mate, restricted to one source chart, is
canonical scalar reassociation for the sum-then-ordered-affine right adjunction.
Source: general-ring smooth purity, Proof (2), local adjunctions;
exceptional coefficient change, Charts.
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).

Proof: transpose both sides under the B-coefficient chart adjunction. The definition
of OrdinaryChart.rightIso preserves the counit of the compactified exceptional
adjunction. The defining transpose equation for mateMap therefore expresses the
second path as scalar extension of the A-counit, preceded by the inverse compact
support comparison. For the first path, the graph normalization of MA and MB
identifies the etale part with summation on sheets. Scalar extension commutes with
this sum and its evaluation counit. On each ordered affine coordinate the normalized
P1 counit is the inverse of the two-summand Kummer decomposition followed by its
second projection. The Kummer boundary and the two summand maps commute with
coefficient extension: on roots the map is z tensor a tensor b to z tensor phi(a)b.
Consequently the inverse decomposition and its trace commute as well. Tensoring
this trace with the input, using the canonical tensorator and pullback balancing,
proves the affine counit square. Paste these squares in coordinate order, then
with the etale sum square; naturality moves the intermediate counits past each
comparison. The two transposes are now identical. Injectivity of the chart
adjunction bijection proves the equation. This is entirely on the ordinary etale
site and needs no presentation over a field. Rank-one Tate lines are flat over A,
so no flatness of B over A is used. For dimension zero the affine adjunction is
identity; for zero coefficient rings every object and map is zero. No covering
or isomorphism detection is part of this local assertion. -/
theorem ordinary_chart_exceptional_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S U : Scheme.{u}} [IsNoetherian V] [IsNoetherian S] [IsNoetherian U]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    (i : U ⟶ V) [IsOpenImmersion i] (d : ℕ)
    (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g = e ≫ affineTraceProjection S d)
    (MA : EtaleCompactSupportNormalization A) (MB : EtaleCompactSupportNormalization B)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ U).map
        ((OrdinaryChart.rightIso A MA g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek A g)
          (rightDerivedUpperShriekAdjunction A g)
          N hA tA PA hS).hom.app K) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom =
    (scalarPullbackIso φ i).inv.app
        ((rightDerivedUpperShriek A g).obj K) ≫
      (ordinaryFinitePullback B i).map (ExceptionalCoefficients.mateMap φ g K) ≫
      (OrdinaryChart.rightIso B MB g i d e he
        (HasCompactification.compactification g)
        (rightDerivedUpperShriek B g)
        (rightDerivedUpperShriekAdjunction B g)
        N hB tB PB hS).hom.app ((scalarExtension φ S).obj K) := by
  let aA := ((derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm).comp
        (rightDerivedUpperShriekAdjunction A g)
  let aB := ((derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) i inferInstance).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) i).symm).comp
        (rightDerivedUpperShriekAdjunction B g)
  let hA' := OrdinaryChart.adjunction A S N hA tA PA hS d e
  let hB' := OrdinaryChart.adjunction B S N hB tB PB hS d e
  let lA := OrdinaryChart.leftIso A MA g i d e he
    (HasCompactification.compactification g)
  let lB := OrdinaryChart.leftIso B MB g i d e he
    (HasCompactification.compactification g)
  let β := scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ i).hom
    (compactScalarMap φ (HasCompactification.compactification g))
  let γ := scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom
    (affineLeftScalar φ S d)
  let q := (scalarPullbackIso φ i).inv.app
      ((rightDerivedUpperShriek A g).obj K) ≫
    (ordinaryFinitePullback B i).map (ExceptionalCoefficients.mateMap φ g K)
  let r := (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom
  have hq : β.app (((rightDerivedUpperShriek A g) ⋙
        ordinaryFinitePullback A i).obj K) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} B) i inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map q ≫
      aB.counit.app ((scalarExtension φ S).obj K) =
        (scalarExtension φ S).map (aA.counit.app K) := by
    have h := compose_counit_scalar
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm)
      (rightDerivedUpperShriekAdjunction A g)
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) i inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) i).symm)
      (rightDerivedUpperShriekAdjunction B g)
      (scalarExtension φ U) (scalarExtension φ V) (scalarExtension φ S)
      (ProEtale.CoefficientCompatibility.sumCoefficientIso φ i).hom
      (compactScalarMap φ (HasCompactification.compactification g)) K
      ((scalarPullbackIso φ i).inv.app
        ((rightDerivedUpperShriek A g).obj K))
      (ExceptionalCoefficients.mateMap φ g K)
      (sum_scalar_counit φ i _) (exceptional_scalar_counit φ g K)
    simpa only [β, q, aA, aB, scalarComposite, Functor.comp_map,
      ordinaryFinitePullback, Functor.comp_obj, Category.assoc,
      rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification] using h
  have hb : Epi (β.app (((rightDerivedUpperShriek A g) ⋙
        ordinaryFinitePullback A i).obj K)) := by
    dsimp only [β, scalarComposite]
    have := compactScalarMap_isIso φ (HasCompactification.compactification g)
      ((etaleLowerShriek (ModuleCat.{u + 1} A) i inferInstance).mapDerivedCategory.obj
        (((rightDerivedUpperShriek A g) ⋙
        ordinaryFinitePullback A i).obj K))
    infer_instance
  have hr : β.app ((affineTraceRight A N hA S d ⋙ ordinaryFinitePullback A e).obj K) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} B) i inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map r ≫
      (hB'.ofNatIsoLeft lB).counit.app ((scalarExtension φ S).obj K) =
        (scalarExtension φ S).map ((hA'.ofNatIsoLeft lA).counit.app K) := by
    exact transported_counit_scalar hA' hB' lA lB
      (scalarExtension φ U) (scalarExtension φ S) β γ K r
      (chart_left_scalar φ MA MB g i d e he)
      (chart_scalar_counit φ N hN hA hB S hS tA tB PA PB d e K)
  have h := rightAdjointUniq_scalar_of_counits aA (hA'.ofNatIsoLeft lA)
    aB (hB'.ofNatIsoLeft lB) (scalarExtension φ U) (scalarExtension φ S)
    β K q r hq hb hr
  simpa only [aA, aB, hA', hB', lA, lB, q, r,
    OrdinaryChart.rightIso, Category.assoc] using h

end AlgebraicGeometry.Etale

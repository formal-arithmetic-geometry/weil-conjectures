/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-! # The ordered compactification scalar square over the corrected field domain

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: ordered projective-line integration
(blueprint: lem-sp-ordered-compactification-scalar-square).

The ordered coefficient recursion uses ordinary scalar extension and the canonical
proper/open coefficient map, with the coherent comparison to a specified compactification.
The field may be finite or algebraically closed,
including characteristic zero when it is algebraically closed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open ProEtale.OrdinaryScalarSite ProEtale.FiniteCompactCoefficients

/-- The ordered coefficient arrow for ordinary scalar extension, with identity at zero.
At a successor, apply the preceding coefficient arrow to the last line's output,
then map the standard compactification's proper/open beta through the preceding tower.
Source: latest blueprint, reduction-exceptional proof, Charts
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteAffineCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (S : Scheme.{u}) :
    (d : ℕ) → (M : DerivedCategoryModule A (affineTraceTower S d)) →
      (scalar S.smallEtaleTopology φ).obj ((affineTraceLeft A S d).obj M) ⟶
        (affineTraceLeft B S d).obj
          ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M)
  | 0, M => 𝟙 ((scalar S.smallEtaleTopology φ).obj M)
  | d + 1, M =>
    orderedFiniteAffineCoefficientMap φ S d
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft B S d).map
        ((beta φ (affineTraceLineCompactification (affineTraceTower S d))).app M)

/-- The canonical coherent tower comparison to the specified compactification on D+.
It uses the existing affine composition comparison and canonical pairwise comparison,
transported through the two bounded-below inclusion compatibility isomorphisms.
At zero its tower factor is the inverse identity normalization.
Source: latest blueprint, reduction-exceptional proof, Charts
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteCompactificationComparison
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineTraceLeft R S d).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj :=
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  letI : IsNoetherian S := ⟨⟩
  ((affineTracePlusCompatibility R S d).app M).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      ((affineTraceCompactSupportComparison R S d).app M ≪≫
        (rightDerivedLowerShriekOfCompactificationPlusIso R
          (HasCompactification.compactification (affineTraceProjection S d)) c).app M) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c).app M

/-- The comparison through every auxiliary compactification and common refinement.
The two refinement factors are the actual canonical D+ comparison isomorphisms;
no Cartesian-square or density hypothesis is imposed on their refinement arrows.
Source: latest blueprint, reduction-exceptional proof, Charts, refinement independence
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteCompactificationComparisonVia
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c c' e : Compactification (affineTraceProjection S d))
    (r : e.Refinement c') (s : e.Refinement c)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineTraceLeft R S d).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj :=
  orderedFiniteCompactificationComparison R k S d c' M ≪≫
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} R) c').app M).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).app M) ≪≫
        ((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R s).app M).symm) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c).app M

private theorem ordinaryScalar_plus
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : DerivedCategoryModule A T) (hK : Input A T K) :
    _root_.DerivedCategory.TStructure.t.plus ((scalar T.smallEtaleTopology φ).obj K) := by
  obtain ⟨a, b, hab, hTor⟩ := hK.2
  obtain ⟨P, hf, -, hz, ⟨e⟩⟩ :=
    (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A T a b hab K hK.1).1 hTor
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    fun q hq ↦ hz q (.inl hq)
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    fun q hq ↦ hz q (.inr hq)
  have hk := CochainComplex.kFlat_of_bounded_of_flat P a b hf
  let E := CoefficientScalarRepresentatives.ordinaryExtension T.smallEtaleTopology φ
  let Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj P
  have : Q.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    fun q hq ↦ E.map_isZero (hz q (.inl hq))
  let adj : E.leftDerivedFunctor ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
    CoefficientScalarRepresentatives.scalarDerivedAdjunction T.smallEtaleTopology φ
  let eF : scalar T.smallEtaleTopology φ ≅ E.leftDerivedFunctor :=
    (CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology φ).leftAdjointUniq adj
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hk
  let eQ : (scalar T.smallEtaleTopology φ).obj K ≅ _root_.DerivedCategory.Q.obj Q :=
    eF.app K ≪≫ E.leftDerivedFunctor.mapIso
      (e.symm ≪≫ ((_root_.DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
    asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
    _root_.DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (_root_.DerivedCategory.quotientCompQhIso _).app Q
  have : (_root_.DerivedCategory.Q.obj Q).IsGE a := by infer_instance
  exact ⟨a, _root_.DerivedCategory.TStructure.t.isGE_of_iso eQ.symm a⟩

private noncomputable def ordinaryLeftScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :=
  (@asIso _ _ _ _
    (((mateEquiv
      (CoefficientScalarRepresentatives.adjunction W.smallEtaleTopology φ)
      (CoefficientScalarRepresentatives.adjunction Z.smallEtaleTopology φ)).symm
        (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans)
    (CoefficientScalarRepresentatives.etaleScalarPullbackMate_isIso φ f)).symm

private theorem restrictionIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    upperStarRestrictScalarsIso φ f = upperStarRestrictScalarsIsoSheaf φ f := by
  let a := (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  let b := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
    (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
  apply Iso.ext
  apply (conjugateEquiv b a).injective
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq,
    Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv,
    a, b]
  exact ((conjugateEquiv b a).apply_symm_apply _).symm

private theorem scalarExact_inverse_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (N : DerivedCategoryModule A W) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((etaleIso φ f).inv.app N) =
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).unit.app N) ≫
      (restrictionExactIso φ f).hom.app
        (((scalar W.smallEtaleTopology φ)).obj N) := by
  have hu := unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom) N
  change L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).unit.app N) ≫
        (scalarRestrictionPullbackIso φ f).hom.app (((scalar W.smallEtaleTopology φ)).obj N) =
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        (L(upperStar (ModuleCat.{u + 1} A) f).obj N) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((ordinaryLeftScalarIso φ f).inv.app N) at hu
  have he : scalarRestrictionPullbackIso φ f =
      Functor.isoWhiskerLeft _
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      restrictionExactIso φ f ≪≫ Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _ := by
    unfold restrictionExactIso
    rfl
  rw [he] at hu
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom] at hu
  simpa only [etaleIso, ordinaryLeftScalarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using
    transportReverseUnit ((scalar W.smallEtaleTopology φ)) ((scalar Z.smallEtaleTopology φ))
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
      (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
      _ _ _ _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
      (ordinaryLeftScalarIso φ f).inv
      (restrictionExactIso φ f).hom N hu.symm

private theorem scalarExact_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}} (v : T₁ ⟶ T₂) (j : X ⟶ T₁)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} B) j v)).hom.app
        (((scalar T₂.smallEtaleTopology φ)).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etaleIso φ v).hom.app N) ≫
      (etaleIso φ j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
    (etaleIso φ (j ≫ v)).hom.app N ≫ ((scalar X.smallEtaleTopology φ)).map
      ((Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) j v)).hom.app
        N) := by
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (upperStarRestrictScalarsIso φ v) (upperStarRestrictScalarsIso φ j)
    (upperStarRestrictScalarsIso φ (j ≫ v))
    (upperStarComp (ModuleCat.{u + 1} A) j v)
    (upperStarComp (ModuleCat.{u + 1} B) j v)
    (fun M ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom φ j v) M)
    (((scalar T₂.smallEtaleTopology φ)).obj N)
  have hr := reverseComposition
    (scalar T₂.smallEtaleTopology φ) (scalar T₁.smallEtaleTopology φ)
    (scalar X.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars T₂.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars T₁.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
    (Adjunction.ofIsRightAdjoint _)
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (j ≫ v)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) (j ≫ v)).mapDerivedCategory
    (etaleIso φ v).inv (etaleIso φ j).inv (etaleIso φ (j ≫ v)).inv
    (restrictionExactIso φ v).hom (restrictionExactIso φ j).hom
    (restrictionExactIso φ (j ≫ v)).hom
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) j v))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} B) j v)) N
    (scalarExact_inverse_unit φ v N)
    (scalarExact_inverse_unit φ j
      ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N))
    (scalarExact_inverse_unit φ (j ≫ v) N)
    (by simpa only [restrictionExactIso, ← restrictionIso_eq] using hd)
  apply (cancel_epi ((etaleIso φ (j ≫ v)).inv.app N)).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hr]
  simp only [Functor.comp_obj,
    ← (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app,
    (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map_id,
    Category.id_comp, Category.comp_id]

private theorem ordinaryScalar_identity
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : DerivedCategoryModule A T) :
    let eA := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 T)).symm ≪≫
      leftDerivedUpperStarId (ModuleCat.{u + 1} A) T
    let eB := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (𝟙 T)).symm ≪≫
      leftDerivedUpperStarId (ModuleCat.{u + 1} B) T
    (etaleIso φ (𝟙 T)).hom.app N ≫ (scalar T.smallEtaleTopology φ).map (eA.hom.app N) =
      eB.hom.app ((scalar T.smallEtaleTopology φ).obj N) := by
  dsimp only
  apply identity_of_composition
    (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) (𝟙 T)).mapDerivedCategory
    (scalar T.smallEtaleTopology φ) _ _
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp (𝟙 T)).symm) ≪≫ Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp (𝟙 T)).symm) ≪≫ Functor.mapDerivedCategoryCompIso _ _)
    (etaleIso φ (𝟙 T))
    (exact_identity_unit A T) (exact_identity_unit B T)
  intro X
  exact scalarExact_composition φ (𝟙 T) (𝟙 T) X

private theorem etaleIso_inv_eq_leftMateExact
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleIso φ f).inv =
      (((mateEquiv
        (CoefficientScalarRepresentatives.adjunction Y.smallEtaleTopology φ)
        (CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology φ)).symm
        (TwoSquare.mk _ _ _ _ (restrictionExactIso φ f).hom)).natTrans) := by
  ext K
  apply ((CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology φ).homEquiv
    _ _).injective
  simp only [Adjunction.homEquiv_unit]
  change (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app _ ≫ _ = _
  rw [scalarExact_inverse_unit]
  exact unit_mateEquiv_symm _ _ _ _

private theorem ordinaryOpen_inv_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    ((mateEquiv
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).symm
        (TwoSquare.mk _ _ _ _ (etaleIso φ j).inv)).natTrans = (etOpen φ j).inv := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := CoefficientScalarRepresentatives.adjunction V.smallEtaleTopology φ
  let v := CoefficientScalarRepresentatives.adjunction U.smallEtaleTopology φ
  let α := (mateEquiv x v).symm (TwoSquare.mk _ _ _ _ (restrictionExactIso φ j).hom)
  have he : α.natTrans = (etaleIso φ j).inv :=
    (etaleIso_inv_eq_leftMateExact φ j).symm
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b v x
      (TwoSquare.mk _ _ _ _ (restrictionExactIso φ j).hom))
  change ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ (etaleIso φ j).inv)).natTrans = _
  rw [← he]
  rw [h]
  ext K
  change ((conjugateEquiv (a.comp x) (v.comp b)).symm
    (restrictionExactIso φ j).hom).app K = _
  simp only [etOpen, Adjunction.leftAdjointUniq, Iso.symm_inv,
    conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    NatTrans.id_app, Category.assoc,
    Functor.map_comp, a, b, x, v, restrictionExactIso,
    derivedOpenImmersionLowerShriekUpperStarAdjunction]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]

private theorem ordinaryOpen_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
        ((scalar U.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etOpen φ j).inv.app M) =
    (scalar U.smallEtaleTopology φ).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app M) ≫
      (etaleIso φ j).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) := by
  have h := unit_mateEquiv_symm
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (TwoSquare.mk _ _ _ _ (etaleIso φ j).inv) M
  change (scalar U.smallEtaleTopology φ).map _ ≫ (etaleIso φ j).inv.app _ =
    _ ≫ (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      ((((mateEquiv
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).symm
          (TwoSquare.mk _ _ _ _ (etaleIso φ j).inv)).natTrans.app M)) at h
  rw [ordinaryOpen_inv_mate] at h
  exact h.symm

private theorem ordinaryOpen_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategoryModule A V) :
    (etOpen φ j).hom.app ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etaleIso φ j).inv.app K) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).counit.app ((scalar V.smallEtaleTopology φ).obj K) =
    (scalar V.smallEtaleTopology φ).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).counit.app K) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := CoefficientScalarRepresentatives.adjunction V.smallEtaleTopology φ
  let v := CoefficientScalarRepresentatives.adjunction U.smallEtaleTopology φ
  let α := (mateEquiv x v).symm (TwoSquare.mk _ _ _ _ (restrictionExactIso φ j).hom)
  have he : α.natTrans = (etaleIso φ j).inv :=
    (etaleIso_inv_eq_leftMateExact φ j).symm
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b v x
      (TwoSquare.mk _ _ _ _ (restrictionExactIso φ j).hom))
  have h' : ((mateEquiv a b).symm α).natTrans = (etOpen φ j).inv := by
    change ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α.natTrans)).natTrans = _
    rw [he]
    exact ordinaryOpen_inv_mate φ j
  have hc := mateEquiv_counit_symm a b α K
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalar V.smallEtaleTopology φ).obj K) =
    ((mateEquiv a b).symm α).natTrans.app _ ≫
      (scalar V.smallEtaleTopology φ).map (a.counit.app K) at hc
  rw [he, h'] at hc
  have hh := congrArg (fun z ↦ (etOpen φ j).hom.app
    ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫ z) hc
  simpa only [a, b, Category.assoc, Iso.hom_inv_id_app_assoc] using hh

private theorem ordinaryOpen_identity_counit
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K : DerivedCategoryModule A S) :
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).inv.app
        ((upperStar (ModuleCat.{u + 1} A) (𝟙 S)).mapDerivedCategory.obj K) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (𝟙 S)).counit.app K =
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) S) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app K := by
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 S)
  let l := openImmersionLowerShriekId (ModuleCat.{u + 1} A) S
  let r := upperStarId (ModuleCat.{u + 1} A) S
  have hs (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      l.inv.app ((upperStar (ModuleCat.{u + 1} A) (𝟙 S)).obj M) ≫
        a.counit.app M = r.hom.app M := by
    have hh := a.leftAdjointUniq_hom_app_counit (Adjunction.id.ofNatIsoRight r.symm) M
    change l.hom.app _ ≫ r.hom.app M = a.counit.app M at hh
    rw [← hh, Iso.inv_hom_id_app_assoc]
  exact a.mapDerivedCategoryAdjunction_counit_app_of_iso l r hs K

private theorem ordinaryOpen_identity
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    (etOpen φ (𝟙 S)).hom.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S).hom.app
        ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K) := by
  let rA := Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) S) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let rB := Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} B) S) ≪≫
    Functor.mapDerivedCategoryIdIso _
  apply identity_left_scalar
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 S))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (𝟙 S))
    (scalar S.smallEtaleTopology φ)
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) rA
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) rB
    (etOpen φ (𝟙 S)).hom (etaleIso φ (𝟙 S)).inv
    (ordinaryOpen_identity_counit A S) (ordinaryOpen_identity_counit B S)
    (ordinaryOpen_scalar_counit φ (𝟙 S))
  intro X
  have h := ordinaryScalar_identity φ S X
  have hr (R : Type (u + 1)) [CommRing R] :
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) (𝟙 S)).symm ≪≫
        leftDerivedUpperStarId (ModuleCat.{u + 1} R) S =
      Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} R) S) ≪≫
        Functor.mapDerivedCategoryIdIso _ := by
    ext N
    simp [leftDerivedUpperStarId, leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.leftDerivedFunctorNatIso]
  dsimp only at h
  rw [hr A, hr B] at h
  rw [← h, Iso.inv_hom_id_app_assoc]

private theorem ordinaryDirect_identity
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (M : DerivedCategoryModule A T) :
    (etaleGamma φ (𝟙 T)).app M ≫
        (rightDerivedLowerStarIdIso B T).hom.app ((scalar T.smallEtaleTopology φ).obj M) =
      (scalar T.smallEtaleTopology φ).map ((rightDerivedLowerStarIdIso A T).hom.app M) := by
  let Q := scalar T.smallEtaleTopology φ
  let U := R(lowerStar (ModuleCat.{u + 1} A) (𝟙 T)).obj M
  let iA := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 T)).symm ≪≫
    leftDerivedUpperStarId (ModuleCat.{u + 1} A) T
  let iB := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (𝟙 T)).symm ≪≫
    leftDerivedUpperStarId (ModuleCat.{u + 1} B) T
  have hc (R : Type (u + 1)) [CommRing R] [Finite R]
      (N : DerivedCategoryModule R T) :
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) (𝟙 T)).symm ≪≫
        leftDerivedUpperStarId (ModuleCat.{u + 1} R) T).inv.app
          (R(lowerStar (ModuleCat.{u + 1} R) (𝟙 T)).obj N) ≫
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (𝟙 T)).counit.app N =
      (rightDerivedLowerStarIdIso R T).hom.app N := by
    rw [mapDerivedUpperStarLowerStarAdjunction_eq]
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Adjunction.ofNatIsoLeft_counit, Functor.whiskerLeft_app, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    rw [identity_counit, derived_identity_comparison]
    rfl
  have hl : iB.inv.app (Q.obj U) ≫ (etaleIso φ (𝟙 T)).hom.app U =
      Q.map (iA.inv.app U) := by
    apply (cancel_mono (Q.map (iA.hom.app U))).1
    rw [Category.assoc, ordinaryScalar_identity φ T U]
    simp only [Q, iB, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj]
    exact (scalar T.smallEtaleTopology φ).map_id _ |>.symm
  rw [← hc B (Q.obj M)]
  have hn := iB.inv.naturality ((etaleGamma φ (𝟙 T)).app M)
  dsimp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hm := mateEquiv_counit
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T))
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (𝟙 T))
    (TwoSquare.mk _ _ _ _ (etaleIso φ (𝟙 T)).hom) M
  change (upperStar (ModuleCat.{u + 1} B) (𝟙 T)).mapDerivedCategory.map
    ((etaleGamma φ (𝟙 T)).app M) ≫ _ = _ at hm
  rw [hm, ← Category.assoc, hl, ← Q.map_comp, hc]

private theorem ordinaryIdentityCompact_scalar
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    let eA := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    let eB := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso B S
    (beta φ (Compactification.ofIsProper (𝟙 S))).app K ≫
        eB.hom.app ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map (eA.hom.app K) := by
  dsimp only
  have hn := (etaleGamma φ (𝟙 S)).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have ho := congrArg
    (fun z ↦ ((lowerStar (ModuleCat.{u + 1} B) (𝟙 S)).rightDerivedFunctor).map z)
    (ordinaryOpen_identity φ S K)
  simp only [Functor.map_comp] at ho
  simp only [beta, Compactification.ofIsProper, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% ho, ← reassoc_of% hn]
  change (scalar S.smallEtaleTopology φ).map
      (((lowerStar (ModuleCat.{u + 1} A) (𝟙 S)).rightDerivedFunctor).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
        (etaleGamma φ (𝟙 S)).app K ≫ 𝟙 _ ≫
          (rightDerivedLowerStarIdIso B S).hom.app ((scalar S.smallEtaleTopology φ).obj K) =
    (scalar S.smallEtaleTopology φ).map
      (((lowerStar (ModuleCat.{u + 1} A) (𝟙 S)).rightDerivedFunctor).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
          (scalar S.smallEtaleTopology φ).map (𝟙 _) ≫
          (scalar S.smallEtaleTopology φ).map ((rightDerivedLowerStarIdIso A S).hom.app K)
  simp only [Category.id_comp]
  rw [ordinaryDirect_identity]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]

private theorem ordinaryDirect_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X) :
    (scalar Z.smallEtaleTopology φ).map
        ((Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
          (lowerStarComp (ModuleCat.{u + 1} A) r s)).hom.app M) ≫
      (etaleGamma φ (r ≫ s)).app M =
    (etaleGamma φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
      R(lowerStar (ModuleCat.{u + 1} B) s).map ((etaleGamma φ r).app M) ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
        (lowerStarComp (ModuleCat.{u + 1} B) r s)).hom.app
          ((scalar X.smallEtaleTopology φ).obj M) := by
  let a := ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r))
  let b := ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r))
  let ac := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r ≫ s)
  let bc := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (r ≫ s)
  let cA := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} A) r s) ≪≫ Functor.mapDerivedCategoryCompIso _ _
  let cB := Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) r s) ≪≫ Functor.mapDerivedCategoryCompIso _ _
  let kA := Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
    (lowerStarComp (ModuleCat.{u + 1} A) r s)
  let kB := Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
    (lowerStarComp (ModuleCat.{u + 1} B) r s)
  let l := fun {W T : Scheme.{u}} (f : W ⟶ T) ↦ (etaleIso φ f).hom
  let L : scalar Z.smallEtaleTopology φ ⋙
      ((upperStar (ModuleCat.{u + 1} B) s).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} B) r).mapDerivedCategory) ⟶
      ((upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory) ⋙ scalar X.smallEtaleTopology φ :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (l s) _ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (l r) ≫ (Functor.associator _ _ _).inv
  have hm : (upperStar (ModuleCat.{u + 1} B) (r ≫ s)).mapDerivedCategory.map
        ((etaleGamma φ (r ≫ s)).app M) ≫ bc.counit.app _ =
      (l (r ≫ s)).app _ ≫ (scalar X.smallEtaleTopology φ).map (ac.counit.app M) := by
    exact mateEquiv_counit ac bc (TwoSquare.mk _ _ _ _ (etaleIso φ (r ≫ s)).hom) M
  have hl : cB.hom.app ((scalar Z.smallEtaleTopology φ).obj
      (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) ≫
      L.app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) =
      (l (r ≫ s)).app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)) ≫
        (scalar X.smallEtaleTopology φ).map (cA.hom.app (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))) := by
    simpa only [L, l, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      scalarExact_composition φ s r (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M))
  have h := composite_mate_calculation a ac b bc cA cB kA kB
    (scalar Z.smallEtaleTopology φ) (scalar X.smallEtaleTopology φ) (l (r ≫ s)) L M
    ((etaleGamma φ (r ≫ s)).app M)
    (compositor_counit A r s M)
    (compositor_counit B r s ((scalar X.smallEtaleTopology φ).obj M)) hm hl
  have hh := congrArg (fun z ↦ z.natTrans.app M)
    (mateEquiv_hcomp
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
      (TwoSquare.mk _ _ _ _ (etaleIso φ s).hom)
      (TwoSquare.mk _ _ _ _ (etaleIso φ r).hom))
  have hi : (b.homEquiv _ _).symm
      ((etaleGamma φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) s).map ((etaleGamma φ r).app M)) =
      L.app _ ≫ (scalar X.smallEtaleTopology φ).map (a.counit.app M) := by
    have hh' : ((mateEquiv a b) (TwoSquare.mk _ _ _ _ L)).natTrans.app M =
        (etaleGamma φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
          R(lowerStar (ModuleCat.{u + 1} B) s).map ((etaleGamma φ r).app M) := by
      simpa only [a, b, L, l, etaleGamma, TwoSquare.vComp, TwoSquare.hComp,
        NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id] using hh
    rw [← hh']
    exact mateEquiv_counit a b (TwoSquare.mk _ _ _ _ L) M
  have he := (b.homEquiv _ _).symm.injective (h.trans hi.symm)
  change (scalar Z.smallEtaleTopology φ).map (kA.hom.app M) ≫
    (etaleGamma φ (r ≫ s)).app M = _ ≫ _ ≫ kB.hom.app _
  apply (cancel_mono (kB.inv.app ((scalar X.smallEtaleTopology φ).obj M))).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using he

private def refinementRestriction
    (A : Type (u + 1)) [CommRing A]
    {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂) :
    (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory :=
  let k := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  { app M := k.hom.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).counit.app M)
    naturality {M N} f := by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [reassoc_of% k.hom.naturality
        (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).map f)]
      rw [← Functor.map_comp, Adjunction.counit_naturality, Functor.map_comp]
      exact (Category.assoc _ _ _).symm }

private theorem coefficientPullback_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).hom.app ((scalar T₂.smallEtaleTopology φ).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((etaleIso φ v).hom.app N) ≫
      (etaleIso φ j₁).hom.app ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
    (etaleIso φ j₂).hom.app N ≫ (scalar X.smallEtaleTopology φ).map
      ((Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app N) := by
  subst j₂
  exact scalarExact_composition φ v j₁ N

private theorem coefficientMate_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
        ((etaleGamma φ f).app M) ≫
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
        ((scalar X.smallEtaleTopology φ).obj M) =
    (etaleIso φ f).hom.app (((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor).obj M) ≫
      (scalar X.smallEtaleTopology φ).map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app M) :=
  mateEquiv_counit
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (etaleIso φ f).hom) M

private theorem ordinaryDirect_composition_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (t : X ⟶ Z) (h : r ≫ s = t) (M : DerivedCategoryModule A X) :
    (scalar Z.smallEtaleTopology φ).map
        ((Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
          (lowerStarComp (ModuleCat.{u + 1} A) r s t h.symm)).hom.app M) ≫
      (etaleGamma φ t).app M =
    (etaleGamma φ s).app (((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).obj M) ≫
      ((lowerStar (ModuleCat.{u + 1} B) s).rightDerivedFunctor).map ((etaleGamma φ r).app M) ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
        (lowerStarComp (ModuleCat.{u + 1} B) r s t h.symm)).hom.app
          ((scalar X.smallEtaleTopology φ).obj M) := by
  subst t
  exact ordinaryDirect_composition φ r s M

private theorem refinement_normalization_unbounded
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategoryModule A X) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) d.i).homEquiv _ _
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj K) ≫
      ((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app K)) ≫
      (refinementRestriction A r.hom c.i d.i r.i_hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) c.i).unit.app K := by
  have h := refinement_transpose_normalization
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) r.hom).mapDerivedCategory
    ((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarCompIso (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom))
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp)
    (unit_map_refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp) K
  simpa only [refinementRestriction, upperStarCompIso_eq,
    Functor.mapDerivedCategoryTriangleIso, mapDerivedUpperStarLowerStarAdjunction_eq,
    rightDerivedLowerStar] using h

private theorem refinement_open_scalar_unbounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategoryModule A X) :
    let αA := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj K) ≫
        ((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app K)
    let αB := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
        ((scalar X.smallEtaleTopology φ).obj K)) ≫
        ((lowerStar (ModuleCat.{u + 1} B) r.hom).rightDerivedFunctor).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
            ((scalar X.smallEtaleTopology φ).obj K))
    (scalar d.Z.smallEtaleTopology φ).map αA ≫
      (etaleGamma φ r.hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
      ((lowerStar (ModuleCat.{u + 1} B) r.hom).rightDerivedFunctor).map
        ((etOpen φ c.i).app K).hom =
      ((etOpen φ d.i).app K).hom ≫ αB := by
  dsimp only
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let kA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let kB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) c.i r.hom d.i r.i_hom.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have hχ : ∀ M : DerivedCategoryModule A c.Z,
      (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.map
          ((etaleGamma φ r.hom).app M) ≫
        (refinementRestriction B r.hom c.i d.i r.i_hom).app
          ((scalar c.Z.smallEtaleTopology φ).obj M) ≫
        (etaleIso φ c.i).hom.app M =
      (etaleIso φ d.i).hom.app
          (((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor).obj M) ≫
        (scalar X.smallEtaleTopology φ).map
          ((refinementRestriction A r.hom c.i d.i r.i_hom).app M) := by
    intro M
    simpa only [refinementRestriction, kA, kB, rightDerivedLowerStar,
      Functor.map_comp, Category.assoc] using
      restriction_coefficient_mate
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom)
        (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
        (scalar X.smallEtaleTopology φ) (scalar c.Z.smallEtaleTopology φ)
        (scalar d.Z.smallEtaleTopology φ)
        kA kB (etaleIso φ c.i)
        (etaleIso φ d.i) (etaleIso φ r.hom)
        (etaleGamma φ r.hom) (coefficientMate_counit φ r.hom)
        (coefficientPullback_comp φ r.hom c.i d.i r.i_hom) M
  have hA := refinement_normalization_unbounded A r hp K
  have hB := refinement_normalization_unbounded B r hp ((scalar X.smallEtaleTopology φ).obj K)
  have hα : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B)
      r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
        ((scalar X.smallEtaleTopology φ).obj K))) :=
    isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
      r B hp ((scalar X.smallEtaleTopology φ).obj K)
  have ht : IsIso ((refinementRestriction B r.hom c.i d.i r.i_hom).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
        ((scalar X.smallEtaleTopology φ).obj K))) := by
    have hi : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) d.i).homEquiv ((scalar X.smallEtaleTopology φ).obj K) _
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
            ((scalar X.smallEtaleTopology φ).obj K)) ≫
          ((lowerStar (ModuleCat.{u + 1} B) r.hom).rightDerivedFunctor).map
            ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
              ((scalar X.smallEtaleTopology φ).obj K)))) := by
      simp only [Adjunction.homEquiv_unit]
      infer_instance
    exact IsIso.of_isIso_fac_left hB
  exact coefficient_refinement_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) d.i)
    ((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) r.hom).rightDerivedFunctor)
    (scalar X.smallEtaleTopology φ) (scalar c.Z.smallEtaleTopology φ)
        (scalar d.Z.smallEtaleTopology φ)
    (refinementRestriction A r.hom c.i d.i r.i_hom)
    (refinementRestriction B r.hom c.i d.i r.i_hom)
    (etaleIso φ c.i) (etaleIso φ d.i)
    (etaleGamma φ r.hom) hχ K _ _
    ((etOpen φ c.i).app K) ((etOpen φ d.i).app K)
    (ordinaryOpen_unit φ c.i K) (ordinaryOpen_unit φ d.i K) hA hB

/-- Unbounded scalar compatibility of compactification refinement.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-refinement-scalar).

Proof: Express the refinement comparison as inverse proper/open exchange followed by the proper
counit. This identification holds on arbitrary complexes by the published derived normalization
and the open unit equation.
Compute scalar compatibility after restriction to the source open, using the coefficient
base-change cube, the open-unit identities and the counit mate equation. Cancel the invertible
base-change components and transpose back.
Paste this normalized open comparison with the proper scalar mate and apply naturality; the two
compact-support refinement paths agree. No boundedness hypothesis occurs in these computations. -/
private theorem ordinaryRefinementScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategoryModule A X) :
    (scalar Y.smallEtaleTopology φ).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
          r hp).app M) ≫ (beta φ c).app M =
      (beta φ d).app M ≫
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} B)
          r hp).app ((scalar X.smallEtaleTopology φ).obj M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let αA := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj M) ≫
      ((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M)
  let αB := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
      ((scalar X.smallEtaleTopology φ).obj M)) ≫
      ((lowerStar (ModuleCat.{u + 1} B) r.hom).rightDerivedFunctor).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
          ((scalar X.smallEtaleTopology φ).obj M))
  let kA := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} A) r)
  let kB := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r.hom)
    (lowerStar (ModuleCat.{u + 1} B) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} B) r)
  have heA : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) r hp).app M =
      ((lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor).map αA ≫
        kA.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have heB : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} B) r hp).app ((scalar X.smallEtaleTopology φ).obj M) =
      ((lowerStar (ModuleCat.{u + 1} B) d.g).rightDerivedFunctor).map αB ≫
        kB.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalar X.smallEtaleTopology φ).obj M)) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have ho := refinement_open_scalar_unbounded φ r hp M
  have hc (N : DerivedCategoryModule A c.Z) :
      (scalar Y.smallEtaleTopology φ).map (kA.hom.app N) ≫ (etaleGamma φ c.g).app N =
        (etaleGamma φ d.g).app
          (((lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctor).obj N) ≫
          ((lowerStar (ModuleCat.{u + 1} B) d.g).rightDerivedFunctor).map
            ((etaleGamma φ r.hom).app N) ≫
          kB.hom.app ((scalar c.Z.smallEtaleTopology φ).obj N) := by
    dsimp only [kA, kB]
    rw [refinementLowerStarComp_eq, refinementLowerStarComp_eq]
    exact ordinaryDirect_composition_eq φ r.hom d.g c.g r.hom_g N
  rw [heA, heB]
  dsimp only [beta,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hn := (etaleGamma φ d.g).naturality αA
  dsimp only [Functor.comp_map, rightDerivedLowerStar] at hn
  erw [reassoc_of% hn]
  have hk := kB.hom.naturality ((etOpen φ c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  erw [← hk]
  simpa only [αA, αB, Functor.map_comp, Category.assoc, Iso.app_hom,
    Functor.comp_obj, Functor.id_obj] using
    congrArg (fun z ↦ (etaleGamma φ d.g).app _ ≫
    ((lowerStar (ModuleCat.{u + 1} B) d.g).rightDerivedFunctor).map z ≫
      kB.hom.app _) ho

private theorem ordinaryCompactificationScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalar Y.smallEtaleTopology φ).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) ≫
      (beta φ d).app M =
      (beta φ c).app M ≫
        (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
          ((scalar X.smallEtaleTopology φ).obj M) := by
  have h₁ := ordinaryRefinementScalar φ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) M
  have h₂ := ordinaryRefinementScalar φ (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) M
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, asIso_hom]
  apply (cancel_mono ((rightDerivedLowerShriekOfCompactificationComparison
    (ModuleCat.{u + 1} B) (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)).app
        ((scalar X.smallEtaleTopology φ).obj M))).1
  simp only [Category.assoc, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact h₁

private theorem ordinary_conj_uniq_transport
    {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : M ⊣ S) (e : S ≅ R) :
    conjugateIsoEquiv b a (a.leftAdjointUniq (b.ofNatIsoRight e)) = e := by
  apply Iso.ext
  ext X
  simp only [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    Adjunction.unit_leftAdjointUniq_hom_app_assoc, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← e.hom.naturality, ← Category.assoc, b.right_triangle_components, Category.id_comp]

private theorem leftUniq_transport_move
    {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} {R S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (e : R ≅ S) :
    (a.ofNatIsoRight e).leftAdjointUniq b =
      a.leftAdjointUniq (b.ofNatIsoRight e.symm) := by
  apply Iso.ext
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem scalar_composition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.hom.app K) ≫
        ((i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)).hom.app (H.obj K) ≫
        Q.map (((h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)).hom.app K) ≫
        κ.inv.app (La.obj K) =
      ((j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)).hom.app K := by
  let t01 := (h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)
  let t12 := (i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)
  let t02 := (j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by rw [conjugateIsoEquiv_iso_symm, ordinary_conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, ordinary_conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, ordinary_conj_uniq_transport]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  exact paste_cancel (Lc.mapIso (μ.app K)) _ _ (κ.app (La.obj K)) _ he'

private theorem ordinaryOpen_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (M : DerivedCategoryModule A V) :
    (scalar X.smallEtaleTopology φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).hom.app M) ≫
      (etOpen φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etOpen φ k).hom.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} B) k j).inv.app ((scalar V.smallEtaleTopology φ).obj M) =
    (etOpen φ (k ≫ j)).hom.app M := by
  let β := Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) k j)
  let γ := Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} B) k j)
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (upperStarRestrictScalarsIso φ j) (upperStarRestrictScalarsIso φ k)
    (upperStarRestrictScalarsIso φ (k ≫ j))
    (upperStarComp (ModuleCat.{u + 1} A) k j)
    (upperStarComp (ModuleCat.{u + 1} B) k j)
    (fun N ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom φ k j) N)
  have hr : (restrictionExactIso φ (k ≫ j)).symm =
      Functor.isoWhiskerRight γ (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (restrictionExactIso φ k).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictionExactIso φ j).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ β.symm := by
    apply Iso.ext
    ext N
    have h := hd N
    rw [restrictionIso_eq, restrictionIso_eq, restrictionIso_eq] at h
    apply (cancel_epi ((restrictionExactIso φ (k ≫ j)).hom.app N)).1
    simp only [Iso.symm_hom, Iso.hom_inv_id_app]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    simp only [restrictionExactIso, β, γ]
    rw [reassoc_of% h]
    simp only [Category.assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp, Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  simpa only [etOpen, derivedOpenImmersionLowerShriekUpperStarAdjunction,
    restrictionExactIso, leftUniq_transport_move] using scalar_composition
    (CoefficientScalarRepresentatives.adjunction V.smallEtaleTopology φ)
    (CoefficientScalarRepresentatives.adjunction U.smallEtaleTopology φ)
    (CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology φ)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ j))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (k ≫ j))
    (restrictionExactIso φ k).symm (restrictionExactIso φ j).symm
    (restrictionExactIso φ (k ≫ j)).symm β γ.symm
    (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) k j)
    (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} B) k j)
    (Iso.ext (derived_open_comp_conjugate (ModuleCat.{u + 1} A) k j))
    (Iso.ext (derived_open_comp_conjugate (ModuleCat.{u + 1} B) k j)) hr M

private theorem coefficientPullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq h f' f g) (N : DerivedCategoryModule A Y) :
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
        ((scalar Y.smallEtaleTopology φ).obj N) ≫
      D(upperStar (ModuleCat.{u + 1} B) h).map
        ((etaleIso φ f).hom.app N) ≫
      (etaleIso φ h).hom.app
        (D(upperStar (ModuleCat.{u + 1} A) f).obj N) =
    D(upperStar (ModuleCat.{u + 1} B) f').map
        ((etaleIso φ g).hom.app N) ≫
      (etaleIso φ f').hom.app
        (D(upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (scalar X'.smallEtaleTopology φ).map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app N) := by
  have hh := coefficientPullback_comp φ f h (h ≫ f) rfl N
  have hg := coefficientPullback_comp φ g f' (h ≫ f) sq.w.symm N
  let ch (R : Type (u + 1)) [CommRing R] :=
    Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} R) h f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let cg (R : Type (u + 1)) [CommRing R] :=
    Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} R) f' g (h ≫ f) sq.w) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  have hs (R : Type (u + 1)) [CommRing R] :
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} R) sq).hom =
        (cg R).inv ≫ (ch R).hom := by
    simp only [exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom, cg, ch, Iso.trans_inv, Category.assoc]
  apply (cancel_epi ((cg B).hom.app ((scalar Y.smallEtaleTopology φ).obj N))).mp
  simp only [hs, NatTrans.comp_app, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]
  simp only [Category.assoc]
  rw [hh, reassoc_of% hg]
  simp only [cg, ch, ← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

private theorem ordinaryBaseChange_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq h f' f g) (M : DerivedCategoryModule A X) :
    D(upperStar (ModuleCat.{u + 1} B) g).map ((etaleGamma φ f).app M) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app
          ((scalar X.smallEtaleTopology φ).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) f').map
          ((etaleIso φ h).hom.app M) =
      (etaleIso φ g).hom.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (scalar Y'.smallEtaleTopology φ).map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M) ≫
        (etaleGamma φ f').app (D(upperStar (ModuleCat.{u + 1} A) h).obj M) := by
  let PA {S T : Scheme.{u}} (v : S ⟶ T) := D(upperStar (ModuleCat.{u + 1} A) v)
  let PB {S T : Scheme.{u}} (v : S ⟶ T) := D(upperStar (ModuleCat.{u + 1} B) v)
  let QA (T : Scheme.{u}) := scalar T.smallEtaleTopology φ
  let afA := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let afB := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let afA' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f'
  let afB' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f'
  let θA := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq
  let θB := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq
  let lp {S T : Scheme.{u}} (v : S ⟶ T) := (etaleIso φ v).hom
  let eA := exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq
  let eB := exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq
  have heA : (PA f').map (eA.app M) ≫ afA'.counit.app ((PA h).obj M) =
      θA.hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (PA h).map (afA.counit.app M) :=
    mateEquiv_counit afA afA' (TwoSquare.mk _ _ _ _ θA.hom) M
  have heB : (PB f').map (eB.app ((QA X).obj M)) ≫
      afB'.counit.app ((PB h).obj ((QA X).obj M)) =
      θB.hom.app (R(lowerStar (ModuleCat.{u + 1} B) f).obj ((QA X).obj M)) ≫
        (PB h).map (afB.counit.app ((QA X).obj M)) :=
    mateEquiv_counit afB afB' (TwoSquare.mk _ _ _ _ θB.hom) ((QA X).obj M)
  have hf := coefficientMate_counit φ f M
  have hf' := coefficientMate_counit φ f' ((PA h).obj M)
  have nc := afB'.counit.naturality ((lp h).app M)
  have ns := θB.hom.naturality ((etaleGamma φ f).app M)
  have nh := (lp h).naturality (afA.counit.app M)
  have nf' := (lp f').naturality (eA.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at nc ns nh nf'
  apply (afB'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change (PB f').map ((PB g).map ((etaleGamma φ f).app M)) ≫
      (PB f').map (eB.app ((QA X).obj M)) ≫
      (PB f').map (R(lowerStar (ModuleCat.{u + 1} B) f').map ((lp h).app M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M)) =
    (PB f').map ((lp g).app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (PB f').map ((QA Y').map (eA.app M)) ≫
      (PB f').map ((etaleGamma φ f').app ((PA h).obj M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M))
  rw [nc, reassoc_of% heB, reassoc_of% ns]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp]
  simp only [Category.assoc]
  rw [nh, hf', reassoc_of% nf']
  rw [← Functor.map_comp, heA, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ (QA X').map ((PA h).map (afA.counit.app M)))
      (coefficientPullback_square φ h f' f g sq
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj M))

private theorem ordinaryProperOpen_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i
    let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k
    let ex := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E)
    a.homEquiv _ _
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq.flip).app E) ≫
      ex = ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).map
        (b.unit.app E) ∧ IsIso ex := by
  dsimp only
  obtain ⟨θ, Γ, hθ, hΓ, hcart, _⟩ := unboundedProperOpenInterchange A
  obtain ⟨lam, hlam, hcartΓ⟩ := hcart k r p i sq
  have hx : (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) =
      lam.hom.app E ≫ ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) k).unit.app E) := by
    rw [hlam]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  constructor
  · have h := unboundedEtaleCompactSupport_tower_adjunct A sq E
    simp only [unboundedEtaleProperOpenRestriction] at h
    have h' := congrArg (fun z ↦ z ≫ ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) k).unit.app E)) h
    simp only [rightDerivedLowerStar, Category.assoc, ← Functor.map_comp, asIso_inv,
      NatIso.isIso_inv_app, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] at h'
    erw [Category.comp_id] at h'
    exact h'
  · rw [hx]
    infer_instance

private theorem ordinaryProperOpen_scalar
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    (scalar Z.smallEtaleTopology φ).map
        ((openImmersionLowerShriekLowerStarExchange
          (ModuleCat.{u + 1} A) sq.flip).app E) ≫
      (etaleGamma φ p).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) ≫
      ((lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor).map
        ((etOpen φ k).hom.app E) =
    (etOpen φ i).hom.app (((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).obj E) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) i).mapDerivedCategory.map
        ((etaleGamma φ r).app E) ≫
      (openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} B) sq.flip).app ((scalar U.smallEtaleTopology φ).obj E) := by
  let := (ordinaryProperOpen_normalization B sq ((scalar U.smallEtaleTopology φ).obj E)).2
  have hex (M : DerivedCategoryModule A V) :
      (etaleIso φ i).inv.app (((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor).obj M) ≫
        (upperStar (ModuleCat.{u + 1} B) i).mapDerivedCategory.map ((etaleGamma φ p).app M) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app
          ((scalar V.smallEtaleTopology φ).obj M) =
      (scalar W.smallEtaleTopology φ).map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) ≫
        (etaleGamma φ r).app
          ((upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj M) ≫
        ((lowerStar (ModuleCat.{u + 1} B) r).rightDerivedFunctor).map
          ((etaleIso φ k).inv.app M) := by
    have h := congrArg (fun z ↦ (etaleIso φ i).inv.app
      (((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor).obj M) ≫ z ≫
      ((lowerStar (ModuleCat.{u + 1} B) r).rightDerivedFunctor).map ((etaleIso φ k).inv.app M))
      (ordinaryBaseChange_scalar φ k r p i sq.toCommSq M)
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  exact coefficient_interchange_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) i)
    ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) r).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor)
    (scalar U.smallEtaleTopology φ) (scalar V.smallEtaleTopology φ)
    (scalar W.smallEtaleTopology φ) (scalar Z.smallEtaleTopology φ)
    (etaleIso φ k).inv (etaleIso φ i).inv (etaleGamma φ r) (etaleGamma φ p)
    (etOpen φ k) (etOpen φ i)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
    hex (ordinaryOpen_unit φ i) (ordinaryOpen_unit φ k) E _ _
    (ordinaryProperOpen_normalization A sq E).1
    (ordinaryProperOpen_normalization B sq ((scalar U.smallEtaleTopology φ).obj E)).1

private theorem scalarOpen_composition_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (j : Y ⟶ Z) (t : X ⟶ Z) (h : k ≫ j = t)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion t]
    (M : DerivedCategoryModule A X) :
    (scalar Z.smallEtaleTopology φ).map
        (((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} A) h).hom.app M) ≫
      (etOpen φ t).hom.app M =
    (etOpen φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etOpen φ k).hom.app M) ≫
      (((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} B) k j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} B) h).hom.app ((scalar X.smallEtaleTopology φ).obj M)) := by
  subst t
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.trans_hom,
    Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  apply (cancel_epi ((scalar Z.smallEtaleTopology φ).map
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) k j).hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ordinaryOpen_composition φ k j M).symm

private theorem ordinaryCompactTowerScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d : Compactification g)
    (e : Compactification (f ≫ d.i)) (M : DerivedCategoryModule A X) :
    (scalar Z.smallEtaleTopology φ).map
        ((rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app M) ≫
      (beta φ (d.comp e)).app M =
    (beta φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          e.restrict).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
        ((beta φ e.restrict).app M) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B d e).hom.app
        ((scalar X.smallEtaleTopology φ).obj M) := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  have : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
  have : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
  have : IsNoetherian e.Z := ⟨⟩
  have : IsLocallyNoetherian e.restrict.Z :=
    LocallyOfFiniteType.isLocallyNoetherian e.restrict.g
  have : CompactSpace e.restrict.Z := QuasiCompact.compactSpace_of_compactSpace e.restrict.g
  have : IsNoetherian e.restrict.Z := ⟨⟩
  have hi := ordinaryProperOpen_scalar φ e.isPullback_restrict.flip
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      e.restrict.i).mapDerivedCategory.obj M)
  have ho := scalarOpen_composition_eq φ e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst M
  have hp := ordinaryDirect_composition_eq φ e.g d.g (e.g ≫ d.g) rfl
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
          e.restrict.i).mapDerivedCategory.obj M))
  rw [right_derived_star_comp_eq, right_derived_star_comp_eq] at hp
  let aR := fun (R : Type (u + 1)) [CommRing R] ↦
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} R) e.restrict.i (pullback.fst e.g d.i)).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} R) e.restrict_i_fst).hom
  have h := tower_scalar_pasting
    (scalar X.smallEtaleTopology φ) (scalar e.restrict.Z.smallEtaleTopology φ)
    (scalar e.Z.smallEtaleTopology φ)
    (scalar Y.smallEtaleTopology φ) (scalar d.Z.smallEtaleTopology φ)
    (scalar Z.smallEtaleTopology φ)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    ((lowerStar (ModuleCat.{u + 1} A) e.restrict.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} A) e.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g)).rightDerivedFunctor)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    ((lowerStar (ModuleCat.{u + 1} B) e.restrict.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) e.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) d.g).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} B) (e.g ≫ d.g)).rightDerivedFunctor)
    (etOpen φ e.restrict.i).hom
    (etOpen φ (pullback.fst e.g d.i)).hom
    (etOpen φ e.i).hom (etOpen φ d.i).hom
    (etaleGamma φ e.restrict.g) (etaleGamma φ e.g)
    (etaleGamma φ d.g) (etaleGamma φ (e.g ≫ d.g))
    (aR A) (aR B)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} A) e.isPullback_restrict)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} B) e.isPullback_restrict)
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g d.g).hom
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) e.g d.g).hom M ho hp hi
  simpa only [rightDerivedLowerShriekOfCompactificationCompIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, asIso_hom,
    beta,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map,
    Compactification.comp, Compactification.copy,
    Compactification.postcomp, rightDerivedLowerStar, aR] using h

private noncomputable def ordinaryChosen
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  beta φ (HasCompactification.compactification f)

private noncomputable def ordinaryTower
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (d : ℕ) :
    affineTraceLeft A S d ⋙ scalar S.smallEtaleTopology φ ⟶
      scalar (affineTraceTower S d).smallEtaleTopology φ ⋙ affineTraceLeft B S d :=
  affineTraceExchangeTower
    (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
    (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
    (fun r ↦ scalar (affineTraceTower S r).smallEtaleTopology φ)
    (fun r ↦ beta φ (affineTraceLineCompactification (affineTraceTower S r))) d

private theorem ordinaryTower_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (d : ℕ)
    (M : DerivedCategoryModule A (affineTraceTower S d)) :
    (ordinaryTower φ S d).app M = orderedFiniteAffineCoefficientMap φ S d M := by
  induction d with
  | zero =>
    simp only [ordinaryTower, affineTraceExchangeTower_zero,
      orderedFiniteAffineCoefficientMap]
    rfl
  | succ d ih =>
    simp only [ordinaryTower, affineTraceExchangeTower_succ,
      orderedFiniteAffineCoefficientMap]
    rw [← ih]
    rfl

private theorem ordinaryChosen_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A X) :
    (scalar Z.smallEtaleTopology φ).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      (ordinaryChosen φ (f ≫ g)).app M =
    (ordinaryChosen φ g).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
        ((ordinaryChosen φ f).app M) ≫
      (unboundedEtaleLowerShriekCompIso B f g).hom.app
        ((scalar X.smallEtaleTopology φ).obj M) := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict
  apply composition_scalar_transport (scalar X.smallEtaleTopology φ) (scalar Y.smallEtaleTopology φ)
    (scalar Z.smallEtaleTopology φ)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (rightDerivedLowerShriekIso A e.restrict) (rightDerivedLowerShriekIso A d)
    (rightDerivedLowerShriekIso A (d.comp e))
    (rightDerivedLowerShriekIso B e.restrict) (rightDerivedLowerShriekIso B d)
    (rightDerivedLowerShriekIso B (d.comp e))
    (unboundedEtaleLowerShriekCompIso A f g)
    (rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (unboundedEtaleLowerShriekCompIso B f g)
    (rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (ordinaryChosen φ f) (beta φ e.restrict)
    (ordinaryChosen φ g) (beta φ d)
    (ordinaryChosen φ (f ≫ g)) (beta φ (d.comp e)) M
  · exact ordinaryCompactificationScalar φ e.restrict
      (HasCompactification.compactification f) M
  · exact ordinaryCompactificationScalar φ d
      (HasCompactification.compactification g) _
  · exact ordinaryCompactificationScalar φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M
  · exact ordinaryCompactTowerScalar φ f g d e M

private theorem ordinaryAffine_compatibility
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : DerivedCategoryModule A (affineTraceTower S d)) :
    (scalar S.smallEtaleTopology φ).map
        ((affineTraceUnboundedCompactComparison A S d).hom.app M) ≫
      (ordinaryChosen φ (affineTraceProjection S d)).app M =
    (ordinaryTower φ S d).app M ≫
      (affineTraceUnboundedCompactComparison B S d).hom.app
        ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M) := by
  induction d with
  | zero =>
    let c := Compactification.ofIsProper (𝟙 S)
    let eA := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    let eB := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso B S
    have hUA : (affineTraceUnboundedCompactComparison A S 0).hom.app M =
        eA.inv.app M ≫ (rightDerivedLowerShriekIso A c).hom.app M := by
      simp only [affineTraceUnboundedCompactComparison, Iso.symm_hom]
      rw [identity_comparison]
      rfl
    have hUB : (affineTraceUnboundedCompactComparison B S 0).hom.app
        ((scalar (affineTraceTower S 0).smallEtaleTopology φ).obj M) =
        eB.inv.app ((scalar S.smallEtaleTopology φ).obj M) ≫
          (rightDerivedLowerShriekIso B c).hom.app
            ((scalar S.smallEtaleTopology φ).obj M) := by
      simp only [affineTraceUnboundedCompactComparison, Iso.symm_hom]
      rw [identity_comparison]
      rfl
    have hc := ordinaryCompactificationScalar φ c
      (HasCompactification.compactification (𝟙 S)) M
    have hi := ordinaryIdentityCompact_scalar φ S M
    exact zero_assemble (scalar S.smallEtaleTopology φ) _ _ _ _ _ _ _ _ _ hUA hUB
      (by simp only [ordinaryTower, affineTraceExchangeTower_zero]; rfl) hc
      (inverse_square (scalar S.smallEtaleTopology φ) (eA.app M)
        (eB.app ((scalar S.smallEtaleTopology φ).obj M)) _ hi)
  | succ d ih =>
    let := affineTraceNoetherian S d
    let : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let c := affineTraceLineCompactification (affineTraceTower S d)
    have hcomp := ordinaryChosen_composition φ q (affineTraceProjection S d) M
    have hline := ordinaryCompactificationScalar φ c
      (HasCompactification.compactification q) M
    have hn := (ordinaryTower φ S d).naturality
      ((rightDerivedLowerShriekIso A c).hom.app M)
    have hn' := (affineTraceUnboundedCompactComparison B S d).hom.naturality
      ((ordinaryChosen φ q).app M)
    simp only [Functor.comp_map] at hn hn'
    rw [comparison_succ_app, comparison_succ_app]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hcomp]
    erw [reassoc_of% (ih _)]
    erw [reassoc_of% hn]
    erw [← reassoc_of% hn']
    simp only [← CategoryTheory.Functor.map_comp_assoc]
    erw [hline]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [ordinaryTower, affineTraceExchangeTower_succ, Category.assoc]
    rfl

private theorem comparison_eq
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (orderedFiniteCompactificationComparison R k S d c M).hom =
      (affineTraceUnboundedCompactComparison R S d).hom.app M.obj ≫
        (rightDerivedLowerShriekOfCompactificationIso R
          (HasCompactification.compactification (affineTraceProjection S d)) c).hom.app M.obj := by
  have := affineTraceNoetherian S d
  unfold orderedFiniteCompactificationComparison
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [unboundedEtaleCompactSupport_comparison_plus R
    (affineTraceProjection S d) _ c M]
  apply (cancel_epi ((affineTracePlusCompatibility R S d).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  have hh := congrArg (fun z ↦ z ≫ (rightDerivedLowerShriekOfCompactificationIso R
    (HasCompactification.compactification (affineTraceProjection S d)) c).hom.app M.obj)
      (affineTraceUnboundedCompactComparison_restriction R S d M).symm
  simpa only [rightDerivedLowerShriekPlus_eq, rightDerivedLowerShriek_eq,
    rightDerivedLowerShriekPlusCompatibility, Functor.comp_obj,
    ObjectProperty.ι_obj, Category.assoc] using hh

private theorem comparison_via
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c c' e : Compactification (affineTraceProjection S d))
    (r : e.Refinement c') (s : e.Refinement c)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    orderedFiniteCompactificationComparisonVia R k S d c c' e r s M =
      orderedFiniteCompactificationComparison R k S d c M := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := ⟨⟩
  have := affineTraceNoetherian S d
  unfold orderedFiniteCompactificationComparisonVia orderedFiniteCompactificationComparison
  simp only [rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq,
    rightDerivedLowerShriekOfCompactificationPlusIso_symm]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have h := congrArg (fun z ↦ z.hom.app M)
    (rightDerivedLowerShriekOfCompactificationPlusIso_trans R
      (HasCompactification.compactification (affineTraceProjection S d)) c' e)
  have h' := congrArg (fun z ↦ z.hom.app M)
    (rightDerivedLowerShriekOfCompactificationPlusIso_trans R
      (HasCompactification.compactification (affineTraceProjection S d)) e c)
  simp only [Iso.trans_hom, NatTrans.comp_app] at h h'
  simp only [← Iso.symm_hom,
    rightDerivedLowerShriekOfCompactificationPlusIso_symm]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% h, h', Functor.map_comp]
  simp only [Category.assoc]

/-- The ordered proper/open coefficient recursion agrees with the coefficient map for
any specified compactification. The equality also uses the same canonical comparison
through every common refinement, including arbitrary compactifications at dimension zero.

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: ordered projective-line integration
(blueprint: lem-sp-ordered-compactification-scalar-square).

Proof:
1. Finite type over a field makes the base Noetherian. Represent the finite-Tor input
   by a bounded flat constructible complex. The ordinary extension functor's derived
   counit is invertible on this K-flat model, so the extended complex gives hMB.
2. Transpose the exact scalar-restriction pullback comparison through the actual scalar
   adjunction. Its composition and identity laws give those of etaleIso. The geometric
   mate formulas give the corresponding laws for etaleGamma and etOpen.
3. Transpose the coefficient cube through the geometric adjunctions. The normalized
   proper/open exchange and its open-unit equation give the scalar exchange square.
   Paste with the open and proper composition laws to obtain the compact compositor
   square. The refinement transpose equation gives the pairwise scalar square.
4. Induct on the coordinate count. At zero use the identity normalization followed by
   the pairwise comparison to the chosen compactification. At a successor paste the
   line comparison, the preceding tower square, and the compact compositor square.
5. The bounded/unbounded restriction theorem identifies the displayed comparison with
   the unbounded tower comparison followed by the comparison to c. Paste their scalar
   squares. The pairwise cocycle gives both Via equalities through every refinement.
All scalar maps are the ordinary finite-coefficient maps; no withdrawn model is used. -/
theorem orderedCompactification_scalar_square_finiteCoefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (n : ℕ)
    (_hA : ((ℓ ^ n : ℕ) : A) = 0) (_hB : ((ℓ ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hM : Input A (affineTraceTower S d) M.obj) :
    ∃ hMB : _root_.DerivedCategory.TStructure.t.plus
        ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj),
      ((scalar S.smallEtaleTopology φ).map
          (orderedFiniteCompactificationComparison A k S d c M).hom ≫
          (beta φ c).app M.obj =
        orderedFiniteAffineCoefficientMap φ S d M.obj ≫
          (orderedFiniteCompactificationComparison B k S d c
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩).hom) ∧
      (∀ (c' e : Compactification (affineTraceProjection S d))
        (r : e.Refinement c') (s : e.Refinement c),
        orderedFiniteCompactificationComparisonVia A k S d c c' e r s M =
          orderedFiniteCompactificationComparison A k S d c M ∧
        orderedFiniteCompactificationComparisonVia B k S d c c' e r s
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩ =
          orderedFiniteCompactificationComparison B k S d c
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := ⟨⟩
  have := affineTraceNoetherian S d
  have hMB := ordinaryScalar_plus φ (affineTraceTower S d) M.obj _hM
  refine ⟨hMB, ?_, fun c' e r s ↦ ⟨comparison_via A k S d c c' e r s M,
    comparison_via B k S d c c' e r s ⟨_, hMB⟩⟩⟩
  rw [comparison_eq, comparison_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [ordinaryCompactificationScalar φ
    (HasCompactification.compactification (affineTraceProjection S d)) c M.obj]
  rw [← Category.assoc]
  erw [ordinaryAffine_compatibility φ S d M.obj]
  rw [ordinaryTower_app]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale

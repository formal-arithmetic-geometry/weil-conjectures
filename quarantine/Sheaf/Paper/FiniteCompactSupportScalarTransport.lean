/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module
public import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.Paper.EtaleProEtaleScalarMate

/-!
# Canonical transport of the finite compact-support scalar mate

Source: Stacks Tags 0GL6 and 09AL; the scalar-mate compatibility of the etale and
pro-etale comparisons, followed by the normalized intrinsic realization.
(blueprint: lem-finite-compact-support-scalar-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteCompactScalar

/-- The scalar/open comparison fixed by uniqueness of the left adjoint. -/
@[irreducible] def openScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory := by
  let ea := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let eb := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let adjA := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight ea.symm).mapDerivedCategoryAdjunction
  let adjB := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight eb.symm).mapDerivedCategoryAdjunction
  let adjX := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let adjZ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let e := Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)
  exact (adjA.comp adjZ).leftAdjointUniq ((adjX.comp adjB).ofNatIsoRight e.symm)

/-- Proper scalar extension followed by the open scalar comparison. -/
@[irreducible] def compactScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  have : ∀ L, IsIso ((scalarMate φ c.g).app L) :=
    (properFiniteCoefficientExtension φ c.g).1
  have : IsIso (scalarMate φ c.g) := NatIso.isIso_of_isIso_app _
  let e := asIso (scalarMate φ c.g)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openScalarIso φ c.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Etale.FiniteCompactScalar

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The actual sheaf map of constant coefficient rings. -/
abbrev scalarRingMap
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  proEtaleConstantRingMap (T := T) φ

/-- The scalar comparison through intrinsic realization, fixed by its right square. -/
@[irreducible] def realizationScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        (sfIntrinsicDerivedEquivalence T B).functor := by
  let EA := sfIntrinsicDerivedEquivalence T A
  let EB := sfIntrinsicDerivedEquivalence T B
  let ρ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B := scalarRingMap φ T
  let adj : pbcDerivedExtend.{u} ρ ⊣ pbcDerivedRestrict.{u} ρ := pbcDerivedScalarAdjunction ρ
  let rightIso : pbcDerivedRestrict.{u} ρ ⋙
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence T B).inverse.mapDerivedCategory ⋙
      @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) := by
    simpa only [ρ, pbcDerivedRestrict, pbcRestrict, scalarRingMap, proEtaleConstantRingMap,
      proEtaleCoefficientRestrictScalars, sfFixedRestriction, Sheaf.restrictScalars,
      Sheaf.derivedRestrictScalars] using
      Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  let s : EA.functor ⋙ pbcDerivedExtend.{u} ρ ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ EB.functor :=
    ((EA.toAdjunction.comp adj).ofNatIsoRight
      rightIso).leftAdjointUniq
      ((Adjunction.ofIsRightAdjoint
        (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ))).comp EB.toAdjunction)
  exact s

/-- The termwise factorization of intrinsic site comparison through realization. -/
def intrinsicSiteFunctorIso (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  Functor.mapDerivedCategoryCompIso _ _

/-- Site comparison and coefficient extension, in the intrinsic ringed presentation. -/
@[irreducible] def siteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      Etale.scalarExtension.{u} (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison T B :=
  Functor.isoWhiskerRight (intrinsicSiteFunctorIso A T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (realizationScalarIso φ T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcComparisonReduction.{u} T (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (intrinsicSiteFunctorIso B T).symm

/-- Compact support through realization, using the normalized proper comparison. -/
@[irreducible] def compactRealizationIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let J := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let o : EX.functor ⋙ sfIntrinsicExtensionByZero c.i A ≅ J ⋙ EZ.functor :=
    EX.funInvIdAssoc (J ⋙ EZ.functor)
  let od := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ Functor.mapDerivedCategoryCompIso _ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight od _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The compact-support site comparison at a bounded-below etale input. -/
@[irreducible] def compactSiteIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj G.obj) ≅
      (sfIntrinsicCompactSupport c A).obj
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) :=
  (intrinsicSiteFunctorIso A Y).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      ((ProEtale.compactSupportSiteComparison (ULift.{u + 1, u} A) c).app G).symm ≪≫
    (compactRealizationIso A c).symm.app _ ≪≫
    (sfIntrinsicCompactSupport c A).mapIso ((intrinsicSiteFunctorIso A X).app G.obj).symm

/-- The explicit transported proper/open coefficient isomorphism at an etale origin. -/
@[irreducible] def intrinsicCompactScalarIsoOfOrigin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj ≅
      GB.obj) :
    (pbcDerivedExtend.{u} (scalarRingMap φ Y)).obj
        ((sfIntrinsicCompactSupport c A).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) ≅
      (sfIntrinsicCompactSupport c B).obj
        ((pbcDerivedExtend.{u} (scalarRingMap φ X)).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) :=
  (pbcDerivedExtend.{u} (scalarRingMap φ Y)).mapIso (compactSiteIso A c G).symm ≪≫
    (siteScalarIso φ Y).app _ ≪≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).mapIso
      ((Etale.FiniteCompactScalar.compactScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app G.obj ≪≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).mapIso eGB) ≪≫
    compactSiteIso B c GB ≪≫
    (sfIntrinsicCompactSupport c B).mapIso
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).mapIso eGB.symm ≪≫
        (siteScalarIso φ X).symm.app G.obj)

private theorem scalar_transpose_paste
    {C₀ C₁ Z₀ Z₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category Z₀] [Category Z₁]
    [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sz : Z₀ ⥤ Z₁} {Rz : Z₁ ⥤ Z₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (az : Sz ⊣ Rz) (ay : Sy ⊣ Ry)
    (J₀ : C₀ ⥤ Z₀) (J₁ : C₁ ⥤ Z₁)
    (P₀ : Z₀ ⥤ D₀) (P₁ : Z₁ ⥤ D₁)
    (j : Rx ⋙ J₀ ⟶ J₁ ⋙ Rz) (p : Rz ⋙ P₀ ⟶ P₁ ⋙ Ry)
    (K : C₀) :
    (ay.homEquiv _ _).symm
      (P₀.map (J₀.map (ax.unit.app K)) ≫
        P₀.map (j.app (Sx.obj K)) ≫ p.app (J₁.obj (Sx.obj K))) =
      (ay.homEquiv _ _).symm
        (P₀.map (az.unit.app (J₀.obj K)) ≫ p.app (Sz.obj (J₀.obj K))) ≫
      P₁.map ((az.homEquiv _ _).symm
        (J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K))) := by
  let b := (az.homEquiv _ _).symm
    (J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K))
  apply (ay.homEquiv _ _).injective
  dsimp only [Functor.id_obj] at *
  rw [Equiv.apply_symm_apply, ay.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  change _ = (P₀.map (az.unit.app (J₀.obj K)) ≫ p.app _) ≫ Ry.map (P₁.map b)
  have hp := p.naturality b
  change P₀.map (Rz.map b) ≫ p.app _ = p.app _ ≫ Ry.map (P₁.map b) at hp
  dsimp only [Functor.id_obj] at hp
  rw [Category.assoc, ← hp]
  change _ = P₀.map (az.unit.app (J₀.obj K)) ≫ P₀.map (Rz.map b) ≫ _
  have hb : az.unit.app (J₀.obj K) ≫ Rz.map b =
      J₀.map (ax.unit.app K) ≫ j.app (Sx.obj K) :=
    az.homEquiv_apply _ _ b |>.symm.trans (Equiv.apply_symm_apply _ _)
  simpa only [P₀.map_comp, Category.assoc] using
    congrArg (fun t ↦ P₀.map t ≫ p.app (J₁.obj (Sx.obj K))) hb.symm


private theorem intrinsic_scalar_transpose_paste
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
      ((sfIntrinsicCompactSupport c A).map
          ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ)).unit.app K) ≫
        (sfCompactSupportRestriction c φ).hom.app
          ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K)) =
      ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ)).homEquiv _ _).symm
        ((proEtaleConstantDerivedDirectImage c.g A).map
            ((pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := c.Z) φ)).unit.app
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K)) ≫
          (sfDerivedImageRestriction c.g φ).hom.app
            ((pbcDerivedExtend (proEtaleConstantRingMap (T := c.Z) φ)).obj
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K))) ≫
        (proEtaleConstantDerivedDirectImage c.g B).map
          (((pbcDerivedScalarAdjunction
            (proEtaleConstantRingMap (T := c.Z) φ)).homEquiv _ _).symm
              ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.map
                  ((pbcDerivedScalarAdjunction
                    (proEtaleConstantRingMap (T := X) φ)).unit.app K) ≫
                (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom.app
                  ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K))) := by
  simpa only [sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate,
    sfCompactSupportRestriction, Functor.comp_map, Functor.comp_obj, Category.assoc,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using scalar_transpose_paste
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := c.Z) φ))
      (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) φ))
      (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
      (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
      (proEtaleConstantDerivedDirectImage c.g A)
      (proEtaleConstantDerivedDirectImage c.g B)
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom
      (sfDerivedImageRestriction c.g φ).hom K


/-- Canonical transport identifies the scalar transpose, including its units and counits.
This is an equality of maps, rather than merely an isomorphism between their endpoints.

Source: Stacks Tags 0GL6, 09AL and 0D6J; the scalar-mate compatibility of
`etaleProEtale_scalar_mate`, followed by intrinsic realization.
(blueprint: lem-finite-compact-support-scalar-transport).

Proof: factor compact support as open extension followed by proper direct image.
Adjunction naturality factors its scalar transpose as the proper scalar transpose
followed by proper image of the open scalar transpose. For open extension the two
scalar composites are left adjoint to the same restriction composite. Its
unit-preserving uniqueness map is precisely openScalarIso; transporting the
sectionwise realization restriction square gives sfOpenRestriction. For proper
image, compute the restriction square and the realization square on a K-injective
B-complex and a K-injective resolution after restriction. The defining equations of
sfDerivedImageRestriction and sfIntrinsicDerivedDirectImageComparison identify both
paths with the same direct image of the resolution arrow, so cancellation of its
quasi-isomorphism gives equality. On the fixed-scalar sites apply
etaleProEtale_scalar_mate; boundedness of G and GB supplies its two bounded-below
hypotheses. The K-flat normalization of the inverse pullback mate identifies its
etale scalar pullback comparison with scalarPullbackIso. Whisker these identities,
then cancel the site and realization unit/counit isomorphisms. The resulting
composite is exactly intrinsicCompactScalarIsoOfOrigin, proving the equality.
The argument also covers zero rings, empty schemes and identity coefficient maps. -/
theorem intrinsicCompactScalarIsoOfOrigin_hom
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj ≅
      GB.obj) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Y)).homEquiv _ _).symm
      ((sfIntrinsicCompactSupport c A).map
          ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) ≫
        (sfCompactSupportRestriction c φ).hom.app
          ((pbcDerivedExtend (scalarRingMap φ X)).obj
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj))) =
      (intrinsicCompactScalarIsoOfOrigin φ c G GB eGB).hom := by
  sorry

end AlgebraicGeometry.Scheme.FiniteCompactScalar

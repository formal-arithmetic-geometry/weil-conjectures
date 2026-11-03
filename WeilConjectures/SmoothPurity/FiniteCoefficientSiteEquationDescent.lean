/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoefMonoidalSquareHomTransport
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite coefficient scalar/site equation descent

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).

The theorem below uses the actual ordinary derived categories of module sheaves on the
small etale and pro-etale sites.  Its scalar functors are the fixed-coefficient derived
extensions, its site functors are the derived comparison inverse images, and its square
is the published balanced K-flat comparison iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance 2000] isNoetherian_of_finite

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures
open AlgebraicGeometry

namespace WeilConjectures

/-- A canonical K-flat tensorator for fixed-coefficient derived extension.

The ordinary sheafified scalar extension is strong monoidal by the balanced module tensor.
Its left derived monoidal structure is transported along the unique adjunction isomorphism to
`fixedCoefficientDerivedScalarExtension`; this pins the tensorator on K-flat representatives
rather than choosing an arbitrary monoidal structure.
Source: Stacks Tags 03EK, 06YY and 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
@[instance_reducible]
noncomputable def finiteCoefficientScalarMonoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension J f).Monoidal := by
  letI := f.toAlgebra
  let E := AlgebraicGeometry.CoefficientScalarRepresentatives.ordinaryExtension J f
  let adj : E ⊣ CategoryTheory.Sheaf.restrictScalars J f :=
    AlgebraicGeometry.CoefficientScalarRepresentatives.ordinaryAdjunction J f
  letI : E.IsLeftAdjoint := adj.isLeftAdjoint
  letI : E.PreservesFlat := by
    constructor
    intro M hM
    exact CategoryTheory.Sheaf.flat_extendScalars_obj J f hM
  letI : E.OplaxMonoidal :=
    CategoryTheory.composeAndSheafifyOplaxMonoidal J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  letI (M N : _) : IsIso (Functor.OplaxMonoidal.δ E M N) :=
    CategoryTheory.isIso_δ_composeAndSheafify J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f) M N
  letI : IsIso (Functor.OplaxMonoidal.η E) :=
    CategoryTheory.isIso_η_composeAndSheafify J
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  letI : E.Monoidal := .ofOplaxMonoidal E
  letI : E.PreservesKFlatQuasiIso := by
    classical
    let U := CategoryTheory.Sheaf.restrictScalars J f
    let B' := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).obj
      (ModuleCat.of B B)
    let X' := (Functor.const Cᵒᵖ).obj B'
    let a := presheafToSheaf J (ModuleCat.{u + 1} A)
    let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
    let F' := sheafToPresheaf J (ModuleCat.{u + 1} A)
    let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)
    have hs : J.PreservesSheafification
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) :=
      Sheaf.preservesSheafification_of_adjunction J
        (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f)
    let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X') :=
      Functor.associator F' (W ⋙ a') U ≪≫
        Functor.isoWhiskerLeft F' (Functor.associator W a' U) ≪≫
        Functor.isoWhiskerLeft F' (Functor.isoWhiskerLeft W
          (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)
            (sheafificationAdjunction J (ModuleCat.{u + 1} B))
            (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
        Functor.isoWhiskerLeft F' (Functor.associator W _ a).symm ≪≫
        Functor.isoWhiskerLeft F' (Functor.isoWhiskerRight
          (Functor.whiskeringRightObjCompIso _ _ ≪≫
            (Functor.whiskeringRight _ _ _).mapIso
              (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} f) ≪≫
            whiskeringRightTensorRightIso _) a) ≪≫
        Functor.isoWhiskerLeft F' (Sheaf.presheafToSheafCompTensorRightIso X').symm ≪≫
        (Functor.associator F' a (MonoidalCategory.tensorRight (a.obj X'))).symm ≪≫
        Functor.isoWhiskerRight
          (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
          (MonoidalCategory.tensorRight (a.obj X')) ≪≫ Functor.leftUnitor _
    have hU : U.Faithful := inferInstance
    have hc : HasColimitsOfSize.{u + 1, u + 1}
        (Sheaf J (ModuleCat.{u + 1} A)) := IsGrothendieckAbelian.hasColimits _
    have hc0 : HasColimitsOfSize.{0, 0}
        (Sheaf J (ModuleCat.{u + 1} A)) :=
      hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
    have hcc : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
      ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X')
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  letI : E.leftDerivedFunctor.Monoidal := E.leftDerivedFunctorMonoidal
  let dadj : E.leftDerivedFunctor ⊣ CategoryTheory.Sheaf.derivedRestrictScalars J f :=
    adj.derivedAdjunction.ofNatIsoRight
      (CategoryTheory.Sheaf.restrictScalars J f).rightDerivedFunctorIsoMapDerivedCategory
  let fadj : AlgebraicGeometry.CoefficientScalarRepresentatives.extension J f ⊣
      CategoryTheory.Sheaf.derivedRestrictScalars J f :=
    AlgebraicGeometry.CoefficientScalarRepresentatives.adjunction J f
  let e := fadj.leftAdjointUniq dadj
  exact Functor.Monoidal.transport e.symm

/-- The equation package for the displayed monoidal square.  The four tensorators and the
monoidal comparison proof are explicit arguments, so the package cannot replace the canonical
maps by existentially chosen structures.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
def FiniteCoefficientSiteEquationLaws
    {EA : Type u} [Category.{v} EA] [MonoidalCategory EA] [MonoidalClosed EA]
    {EB : Type u₁} [Category.{v₁} EB] [MonoidalCategory EB] [MonoidalClosed EB]
    {PA : Type u₂} [Category.{v₂} PA] [MonoidalCategory PA] [MonoidalClosed PA]
    {PB : Type u₃} [Category.{v₃} PB] [MonoidalCategory PB] [MonoidalClosed PB]
    [BraidedCategory EA] [BraidedCategory EB] [BraidedCategory PA] [BraidedCategory PB]
    (F : EA ⥤ EB) (G : PA ⥤ PB) (UA : EA ⥤ PA) (UB : EB ⥤ PB)
    (h : F ⋙ UB ≅ UA ⋙ G)
    (mF : F.Monoidal) (mG : G.Monoidal) (mUA : UA.Monoidal) (mUB : UB.Monoidal)
    (hm : NatTrans.IsMonoidal h.hom) (successive : Prop) : Prop :=
  letI : F.Monoidal := mF
  letI : G.Monoidal := mG
  letI : UA.Monoidal := mUA
  letI : UB.Monoidal := mUB
  letI : NatTrans.IsMonoidal h.hom := hm
  InternalHomComparisonLaws F ∧
    InternalHomComparisonLaws G ∧
    InternalHomComparisonLaws UA ∧
    InternalHomComparisonLaws UB ∧
    (∀ (K M : EA),
      F.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ F K M ≫
          (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K) ∧
    (∀ (K M : PA),
      G.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ G K M ≫
          (β_ (G.obj K) (G.obj M)).hom ≫ Functor.LaxMonoidal.μ G M K) ∧
    (∀ (K M : EA),
      UA.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ UA K M ≫
          (β_ (UA.obj K) (UA.obj M)).hom ≫ Functor.LaxMonoidal.μ UA M K) ∧
    (∀ (K M : EB),
      UB.map (β_ K M).hom =
        Functor.OplaxMonoidal.δ UB K M ≫
          (β_ (UB.obj K) (UB.obj M)).hom ≫ Functor.LaxMonoidal.μ UB M K) ∧
    (∀ (S T : EA),
      Functor.LaxMonoidal.μ UB (F.obj S) (F.obj T) ≫
          UB.map (Functor.LaxMonoidal.μ F S T) ≫
          UB.map (F.map (β_ S T).hom) ≫
          h.hom.app (T ⊗ S) =
        (h.hom.app S ⊗ₘ h.hom.app T) ≫
          Functor.LaxMonoidal.μ G (UA.obj S) (UA.obj T) ≫
          G.map (Functor.LaxMonoidal.μ UA S T) ≫
          G.map (UA.map (β_ S T).hom)) ∧
    (∀ (K M : EA),
      h.hom.app (K ⟶[EA] M) ≫
          G.map (internalHomComparison UA K M) ≫
          internalHomComparison G (UA.obj K) (UA.obj M) =
        UB.map (internalHomComparison F K M) ≫
          internalHomComparison UB (F.obj K) (F.obj M) ≫
          internalHomTransport h K M) ∧
    NatTrans.IsMonoidal h.hom ∧ successive

/-- The ordinary derived category on the small etale site with constant coefficients.
Source: blueprint `def-weil-sheaf-of-modules-category` and
`def-weil-abstract-derived-category` (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
abbrev finiteEtaleDerivedCategory (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- The ordinary derived category on the small pro-etale site with constant coefficients.
Source: blueprint `def-weil-sheaf-of-modules-category` and
`def-weil-abstract-derived-category` (blueprint: lem-coef-finite-hom-site-equation-descent).
-/
abbrev finiteProEtaleDerivedCategory (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))

private noncomputable instance finiteEtaleDerivedBraided
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    BraidedCategory (finiteEtaleDerivedCategory X R) :=
  DerivedCategory.braidedCategory' _

private noncomputable instance finiteProEtaleDerivedBraided
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    BraidedCategory (finiteProEtaleDerivedCategory X R) :=
  DerivedCategory.braidedCategory' _

/-- Fixed-coefficient derived extension on the small etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteEtaleCoefficientExtension
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : finiteEtaleDerivedCategory X A ⥤ finiteEtaleDerivedCategory X B :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology f

/-- Fixed-coefficient derived extension on the small pro-etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteProEtaleCoefficientExtension
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) : finiteProEtaleDerivedCategory X A ⥤ finiteProEtaleDerivedCategory X B :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology X) f

/-- The sheaf-level identity restriction iso used to normalize scalar extension at `RingHom.id`.
Source: the identity restriction-of-scalars equivalence for sheaves of modules, used for the
identity-ring-map clause of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent). -/
noncomputable def finiteCoefficientRestrictionIdentityIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.restrictScalars J (RingHom.id A) ≅
      𝟭 (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A)) := by
  refine NatIso.ofComponents (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso ?_) ?_
  · exact Functor.isoWhiskerLeft F.obj
      (ModuleCat.restrictScalarsId.{u + 1, u + 1} A)
  · intro F G φ
    apply (fullyFaithfulSheafToPresheaf J _).map_injective
    ext U y
    exact congrArg (fun q ↦ q y)
      ((ModuleCat.restrictScalarsId.{u + 1, u + 1} A).hom.naturality (φ.hom.app U))

/-- Derived version of `finiteCoefficientRestrictionIdentityIso`, normalized to the identity
functor by `mapDerivedCategoryIdIso`.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
noncomputable def finiteCoefficientDerivedRestrictionIdentityIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.derivedRestrictScalars J (RingHom.id A) ≅
      𝟭 (DerivedCategory (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A))) := by
  simpa only [CategoryTheory.Sheaf.derivedRestrictScalars] using
    Functor.mapDerivedCategoryNatIso (finiteCoefficientRestrictionIdentityIso J) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical derived scalar-extension unitor at an identity ring map.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
noncomputable def finiteCoefficientIdentityUnitor
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A] :
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension J (RingHom.id A) ≅
      𝟭 (DerivedCategory (CategoryTheory.Sheaf J (ModuleCat.{u + 1} A))) :=
  ((AlgebraicGeometry.CoefficientScalarRepresentatives.adjunction J (RingHom.id A)).ofNatIsoRight
    (finiteCoefficientDerivedRestrictionIdentityIso J)).leftAdjointUniq Adjunction.id

/-- Derived inverse image of the etale-to-pro-etale comparison morphism.
Source: Stacks Project, Tags 03D2 and 07A4 (blueprint: def-weil-pbc-site-comparison-morphism).
-/
noncomputable def finiteSiteComparisonPullback
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    finiteEtaleDerivedCategory X R ⥤ finiteProEtaleDerivedCategory X R :=
  (AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} R) X).mapDerivedCategory

/-- The balanced scalar/site comparison on derived categories.
Source: Stacks Project, Tag 07A4 (blueprint: def-weil-pbc-site-comparison-morphism and
`lem-sfb-scalar-inverse-image-tower-diagram`).  It is the inverse of the published
`comparisonIso` because that declaration is oriented from pullback-after-scalar to
scalar-after-pullback.
-/
noncomputable def finiteCoefficientSiteComparison
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) :
    finiteEtaleCoefficientExtension X f ⋙ finiteSiteComparisonPullback X B ≅
      finiteSiteComparisonPullback X A ⋙ finiteProEtaleCoefficientExtension X f :=
  (AlgebraicGeometry.CoefficientScalarRepresentatives.comparisonIso X f).symm

/-- The balanced comparison carries the canonical strong-monoidal structures.
Source: Stacks Tags 03EL and 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
The proof is the K-flat representative tensor calculation for the published comparison iso. -/
theorem finiteCoefficientSiteComparison_isMonoidal
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) :
    letI : (finiteEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal X.smallEtaleTopology f
    letI : (finiteSiteComparisonPullback X B).Monoidal :=
      AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
        (ModuleCat.{u + 1} B) X
    letI : (finiteSiteComparisonPullback X A).Monoidal :=
      AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
        (ModuleCat.{u + 1} A) X
    letI : (finiteProEtaleCoefficientExtension X f).Monoidal :=
      finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
    NatTrans.IsMonoidal (finiteCoefficientSiteComparison X f).hom := by
  sorry

/-- The balanced scalar associator on the etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteEtaleCoefficientComposition
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    finiteEtaleCoefficientExtension X f ⋙ finiteEtaleCoefficientExtension X g ≅
      finiteEtaleCoefficientExtension X (g.comp f) :=
  AlgebraicGeometry.CoefficientScalarRepresentatives.composition X.smallEtaleTopology f g

/-- The balanced scalar associator on the pro-etale site.
Source: Stacks Project, Tag 06YY (blueprint: lem-pur-derived-change-of-rings).
-/
noncomputable def finiteProEtaleCoefficientComposition
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    finiteProEtaleCoefficientExtension X f ⋙ finiteProEtaleCoefficientExtension X g ≅
      finiteProEtaleCoefficientExtension X (g.comp f) :=
  AlgebraicGeometry.CoefficientScalarRepresentatives.composition
    (Scheme.ProEt.topology X) f g

/-- The h-tower equation for the concrete maps `f`, `g`, and `g.comp f`.
Source: Stacks Project, Tag 07A4 (blueprint: lem-coef-finite-hom-site-equation-descent).
The two displayed associators are the balanced scalar associators on the etale and
pro-etale sites; the equation is the objectwise coherence equation in the successive
Hom-transport predicate.
-/
def FiniteCoefficientSiteTowerEquation
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : Prop :=
  let αet := finiteEtaleCoefficientComposition X f g
  let αpro := finiteProEtaleCoefficientComposition X f g
  let hAB := finiteCoefficientSiteComparison X f
  let hBC := finiteCoefficientSiteComparison X g
  let hAC := finiteCoefficientSiteComparison X (g.comp f)
  ∀ T : finiteEtaleDerivedCategory X A,
    (finiteSiteComparisonPullback X C).map (αet.inv.app T) ≫
        hBC.hom.app ((finiteEtaleCoefficientExtension X f).obj T) ≫
        (finiteProEtaleCoefficientExtension X g).map (hAB.hom.app T) ≫
        αpro.hom.app ((finiteSiteComparisonPullback X A).obj T) =
      hAC.hom.app T

/-- The successive Hom equations for the concrete coefficient maps `f` and `g`.
The two equations use the balanced etale and pro-etale coefficient compositors directly; there
are no arbitrary further functors and no invertibility guards.  The identity clause explicitly
uses `RingHom.id` and the identity functor unitor.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md`, final paragraph
(blueprint: lem-coef-finite-hom-site-equation-descent).
-/
def FiniteCoefficientSuccessiveHomLaws
    (X : Scheme.{u}) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : Prop :=
  let F := finiteEtaleCoefficientExtension X f
  let FBC := finiteEtaleCoefficientExtension X g
  let FAC := finiteEtaleCoefficientExtension X (g.comp f)
  let G := finiteProEtaleCoefficientExtension X f
  let GBC := finiteProEtaleCoefficientExtension X g
  let GAC := finiteProEtaleCoefficientExtension X (g.comp f)
  let αet := finiteEtaleCoefficientComposition X f g
  let αpro := finiteProEtaleCoefficientComposition X f g
  letI : F.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology f
  letI : FBC.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology g
  letI : FAC.Monoidal := finiteCoefficientScalarMonoidal X.smallEtaleTopology (g.comp f)
  letI : G.Monoidal := finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f
  letI : GBC.Monoidal := finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) g
  letI : GAC.Monoidal :=
    finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) (g.comp f)
  letI : (finiteEtaleCoefficientExtension X (RingHom.id A)).Monoidal :=
    finiteCoefficientScalarMonoidal X.smallEtaleTopology (RingHom.id A)
  letI : (finiteProEtaleCoefficientExtension X (RingHom.id A)).Monoidal :=
    finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) (RingHom.id A)
  (FiniteCoefficientSiteTowerEquation X f g) ∧
    (∀ (K M : finiteEtaleDerivedCategory X A),
      internalHomComparison FAC K M ≫
          internalHomTransport αet.symm K M =
        αet.symm.hom.app (K ⟶[finiteEtaleDerivedCategory X A] M) ≫
          FBC.map (internalHomComparison F K M) ≫
          internalHomComparison FBC (F.obj K) (F.obj M)) ∧
    (∀ (K M : finiteProEtaleDerivedCategory X A),
      internalHomComparison GAC K M ≫
          internalHomTransport αpro.symm K M =
        αpro.symm.hom.app (K ⟶[finiteProEtaleDerivedCategory X A] M) ≫
          GBC.map (internalHomComparison G K M) ≫
          internalHomComparison GBC (G.obj K) (G.obj M)) ∧
    (∀ (K M : finiteEtaleDerivedCategory X A),
      let ι := RingHom.id A
      let Eι := finiteEtaleCoefficientExtension X ι
      let l := finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)
      internalHomComparison Eι K M ≫ internalHomTransport l K M =
        l.hom.app (K ⟶[finiteEtaleDerivedCategory X A] M)) ∧
    (finiteEtaleCoefficientComposition X (RingHom.id A) (RingHom.id A) ≪≫
        finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A) =
      Functor.isoWhiskerLeft (finiteEtaleCoefficientExtension X (RingHom.id A))
          (finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)) ≪≫
        Functor.rightUnitor (finiteEtaleCoefficientExtension X (RingHom.id A)) ≪≫
        finiteCoefficientIdentityUnitor X.smallEtaleTopology (A := A)) ∧
    (∀ (K M : finiteProEtaleDerivedCategory X A),
      let ι := RingHom.id A
      let Eι := finiteProEtaleCoefficientExtension X ι
      let l := finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A)
      internalHomComparison Eι K M ≫ internalHomTransport l K M =
        l.hom.app (K ⟶[finiteProEtaleDerivedCategory X A] M)) ∧
    (finiteProEtaleCoefficientComposition X (RingHom.id A) (RingHom.id A) ≪≫
        finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A) =
      Functor.isoWhiskerLeft (finiteProEtaleCoefficientExtension X (RingHom.id A))
          (finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A)) ≪≫
        Functor.rightUnitor (finiteProEtaleCoefficientExtension X (RingHom.id A)) ≪≫
        finiteCoefficientIdentityUnitor (Scheme.ProEt.topology X) (A := A))


/-- Finite coefficient scalar/site descent and evaluation compatibility.

Source: Stacks Project, Tags 07A4 and 08J9;
(blueprint: lem-coef-finite-hom-site-equation-descent), final paragraph.  The parameters are a
finite or algebraically closed field of characteristic `p`, distinct primes `p` and `ell`,
a positive exponent `N`, arbitrary finite commutative rings `A`, `B`, and `C` killed by
`ell ^ N`, ring maps `f` and `g`, and a separated finite-type `k`-scheme `X` over `Spec k`.
The conclusion uses the concrete ordinary unbounded derived categories of constant-coefficient
module sheaves on `X_et` and `X_proet`; its four functors are fixed coefficient derived
extensions and derived comparison inverse images, and its comparison is the balanced
K-flat representative iso `finiteCoefficientSiteComparison`.

The postponed proof has eight steps. (1) Choose flat-term K-flat resolutions and define the
balanced comparison independently of the resolution. (2) Check its tensor equation using the
K-flat tensor-pullback comparisons. (3) Check associators, unitors and signed symmetry.
(4) Define the four transpose maps by the closed tensor-Hom adjunction and prove their
transpose equation. (5) Prove naturality, internal-Hom composition and identity by uniqueness
of transpose. (6) Transport the etale/pro-etale Hom square through the tensor equation.
(7) Apply the same representative calculation to the balanced scalar tower `f`, `g`, and
`g.comp f`, including the two scalar associators. (8) Apply the identity tensorators to
the scalar unitors and retain the successive Hom equation and the identity unitors.
-/
theorem finiteCoefficientSiteEquationDescent
    (p ell N : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hpell : ell ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (C : Type (u + 1)) [CommRing C] [Finite C]
    (hN : 0 < N)
    (hNA : ((ell ^ N : ℕ) : A) = 0)
    (hNB : ((ell ^ N : ℕ) : B) = 0)
    (hNC : ((ell ^ N : ℕ) : C) = 0)
    (f : A →+* B) (g : B →+* C)
    (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] :
    letI : BraidedCategory (finiteEtaleDerivedCategory X A) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteEtaleDerivedCategory X B) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteProEtaleDerivedCategory X A) :=
      DerivedCategory.braidedCategory' _
    letI : BraidedCategory (finiteProEtaleDerivedCategory X B) :=
      DerivedCategory.braidedCategory' _
    FiniteCoefficientSiteEquationLaws
        (finiteEtaleCoefficientExtension X f)
        (finiteProEtaleCoefficientExtension X f)
        (finiteSiteComparisonPullback X A)
        (finiteSiteComparisonPullback X B)
        (finiteCoefficientSiteComparison X f)
        (finiteCoefficientScalarMonoidal X.smallEtaleTopology f)
        (finiteCoefficientScalarMonoidal (Scheme.ProEt.topology X) f)
        (AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
          (ModuleCat.{u + 1} A) X)
        (AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal
          (ModuleCat.{u + 1} B) X)
        (finiteCoefficientSiteComparison_isMonoidal X f)
        (FiniteCoefficientSuccessiveHomLaws X f g) ∧
      FiniteCoefficientSiteTowerEquation X f g := by
  sorry

end WeilConjectures

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Counit-normalized derived scalar mates and geometric composition

Source: blueprint main-20261015, det-thm-sf-ctf-stability-direct-images, paragraph (3);
Stacks Project, Tags 07A6, 0D6D, 0D6E, 0FPI.
(blueprint: lem-sfb-derived-scalar-mate-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.DerivedScalarMate

-- The recorded composition module also imports integral coefficient instances with
-- max-universe conclusions. Pin the already existing instances to this site's sizes.
/-- The existing small-site witness at the module coefficient universe.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
noncomputable instance (priority := 3000) coefficientSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  WeilConjectures.integralOperationsSiteSmall.{u, u} X

/-- Existing abelian sheafification, specialized to coefficient universe u+1.
Source: Stacks 03DA (blueprint: lem-sfb-derived-scalar-mate-composition). -/
noncomputable instance (priority := 3000) coefficientAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

/-- Existing commutative-ring sheafification at the very same site universe.
Source: Stacks 03DA (blueprint: lem-sfb-derived-scalar-mate-composition). -/
noncomputable instance (priority := 3000) coefficientRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} X

/-- Existing locally bijective criterion at the fixed module coefficient universe.
Source: Stacks 03DA (blueprint: lem-sfb-derived-scalar-mate-composition). -/
noncomputable instance (priority := 3000) coefficientLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

/-- Scalar restriction on the original small pro-etale site, using Mathlib's functor.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev restrict {X : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    Scheme.proEtaleRingModules X B ⥤ Scheme.proEtaleRingModules X A :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)

/-- The coefficient identity comparison conjugate to the canonical direct-image identity.
Source: Stacks 00VE (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def ringId {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (Scheme.proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R ≅ R :=
  ((conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).symm).app R

/-- Presentation of the given coefficient map and its normalized scalar adjunctions.
The site and module universes are those of the actual small pro-etale site.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
structure Coefficients (X : Scheme.{u}) where
  [sheafify : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}]
  [locally : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}
  B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}
  φ : A ⟶ B
  [restriction_limits : PreservesFiniteLimits (restrict φ)]
  [restriction_colimits : PreservesFiniteColimits (restrict φ)]
  model : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} φ
  ordinary : model.E ⊣ restrict φ
  derived : model.T ⊣ (restrict φ).mapDerivedCategory
  ordinary_unit : ∀ (M : Scheme.proEtaleRingModules X A) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
    (ordinary.unit.app M).val.app U x =
      (eqToHom (model.obj_eq M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))
  derived_unit : ∀ P : CochainComplex (Scheme.proEtaleRingModules X A) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := A) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := A) (P.X n)) →
    derived.unit.app (DerivedCategory.Q.obj P) ≫
        (restrict φ).mapDerivedCategory.map (model.ε.app P) ≫
        (restrict φ).mapDerivedCategoryFactors.hom.app
          ((model.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).unit.app P)

attribute [instance] Coefficients.restriction_limits Coefficients.restriction_colimits

/-- A geometric arrow with the specified transported coefficient rings.
Source: Stacks 03D8, 0D6D (blueprint: lem-sfb-derived-scalar-mate-composition). -/
structure Edge {X Y : Scheme.{u}} (x : Coefficients X) (y : Coefficients Y) where
  f : X ⟶ Y
  cA : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj y.A ≅ x.A
  cB : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj y.B ≅ x.B
  compatible : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map y.φ ≫
    cB.hom = cA.hom ≫ x.φ

variable {X Y Z : Scheme.{u}} {x : Coefficients X} {y : Coefficients Y}
  {z : Coefficients Z}

/-- The actual exact module inverse image, with A coefficients.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.pA (h : Edge x y) := Scheme.proEtaleRingModulePullback h.f y.A x.A h.cA
/-- The actual exact module inverse image, with B coefficients.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.pB (h : Edge x y) := Scheme.proEtaleRingModulePullback h.f y.B x.B h.cB
/-- The actual module direct image, with A coefficients.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.uA (h : Edge x y) := Scheme.proEtaleRingModuleDirectImage h.f y.A x.A h.cA
/-- The actual module direct image, with B coefficients.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.uB (h : Edge x y) := Scheme.proEtaleRingModuleDirectImage h.f y.B x.B h.cB
/-- The canonical ordinary A-adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.adjA (h : Edge x y) := Scheme.proEtaleRingModuleAdjunction h.f y.A x.A h.cA
/-- The canonical ordinary B-adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.adjB (h : Edge x y) := Scheme.proEtaleRingModuleAdjunction h.f y.B x.B h.cB
/-- The canonical derived A-adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.dA (h : Edge x y) := Scheme.proEtaleRingDerivedAdjunction h.f y.A x.A h.cA
/-- The canonical derived B-adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.dB (h : Edge x y) := Scheme.proEtaleRingDerivedAdjunction h.f y.B x.B h.cB

/-- The restriction/direct-image square is fixed sectionwise, with no chosen automorphism.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: both composites have sections N(X ×_Y U). Their A-actions agree by compatibility
of the coefficient square and naturality of the geometric unit. Identity functions
therefore give linear maps in both directions, commuting with restrictions and maps.
The section formula fixes every component, so the natural isomorphism is unique. -/
theorem Edge.restrictionSquare_existsUnique (h : Edge x y) :
    ∃! γ : h.uB ⋙ restrict y.φ ≅
        restrict x.φ ⋙ h.uA,
      ∀ (N : Scheme.proEtaleRingModules X x.B) (U : Y.ProEtᵒᵖ)
        (n : ((h.uB.obj N).val.obj U)), (γ.hom.app N).val.app U n = n := by
  exact Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm

/-- The unique sectionwise restriction/direct-image identification.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.restrictionSquare (h : Edge x y) :
    h.uB ⋙ restrict y.φ ≅
      restrict x.φ ⋙ h.uA :=
  Classical.choose h.restrictionSquare_existsUnique.exists

/-- The inverse-image/action comparison, obtained from that very sectionwise square.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.action (h : Edge x y) :
    restrict y.φ ⋙ h.pA ⟶
      h.pB ⋙ restrict x.φ :=
  ((mateEquiv h.adjB h.adjA).symm
    (TwoSquare.mk _ _ _ _ h.restrictionSquare.hom)).natTrans

private theorem Edge.restrictionSquare_eq (h : Edge x y) :
    h.restrictionSquare = Scheme.proEtaleRingRestrictionDirectImage
      h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm := by
  apply (h.restrictionSquare_existsUnique).unique
  · exact Classical.choose_spec h.restrictionSquare_existsUnique.exists
  · exact (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
      h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm).choose_spec.1

private theorem Edge.action_eq (h : Edge x y) :
    h.action = Scheme.proEtaleRingRestrictionPullbackInv
      h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm := by
  rw [Edge.action, h.restrictionSquare_eq]
  apply NatTrans.ext
  funext M
  simp only [mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp]
  change h.pA.map ((restrict y.φ).map (h.adjB.unit.app M)) ≫
      h.pA.map (𝟙 _) ≫ h.pA.map
        ((Scheme.proEtaleRingRestrictionDirectImage
          h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm).hom.app (h.pB.obj M)) ≫
      h.pA.map (𝟙 _) ≫ h.adjA.counit.app _ ≫ 𝟙 _ = _
  rw [h.pA.map_id, h.pA.map_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- Inverse image with transported coefficients preserves the restriction action.
Source: Stacks 03D8, 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: forgetting module structures identifies both functors with inverse image of the
same abelian sheaf. The transported actions agree by h.compatible. The sectionwise
identity and its inverse give a natural linear isomorphism. Their transpose is the
sectionwise identity defining restrictionSquare, so adjunction injectivity identifies
its forward map with action. This argument uses no flatness of the coefficient map. -/
theorem Edge.action_isIso (h : Edge x y) : IsIso h.action := by
  rw [h.action_eq]
  exact Scheme.proEtaleRingRestrictionPullbackInv_isIso
    h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm

/-- Exact localization of the canonical action comparison.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.derivedAction (h : Edge x y) :
    (restrict y.φ).mapDerivedCategory ⋙ h.pA.mapDerivedCategory ≅
      h.pB.mapDerivedCategory ⋙ (restrict x.φ).mapDerivedCategory :=
  haveI := h.action_isIso
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso h.action) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

private theorem Edge.derivedAction_eq (h : Edge x y) :
    h.derivedAction = (Scheme.proEtaleRingRestrictionDerivedPullback
      h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm).symm := by
  apply Iso.ext
  simp only [Edge.derivedAction, h.action_eq, Scheme.proEtaleRingRestrictionDerivedPullback,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  rfl

/-- The specified scalar-adjunction mate theta, on the full unbounded derived category.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.theta (h : Edge x y) :
    h.pA.mapDerivedCategory ⋙ x.model.T ⟶ y.model.T ⋙ h.pB.mapDerivedCategory :=
  SheafOfModules.ScalarPullback.mate y.derived x.derived h.derivedAction.hom

/-- The ordinary reverse balancing comparison with the same scalar-unit normalization.
Source: Stacks 03EL, 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.ordinaryTheta (h : Edge x y) : h.pA ⋙ x.model.E ⟶ y.model.E ⋙ h.pB :=
  SheafOfModules.ScalarPullback.mate y.ordinary x.ordinary h.action

private theorem iterated_mate_isIso
    {AY BY AX BX : Type*} [Category AY] [Category BY] [Category AX] [Category BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    {pA : AY ⥤ AX} {uA : AX ⥤ AY} {pB : BY ⥤ BX} {uB : BX ⥤ BY}
    (aY : TY ⊣ rY) (aX : TX ⊣ rX) (gA : pA ⊣ uA) (gB : pB ⊣ uB)
    (s : uB ⋙ rY ≅ rX ⋙ uA) :
    IsIso (SheafOfModules.ScalarPullback.mate aY aX
      (((mateEquiv gB gA).symm (TwoSquare.mk _ _ _ _ s.hom)).natTrans)) := by
  change IsIso (((mateEquiv aY aX).symm
    ((mateEquiv gB gA).symm (TwoSquare.mk _ _ _ _ s.hom))).natTrans)
  rw [iterated_mateEquiv_conjugateEquiv_symm]
  change IsIso ((conjugateEquiv (aY.comp gB) (gA.comp aX)).symm s.hom)
  infer_instance

/-- The ordinary and derived scalar mates are invertible without flat coefficient maps.
Source: Stacks 03EL, 06YY (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: action is the geometric inverse mate of the sectionwise restriction/direct-image
isomorphism. Taking its scalar mate is therefore conjugation under the composite
scalar/geometric adjunctions, by iterated_mateEquiv_conjugateEquiv_symm. Conjugation
preserves isomorphisms. The canonical derived restriction/direct-image comparison
has this same geometric mate, by the derived hom-equivalence compatibility in
proEtaleRingSheafChangeAdjunction. Apply the same double-mate argument to the derived
adjunctions. Neither argument requires flatness of the coefficient map. Note that an
arbitrary single mate need not preserve isomorphisms; it is the iterated mate here
that is conjugation. -/
theorem Edge.scalar_isIso (h : Edge x y) : IsIso h.ordinaryTheta ∧ IsIso h.theta := by
  constructor
  · exact iterated_mate_isIso y.ordinary x.ordinary h.adjA h.adjB h.restrictionSquare
  · let s := Scheme.proEtaleRingRestrictionDerivedDirectImage
      h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm
    have he : h.derivedAction.hom =
        ((mateEquiv h.dB h.dA).symm (TwoSquare.mk _ _ _ _ s.hom)).natTrans := by
      ext M
      apply (h.dA.homEquiv _ _).injective
      have hs := (Scheme.proEtaleRingSheafChangeAdjunction
        h.f y.A y.B x.A x.B y.φ x.φ h.cA h.cB h.compatible.symm).2.2
        M (h.pB.mapDerivedCategory.obj M) (𝟙 _)
      rw [h.derivedAction_eq]
      erw [(Scheme.proEtaleRingRestrictScalars x.φ).mapDerivedCategory.map_id,
        Category.comp_id, Adjunction.homEquiv_id] at hs
      erw [hs, Adjunction.homEquiv_unit]
      exact unit_mateEquiv_symm h.dB h.dA (TwoSquare.mk _ _ _ _ s.hom) M
    change IsIso (SheafOfModules.ScalarPullback.mate y.derived x.derived h.derivedAction.hom)
    rw [he]
    exact iterated_mate_isIso y.derived x.derived h.dA h.dB s

/-- The balanced ordinary tensor/pullback comparison, fixed by the scalar adjunction.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.chi (h : Edge x y) : y.model.E ⋙ h.pB ≅ h.pA ⋙ x.model.E :=
  haveI := h.scalar_isIso.1
  (asIso h.ordinaryTheta).symm

/-- The forward derived comparison; normalization below fixes its balanced representative.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.lambda (h : Edge x y) :
    y.model.T ⋙ h.pB.mapDerivedCategory ≅ h.pA.mapDerivedCategory ⋙ x.model.T :=
  haveI := h.scalar_isIso.2
  (asIso h.theta).symm

/-- The specified counit transpose, without inverting a direct-image scalar map.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.beta (h : Edge x y) :
    (Scheme.proEtaleRingDerivedDirectImage h.f y.A x.A h.cA) ⋙ y.model.T ⟶
      x.model.T ⋙ (Scheme.proEtaleRingDerivedDirectImage h.f y.B x.B h.cB) :=
  (mateEquiv h.dA h.dB (TwoSquare.mk _ _ _ _ h.lambda.hom)).natTrans

/-- The right-derived A-direct image already fixed by the geometric adjunction.
Source: Stacks 07A5 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.rA (h : Edge x y) := Scheme.proEtaleRingDerivedDirectImage h.f y.A x.A h.cA
/-- The right-derived B-direct image already fixed by the geometric adjunction.
Source: Stacks 07A5 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
abbrev Edge.rB (h : Edge x y) := Scheme.proEtaleRingDerivedDirectImage h.f y.B x.B h.cB

/-- The composite coefficient identification respects the pulled-back ring map.
Source: Stacks 03D8, 0D6D (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: expand proEtaleRingCompositeCoefficients. Naturality of inverse-image composition
at z.φ moves it through the ring compositor. Apply f.compatible inside g's inverse image,
then g.compatible. Functoriality gives the displayed equation. -/
theorem Edge.comp_compatible (g : Edge x y) (f : Edge y z) :
    (Scheme.proEtaleSheafInverseImage (g.f ≫ f.f) CommRingCat.{u + 1}).map z.φ ≫
        (Scheme.proEtaleRingCompositeCoefficients g.f f.f z.B y.B x.B f.cB g.cB).hom =
      (Scheme.proEtaleRingCompositeCoefficients g.f f.f z.A y.A x.A f.cA g.cA).hom ≫ x.φ := by
  symm
  simp only [Scheme.proEtaleRingCompositeCoefficients, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← g.compatible, ← Functor.map_comp_assoc, ← f.compatible, Functor.map_comp]
  simp only [Category.assoc, Iso.app_hom]
  rw [← reassoc_of% ((Scheme.proEtaleRingInverseImageComp g.f f.f).hom.naturality z.φ)]

/-- Composition uses the canonical inverse-image ring compositor.
Source: Stacks 03D8, 0D6D (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.comp (g : Edge x y) (f : Edge y z) : Edge x z where
  f := g.f ≫ f.f
  cA := Scheme.proEtaleRingCompositeCoefficients g.f f.f z.A y.A x.A f.cA g.cA
  cB := Scheme.proEtaleRingCompositeCoefficients g.f f.f z.B y.B x.B f.cB g.cB
  compatible := g.comp_compatible f

/-- The specified adjunction-compatible direct-image compositor for A.
Source: Stacks 0D6D, 0D6E (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.kappaA (g : Edge x y) (f : Edge y z) : (g.comp f).rA ≅ g.rA ⋙ f.rA :=
  (conjugateIsoEquiv (f.dA.comp g.dA) (g.comp f).dA
    (WeilConjectures.integralTowerGeneralPullbackComposition g.f f.f z.A y.A x.A f.cA g.cA)).symm

/-- The specified adjunction-compatible direct-image compositor for B.
Source: Stacks 0D6D, 0D6E (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def Edge.kappaB (g : Edge x y) (f : Edge y z) : (g.comp f).rB ≅ g.rB ⋙ f.rB :=
  (conjugateIsoEquiv (f.dB.comp g.dB) (g.comp f).dB
    (WeilConjectures.integralTowerGeneralPullbackComposition g.f f.f z.B y.B x.B f.cB g.cB)).symm

/-- Identity inverse image respects the ring map, by naturality of its canonical comparison.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: ringId is the component of the inverse-image identity natural isomorphism;
apply its naturality to x.φ. -/
theorem identity_compatible (x : Coefficients X) :
    (Scheme.proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).map x.φ ≫
        (ringId x.B).hom =
      (ringId x.A).hom ≫ x.φ := by
  exact (((conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).symm).hom.naturality x.φ)

/-- The geometric identity with the canonical coefficient identity comparisons.
Source: Stacks 03D8 (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def identity (x : Coefficients X) : Edge x x where
  f := 𝟙 X
  cA := ringId x.A
  cB := ringId x.B
  compatible := identity_compatible x

-- The pushforwardCongr₂ construction also used in RingedRestrictionExchangeOpenDescent.
private theorem identityDirect_existsUnique
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    ∃! e : Scheme.proEtaleRingModuleDirectImage (𝟙 X) R R (ringId R) ≅ 𝟭 _,
      ∀ (M : Scheme.proEtaleRingModules X R) (U : X.ProEt)
        (m : M.val.obj (Opposite.op ((Scheme.proEtaleBaseChange (𝟙 X)).obj U))),
        (e.hom.app M).val.app (Opposite.op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m := by
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) := Functor.isContinuous_id _
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X
  let t : A ⟶ ((Scheme.proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).obj A :=
    ⟨Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap (𝟙 X) R R (ringId R)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hc : Scheme.proEtaleRingDirectImageMap (𝟙 X) R R (ringId R) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.app R := by
    exact (unit_conjugateEquiv_symm Adjunction.id
      (Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv R).symm
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [hc]
    ext U r
    change (R.obj.map (e.hom.app U.unop).op ≫ R.obj.map (e.inv.app U.unop).op) r = r
    rw [← R.obj.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
      CategoryTheory.op_id, R.obj.map_id]
    rfl
  let d : Scheme.proEtaleRingModuleDirectImage (𝟙 X) R R (ringId R) ≅ 𝟭 _ :=
    SheafOfModules.pushforwardCongr₂ (φ := t) e.symm ht ≪≫ SheafOfModules.pushforwardId A
  refine ⟨d, fun _ _ _ ↦ rfl, ?_⟩
  intro d' hd'
  apply Iso.ext
  ext M U m
  exact (hd' M U.unop m).trans (show (d.hom.app M).val.app U m = _ from rfl).symm

/-- Identity direct image is uniquely fixed by restriction along U ×_X X → U.
Source: Stacks 03D8, 0D6E (blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: pullbackId is the canonical isomorphism U ×_X X ≅ U. Applying each sheaf's
restriction functor gives inverse linear section maps. The ring action agrees because
ringId is adjoint to this same direct-image identity comparison. These maps are natural
in U and the module. Equality of all section maps proves uniqueness. -/
theorem identity_direct_existsUnique (x : Coefficients X) :
    (∃! e : (identity x).uA ≅ 𝟭 (Scheme.proEtaleRingModules X x.A),
      ∀ (M : Scheme.proEtaleRingModules X x.A) (U : X.ProEt) (m : M.val.obj
        (Opposite.op ((Scheme.proEtaleBaseChange (𝟙 X)).obj U))),
        (e.hom.app M).val.app (Opposite.op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m) ∧
    (∃! e : (identity x).uB ≅ 𝟭 (Scheme.proEtaleRingModules X x.B),
      ∀ (M : Scheme.proEtaleRingModules X x.B) (U : X.ProEt) (m : M.val.obj
        (Opposite.op ((Scheme.proEtaleBaseChange (𝟙 X)).obj U))),
        (e.hom.app M).val.app (Opposite.op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m) := by
  exact ⟨identityDirect_existsUnique x.A, identityDirect_existsUnique x.B⟩

/-- Canonical derived pullback identity for A, descended from the specified adjunction.
Source: Stacks 0D6D (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def identityPullbackA (x : Coefficients X) :
    (identity x).pA.mapDerivedCategory ≅ 𝟭 (DerivedCategory (Scheme.proEtaleRingModules X x.A)) :=
  Functor.mapDerivedCategoryNatIso
    ((conjugateIsoEquiv Adjunction.id (identity x).adjA).symm
      (Classical.choose (identity_direct_existsUnique x).1.exists).symm) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Canonical derived pullback identity for B, descended from the specified adjunction.
Source: Stacks 0D6D (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def identityPullbackB (x : Coefficients X) :
    (identity x).pB.mapDerivedCategory ≅ 𝟭 (DerivedCategory (Scheme.proEtaleRingModules X x.B)) :=
  Functor.mapDerivedCategoryNatIso
    ((conjugateIsoEquiv Adjunction.id (identity x).adjB).symm
      (Classical.choose (identity_direct_existsUnique x).2.exists).symm) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The identity direct-image comparison is conjugate to canonical identity pullback.
Source: Stacks 0D6E (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def identityDirectA (x : Coefficients X) :
    (identity x).rA ≅ 𝟭 (DerivedCategory (Scheme.proEtaleRingModules X x.A)) :=
  conjugateIsoEquiv (identity x).dA Adjunction.id (identityPullbackA x).symm

/-- The identity direct-image comparison is conjugate to canonical identity pullback.
Source: Stacks 0D6E (blueprint: lem-sfb-derived-scalar-mate-composition). -/
def identityDirectB (x : Coefficients X) :
    (identity x).rB ≅ 𝟭 (DerivedCategory (Scheme.proEtaleRingModules X x.B)) :=
  conjugateIsoEquiv (identity x).dB Adjunction.id (identityPullbackB x).symm

/-- Balanced representative normalization and the specified counit-mate characterization.
Source: blueprint det-thm-sf-ctf-stability-direct-images (3); Stacks 03EL, 07A6, 0FPI
(blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: the action square is the sectionwise restriction square of the same inverse
images, so apply lem-sfb-kflat-scalar-comparison-normalization, with the AsSmall site
transport for the distinct pro-etale universes. Its ordinary scalar-unit normalization
identifies chi with the coequalizer balancing comparison. On a flat-term K-flat P it
identifies theta with the inverse of the localized chi after the canonical resolution
counits. Invert this equality to get lambda's representative formula. Finally beta is
mateEquiv applied to lambda, so the geometric counit-transpose identity is the defining
mate equation, using the A-adjunction counit. No beta is inverted. -/
theorem normalization (h : Edge x y) :
    (∀ M : Scheme.proEtaleRingModules Y y.A,
      h.pA.map (y.ordinary.unit.app M) ≫ h.action.app (y.model.E.obj M) ≫
        (restrict x.φ).map (h.chi.hom.app M) =
      x.ordinary.unit.app (h.pA.obj M)) ∧
    (∀ P : CochainComplex (Scheme.proEtaleRingModules Y y.A) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := y.A) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology Y) (R := y.A) (P.X n)) →
      IsIso (x.model.ε.app ((h.pA.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      h.pB.mapDerivedCategory.map (y.model.ε.app P) ≫
          h.pB.mapDerivedCategoryFactors.hom.app
            ((y.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex h.chi (.up ℤ)).hom.app P) =
        h.lambda.hom.app (DerivedCategory.Q.obj P) ≫
          x.model.T.map (h.pA.mapDerivedCategoryFactors.hom.app P) ≫
          x.model.ε.app ((h.pA.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    h.lambda.inv = h.theta ∧
    (∀ K : DerivedCategory (Scheme.proEtaleRingModules X x.A),
      h.pB.mapDerivedCategory.map (h.beta.app K) ≫
          h.dB.counit.app (x.model.T.obj K) =
        h.lambda.hom.app (h.rA.obj K) ≫ x.model.T.map (h.dA.counit.app K)) := by
  sorry

/-- Counit-normalized derived scalar mates respect geometric composition.
Source: blueprint det-thm-sf-ctf-stability-direct-images (3); Stacks 0D6D, 0D6E, 0FPI
(blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: invert theta_composition from lem-sfb-kflat-scalar-comparison-normalization.
Under the canonical pullback and direct-image compositors this says lambda_fg is
lambda_f followed by lambda_g. The canonical composite adjunction's counit is the
g-counit after g-pullback of the f-counit, by lem-sfb-ringed-derived-monoidal-comparisons.
Transpose f's beta followed by f-direct-image of g's beta. Naturality of the f-counit
moves beta_g past that counit; substitute beta_f's defining transpose and beta_g's
transpose. Naturality of lambda_g moves the A f-counit through it. The result is the
composite A-counit after lambda_fg, exactly the transpose defining beta_fg. Injectivity
of the adjunction Hom equivalence proves equality. Reinsert kappaA and kappaB to obtain
the displayed equation. Identity follows from the identity counit and lambda_id = 1. -/
theorem derived_scalar_mate_composition (g : Edge x y) (f : Edge y z) :
    (∀ K : DerivedCategory (Scheme.proEtaleRingModules X x.A),
      (g.comp f).beta.app K ≫ (g.kappaB f).hom.app (x.model.T.obj K) =
        z.model.T.map ((g.kappaA f).hom.app K) ≫
          f.beta.app (g.rA.obj K) ≫ f.rB.map (g.beta.app K)) ∧
    (∀ K : DerivedCategory (Scheme.proEtaleRingModules X x.A),
      (identity x).beta.app K ≫ (identityDirectB x).hom.app (x.model.T.obj K) =
        x.model.T.map ((identityDirectA x).hom.app K)) := by
  sorry

/-- The two paths around every commuting scheme square agree under the normalized
compositors, including the coefficient inverse-image identifications.
Source: blueprint det-thm-sf-ctf-stability-direct-images (3); Stacks 0D6E, 0FPI
(blueprint: lem-sfb-derived-scalar-mate-composition).
Proof: apply derived_scalar_mate_composition to j,q and to p,j'. Each transported
path is beta of the composite. The equality of composites identifies those maps and
both endpoints; cancelling the invertible compositors gives the displayed equality.
The equality of Edge composites expresses jq = pj' together with exactly the canonical
pulled-back coefficient identifications; it imposes no Cartesian or properness condition. -/
theorem commuting_square {W : Scheme.{u}} {w : Coefficients W}
    (j : Edge y z) (q : Edge x y) (p : Edge w z) (j' : Edge x w)
    (comm : q.comp j = j'.comp p) (K : DerivedCategory (Scheme.proEtaleRingModules X x.A)) :
    z.model.T.map ((q.kappaA j).hom.app K) ≫
        j.beta.app (q.rA.obj K) ≫ j.rB.map (q.beta.app K) ≫
        (q.kappaB j).inv.app (x.model.T.obj K) =
      z.model.T.map (eqToHom (congrArg (fun h : Edge x z ↦ h.rA.obj K) comm)) ≫
        z.model.T.map ((j'.kappaA p).hom.app K) ≫
        p.beta.app (j'.rA.obj K) ≫ p.rB.map (j'.beta.app K) ≫
        (j'.kappaB p).inv.app (x.model.T.obj K) ≫
        eqToHom (congrArg (fun h : Edge x z ↦ h.rB.obj (x.model.T.obj K)) comm.symm) := by
  have hq := congrArg (fun t ↦ t ≫ (q.kappaB j).inv.app (x.model.T.obj K))
    ((derived_scalar_mate_composition q j).1 K)
  have hp := congrArg (fun t ↦ t ≫ (j'.kappaB p).inv.app (x.model.T.obj K))
    ((derived_scalar_mate_composition j' p).1 K)
  simp only [Category.assoc, Iso.hom_inv_id_app] at hq hp
  have hq' := (Category.comp_id ((q.comp j).beta.app K)).symm.trans hq
  have hp' := (Category.comp_id ((j'.comp p).beta.app K)).symm.trans hp
  rw [← hq', ← reassoc_of% hp']
  have transport (h₁ h₂ : Edge x z) (e : h₁ = h₂) :
      h₁.beta.app K =
        z.model.T.map (eqToHom (congrArg (fun h : Edge x z ↦ h.rA.obj K) e)) ≫
          h₂.beta.app K ≫
          eqToHom (congrArg (fun h : Edge x z ↦ h.rB.obj (x.model.T.obj K)) e.symm) := by
    cases e
    simp
  exact transport _ _ comm

end AlgebraicGeometry.DerivedScalarMate

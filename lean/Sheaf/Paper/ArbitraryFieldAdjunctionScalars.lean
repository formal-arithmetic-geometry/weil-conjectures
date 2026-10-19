/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.RationalDirectImageRealization
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Paper.RingedComparisonTensorAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Scalar compatibility of the ordinary adjunction over an arbitrary field

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
the normalized scalar mate calculation
(blueprint: lem-per-arbitrary-field-adjunction-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational.DirectImage
namespace ScalarAdjunction

section HomEquations
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ uR
variable {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₁} [Category.{v₁} D₀]
  {C₁ : Type u₂} [Category.{v₂} C₁] {D₁ : Type u₃} [Category.{v₃} D₁]
  {P₀ : C₀ ⥤ D₀} {D₀' : D₀ ⥤ C₀} {P₁ : C₁ ⥤ D₁} {D₁' : D₁ ⥤ C₁}
  {T_X : D₀ ⥤ D₁} {T_Y : C₀ ⥤ C₁}

/-- The three displayed equations, expressed once for the four actual categories
and then specialized below to the given raw functors and their normalized stages.
Source: BS 6.8.15; scalar mate calculation
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure HomEquations (h₀ : P₀ ⊣ D₀') (h₁ : P₁ ⊣ D₁')
    (a : T_Y ⋙ P₁ ≅ P₀ ⋙ T_X) (b : D₀' ⋙ T_Y ≅ T_X ⋙ D₁') : Prop where
  mate : ∀ B, (h₁.homEquiv _ _).symm (b.hom.app B) =
    a.hom.app (D₀'.obj B) ≫ T_X.map (h₀.counit.app B)
  forward : ∀ A B (w : P₀.obj A ⟶ B),
    h₁.homEquiv _ _ (a.hom.app A ≫ T_X.map w) =
      T_Y.map (h₀.homEquiv A B w) ≫ b.hom.app B
  inverse : ∀ A B (v : A ⟶ D₀'.obj B),
    (h₁.homEquiv _ _).symm (T_Y.map v ≫ b.hom.app B) =
      a.hom.app A ≫ T_X.map ((h₀.homEquiv A B).symm v)

/-- Additivity and scalar linearity in both directions of the specified Hom
bijection, later specialized to each actual raw category.
Source: BS 6.8.14(2), 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure LinearHomEquations (R : Type uR) [CommRing R]
    [Preadditive C₀] [Preadditive D₀] [Linear R C₀] [Linear R D₀]
    (h : P₀ ⊣ D₀') : Prop where
  forward_add : ∀ A B (w w' : P₀.obj A ⟶ B),
    h.homEquiv A B (w + w') = h.homEquiv A B w + h.homEquiv A B w'
  inverse_add : ∀ A B (v v' : A ⟶ D₀'.obj B),
    (h.homEquiv A B).symm (v + v') =
      (h.homEquiv A B).symm v + (h.homEquiv A B).symm v'
  forward : ∀ A B (w : P₀.obj A ⟶ B) (s : R),
    h.homEquiv A B (s • w) = s • h.homEquiv A B w
  inverse : ∀ A B (v : A ⟶ D₀'.obj B) (s : R),
    (h.homEquiv A B).symm (s • v) = s • (h.homEquiv A B).symm v

end HomEquations

section General
variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (r : Family.{u} l)
  {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
  (dE : Comparison l E f (r.realization E X) (r.realization E Y) (r.along E f))
  (dF : Comparison l F f (r.realization F X) (r.realization F Y) (r.along F f))

/-- Restriction/direct-image comparison, constructed as the conjugate of the specified
balanced tensor comparison for the two factorizations of the coefficient square.
Source: BS 6.8.15; ringed-topos composition comparison
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
@[irreducible] def restrictionComparison :
    derivedPush f (r.along F f).coefficient ⋙
        pbcDerivedRestrict (r.fieldChange E F i Y).coefficient ≅
      pbcDerivedRestrict (r.fieldChange E F i X).coefficient ⋙
        derivedPush f (r.along E f).coefficient :=
  conjugateIsoEquiv
    ((pbcDerivedScalarAdjunction (r.fieldChange E F i Y).coefficient).comp
      dF.ordinary.adjunction)
    (dE.ordinary.adjunction.comp
      (pbcDerivedScalarAdjunction (r.fieldChange E F i X).coefficient))
    (r.mixed E F i f).ambient.symm

/-- The same composition comparison before deriving; the tensor and geometric
adjunctions are the published ones, normalized on sections by insertion of one.
Source: BS 6.8.15; ringed-topos composition comparison
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
@[irreducible] def moduleRestrictionComparison :
    modulePush f (r.along F f).coefficient ⋙
        pbcRestrict (r.fieldChange E F i Y).coefficient ≅
      pbcRestrict (r.fieldChange E F i X).coefficient ⋙
        modulePush f (r.along E f).coefficient :=
  conjugateIsoEquiv
    ((pbcScalarAdjunction (r.fieldChange E F i Y).coefficient).comp
      dF.ordinary.moduleAdjunction)
    (dE.ordinary.moduleAdjunction.comp
      (pbcScalarAdjunction (r.fieldChange E F i X).coefficient))
    (r.mixed E F i f).ordinary.symm

/-- All three raw equations and the ambient normalizations, for the specified
coefficient comparisons. The first field identifies the constructed restriction
comparison with the right-derived composition comparison by its universal units.
Source: BS 6.7.2, 6.8.14(2), 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure Equations (b : FieldChange l E F i f r dE dF) : Prop where
  restriction_normalization : ∀ I : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme F)) ℤ,
    (pbcDerivedRestrict (r.fieldChange E F i Y).coefficient).map
        (pushUnit f (r.along F f).coefficient I) ≫
        (restrictionComparison l E F i r f dE dF).hom.app (DerivedCategory.Q.obj I) =
      (pbcRestrict (r.fieldChange E F i Y).coefficient).mapDerivedCategoryFactors.hom.app
          (((modulePush f (r.along F f).coefficient).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (moduleRestrictionComparison l E F i r f dE dF) (.up ℤ)).hom.app I) ≫
        pushUnit f (r.along E f).coefficient
          (((pbcRestrict (r.fieldChange E F i X).coefficient).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
        (derivedPush f (r.along E f).coefficient).map
          ((pbcRestrict (r.fieldChange E F i X).coefficient).mapDerivedCategoryFactors.inv.app I)
  coefficient_transpose : ∀ K,
    (pbcDerivedScalarAdjunction (r.fieldChange E F i Y).coefficient).homEquiv _ _
        (b.ambient.hom.app K) =
      (derivedPush f (r.along E f).coefficient).map
          ((pbcDerivedScalarAdjunction (r.fieldChange E F i X).coefficient).unit.app K) ≫
        (restrictionComparison l E F i r f dE dF).inv.app
          ((pbcDerivedExtend (r.fieldChange E F i X).coefficient).obj K)
  ambient_mate : ∀ K,
    (dF.ordinary.adjunction.homEquiv _ _).symm (b.ambient.hom.app K) =
      (r.mixed E F i f).ambient.hom.app
          ((derivedPush f (r.along E f).coefficient).obj K) ≫
        (pbcDerivedExtend (r.fieldChange E F i X).coefficient).map
          (dE.ordinary.adjunction.counit.app K)
  raw : HomEquations dE.rawAdjunction dF.rawAdjunction
    (r.mixed E F i f).raw b.raw

/-- Linearity of both directions of the given raw adjunction, on the actual field
module structures on raw Hom spaces. Source: BS 6.8.14(2), 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
abbrev Linearity : Prop := LinearHomEquations E dE.rawAdjunction

/-- Shift comparisons with their resolution and realization normalizations.
Compatibility of the adjunction units and counits expresses that both directions
of each Hom bijection commute with cochain shifts. Source: BS 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure ShiftCompatibility (b : FieldChange l E F i f r dE dF) where
  [rawPullE : ((r.along E f).raw l E).CommShift ℤ]
  [rawPushE : (rawPush l E f dE.preserves).CommShift ℤ]
  [rawPullF : ((r.along F f).raw l F).CommShift ℤ]
  [rawPushF : (rawPush l F f dF.preserves).CommShift ℤ]
  [ambientPullE : (derivedPull f (r.along E f).coefficient).CommShift ℤ]
  [ambientPushE : (derivedPush f (r.along E f).coefficient).CommShift ℤ]
  [ambientPullF : (derivedPull f (r.along F f).coefficient).CommShift ℤ]
  [ambientPushF : (derivedPush f (r.along F f).coefficient).CommShift ℤ]
  [tensorX : (pbcDerivedExtend (r.fieldChange E F i X).coefficient).CommShift ℤ]
  [tensorY : (pbcDerivedExtend (r.fieldChange E F i Y).coefficient).CommShift ℤ]
  pull_resolution_E : NatTrans.CommShift (r.along E f).counit ℤ
  push_resolution_E : NatTrans.CommShift
    (modulePush f (r.along E f).coefficient).rightDerivedFunctorUnit ℤ
  pull_resolution_F : NatTrans.CommShift (r.along F f).counit ℤ
  push_resolution_F : NatTrans.CommShift
    (modulePush f (r.along F f).coefficient).rightDerivedFunctorUnit ℤ
  tensor_resolution_X : NatTrans.CommShift
    (pbcExtensionCounit (r.fieldChange E F i X).coefficient) ℤ
  tensor_resolution_Y : NatTrans.CommShift
    (pbcExtensionCounit (r.fieldChange E F i Y).coefficient) ℤ
  pull_realization_E :
    (fun [_q : (rawPull l E f (r.along E f).integral_mem).CommShift ℤ] ↦
      NatTrans.CommShift (r.along E f).comparison.hom ℤ) (_q := rawPullE)
  push_realization_E : NatTrans.CommShift dE.comparison.hom ℤ
  pull_realization_F :
    (fun [_q : (rawPull l F f (r.along F f).integral_mem).CommShift ℤ] ↦
      NatTrans.CommShift (r.along F f).comparison.hom ℤ) (_q := rawPullF)
  push_realization_F : NatTrans.CommShift dF.comparison.hom ℤ
  scalar_realization_X : NatTrans.CommShift (r.fieldChange E F i X).comparison.hom ℤ
  scalar_realization_Y : NatTrans.CommShift (r.fieldChange E F i Y).comparison.hom ℤ
  raw_adjunction_E : dE.rawAdjunction.CommShift ℤ
  ambient_adjunction_E : dE.ordinary.adjunction.CommShift ℤ
  raw_adjunction_F : dF.rawAdjunction.CommShift ℤ
  ambient_adjunction_F : dF.ordinary.adjunction.CommShift ℤ
  raw_pull : NatTrans.CommShift (r.mixed E F i f).raw.hom ℤ
  raw_push : NatTrans.CommShift b.raw.hom ℤ
  ambient_pull : NatTrans.CommShift (r.mixed E F i f).ambient.hom ℤ
  ambient_push : NatTrans.CommShift b.ambient.hom ℤ

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)
  (dG : Comparison l G f (r.realization G X) (r.realization G Y) (r.along G f))

/-- The specified pullback comparisons paste under the specified raw and ambient
tensor associators. The companion direct-image equations are exactly
`DirectImage.FieldComposition`. Repeated fields are allowed.
Source: BS 6.8.15; scalar-extension associators
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure Tower (bEF : FieldChange l E F i f r dE dF)
    (bFG : FieldChange l F G j f r dF dG)
    (bEG : FieldChange l E G (j.comp i) f r dE dG) : Prop where
  raw_pull : ∀ A,
    (r.mixed F G j f).raw.hom.app
        ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj A) ≫
        (pbcRationalScalarExtension l F G j X.scheme X.dimension X.prime_unit).map
          ((r.mixed E F i f).raw.hom.app A) ≫
        (pbcRationalScalarCompComponent l E F G i j X.scheme X.dimension X.prime_unit
          (((r.along E f).raw l E).obj A)).hom =
      ((r.along G f).raw l G).map
          (pbcRationalScalarCompComponent l E F G i j Y.scheme Y.dimension Y.prime_unit A).hom ≫
        (r.mixed E G (j.comp i) f).raw.hom.app A
  ambient_pull : ∀ A,
    (r.mixed F G j f).ambient.hom.app
        ((pbcDerivedExtend (r.fieldChange E F i Y).coefficient).obj A) ≫
        (pbcDerivedExtend (r.fieldChange F G j X).coefficient).map
          ((r.mixed E F i f).ambient.hom.app A) ≫
        (pbcReductionNormalization (r.fieldChange E F i X).coefficient
          (r.fieldChange F G j X).coefficient (r.fieldChange E G (j.comp i) X).coefficient
          (r.fieldComposition E F G i j X).coefficient
          ((derivedPull f (r.along E f).coefficient).obj A)).hom =
      (derivedPull f (r.along G f).coefficient).map
          (pbcReductionNormalization (r.fieldChange E F i Y).coefficient
            (r.fieldChange F G j Y).coefficient (r.fieldChange E G (j.comp i) Y).coefficient
            (r.fieldComposition E F G i j Y).coefficient A).hom ≫
        (r.mixed E G (j.comp i) f).ambient.hom.app A
  direct_image : FieldComposition l E F G i j f r dE dF dG bEF bFG bEG

/-- Identity coefficient comparisons, after the published tensor unitors.
Conjugating by stage normalization gives literally identity transitions and maps.
Source: BS 6.8.15; scalar-extension unit normalization
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure IdentityExtension
    (b : FieldChange l E E (AlgHom.id ℚ_[l] E) f r dE dE) where
  raw_pull : ∀ A,
    (r.mixed E E (AlgHom.id ℚ_[l] E) f).raw.hom.app A ≫
        (pbcRationalScalarUnit l E X.scheme X.dimension X.prime_unit).hom.app
          (((r.along E f).raw l E).obj A) =
      ((r.along E f).raw l E).map
        ((pbcRationalScalarUnit l E Y.scheme Y.dimension Y.prime_unit).hom.app A)
  raw_push : ∀ B,
    b.raw.hom.app B ≫
        (rawPush l E f dE.preserves).map
          ((pbcRationalScalarUnit l E X.scheme X.dimension X.prime_unit).hom.app B) =
      (pbcRationalScalarUnit l E Y.scheme Y.dimension Y.prime_unit).hom.app
        ((rawPush l E f dE.preserves).obj B)
  ordinaryX : pbcExtend (r.fieldChange E E (AlgHom.id ℚ_[l] E) X).coefficient ≅ 𝟭 _
  ordinaryY : pbcExtend (r.fieldChange E E (AlgHom.id ℚ_[l] E) Y).coefficient ≅ 𝟭 _
  ordinaryX_sections : ∀ (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
      (U : X.scheme.ProEtᵒᵖ)
      (a : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (m : M.val.obj U),
    (ordinaryX.hom.app M).val.app U
        (pbcTensorSection (r.fieldChange E E (AlgHom.id ℚ_[l] E) X).coefficient M U a m) = a • m
  ordinaryY_sections : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEtᵒᵖ)
      (a : (rationalCoefficientSheaf l Y.scheme E).obj.obj U) (m : M.val.obj U),
    (ordinaryY.hom.app M).val.app U
        (pbcTensorSection (r.fieldChange E E (AlgHom.id ℚ_[l] E) Y).coefficient M U a m) = a • m
  ambientX : pbcDerivedExtend (r.fieldChange E E (AlgHom.id ℚ_[l] E) X).coefficient ≅ 𝟭 _
  ambientY : pbcDerivedExtend (r.fieldChange E E (AlgHom.id ℚ_[l] E) Y).coefficient ≅ 𝟭 _
  ambientX_normalization : ∀ P : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) ℤ,
    pbcComplexCounit (r.fieldChange E E (AlgHom.id ℚ_[l] E) X).coefficient P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinaryX (.up ℤ)).hom.app P) =
      ambientX.hom.app (DerivedCategory.Q.obj P)
  ambientY_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    pbcComplexCounit (r.fieldChange E E (AlgHom.id ℚ_[l] E) Y).coefficient P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinaryY (.up ℤ)).hom.app P) =
      ambientY.hom.app (DerivedCategory.Q.obj P)
  ambient_pull : ∀ A,
    (r.mixed E E (AlgHom.id ℚ_[l] E) f).ambient.hom.app A ≫
        ambientX.hom.app ((derivedPull f (r.along E f).coefficient).obj A) =
      (derivedPull f (r.along E f).coefficient).map (ambientY.hom.app A)
  ambient_push : ∀ B,
    b.ambient.hom.app B ≫
        (derivedPush f (r.along E f).coefficient).map (ambientX.hom.app B) =
      ambientY.hom.app ((derivedPush f (r.along E f).coefficient).obj B)

end General

section Stages
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
  (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
  (r : Family.{u} l) {X Y : Base.{u} l} (f : X.scheme ⟶ Y.scheme)
  (dE : Comparison l E.val f (r.realization E.val X) (r.realization E.val Y)
    (r.along E.val f))
  (dF : Comparison l F.val f (r.realization F.val X) (r.realization F.val Y)
    (r.along F.val f))

/-- The specified inverse pullback comparison with the literal identity transition
normalization of the scalar-extension proposition. Source: BS 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
@[irreducible] def stagePullComparison :
    pbcStageTransition l Ω Y.scheme h ⋙ (r.along F.val f).raw l F.val ≅
      (r.along E.val f).raw l E.val ⋙ pbcStageTransition l Ω X.scheme h :=
  Functor.isoWhiskerRight (pbcStageNormalization l Ω Y.scheme h).symm _ ≪≫
    (r.mixed E.val F.val (pbcSubfieldInclusion l Ω h) f).raw ≪≫
      Functor.isoWhiskerLeft _ (pbcStageNormalization l Ω X.scheme h)

/-- The specified direct-image comparison, with the same literal identity
normalization. Source: BS 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
@[irreducible] def stagePushComparison
    (b : FieldChange l E.val F.val (pbcSubfieldInclusion l Ω h) f r dE dF) :
    rawPush l E.val f dE.preserves ⋙ pbcStageTransition l Ω Y.scheme h ≅
      pbcStageTransition l Ω X.scheme h ⋙ rawPush l F.val f dF.preserves :=
  Functor.isoWhiskerLeft _ (pbcStageNormalization l Ω Y.scheme h).symm ≪≫ b.raw ≪≫
    Functor.isoWhiskerRight (pbcStageNormalization l Ω X.scheme h) _

/-- The displayed equations on the proposition's normalized stage transitions.
Thus T for a repeated field is literally identity, with no change of raw category.
Source: BS 6.7.2, 6.8.14(2), 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
abbrev StageEquations
    (b : FieldChange l E.val F.val (pbcSubfieldInclusion l Ω h) f r dE dF) : Prop :=
  HomEquations dE.rawAdjunction dF.rawAdjunction
    (stagePullComparison l Ω E F h r f) (stagePushComparison l Ω E F h r f dE dF b)

end Stages

/-- The clauses of scalar/adjunction compatibility for all separated finite-type
morphisms over the given field, for finite intermediate fields in the chosen
algebraic closure and their actual inclusions.
All comparisons are taken from the input normalized realization packages.
Source: BS 6.7.2, 6.8.14(2), 6.8.15
(blueprint: lem-per-arbitrary-field-adjunction-scalars). -/
structure Compatibility (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (r : Family.{u} l) (p : DirectImage.Package k l r) : Prop where
  equations : ∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    Equations l E.val F.val (pbcSubfieldInclusion l Ω h) r f
      (p.along E.val f) (p.along F.val f)
      (p.fieldChange E.val F.val (pbcSubfieldInclusion l Ω h) f)
  stage_equations : ∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    StageEquations l Ω E F h r f (p.along E.val f) (p.along F.val f)
      (p.fieldChange E.val F.val (pbcSubfieldInclusion l Ω h) f)
  linearity : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    Linearity l E.val r f (p.along E.val f)
  shifts : ∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    Nonempty (ShiftCompatibility l E.val F.val (pbcSubfieldInclusion l Ω h) r f
      (p.along E.val f) (p.along F.val f)
      (p.fieldChange E.val F.val (pbcSubfieldInclusion l Ω h) f))
  tower : ∀ (E F G : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F) (h' : F ≤ G)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    Tower l E.val F.val (pbcSubfieldInclusion l Ω h) r f (p.along E.val f)
      (p.along F.val f) G.val (pbcSubfieldInclusion l Ω h') (p.along G.val f)
      (p.fieldChange E.val F.val (pbcSubfieldInclusion l Ω h) f)
      (p.fieldChange F.val G.val (pbcSubfieldInclusion l Ω h') f)
      (p.fieldChange E.val G.val
        ((pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h)) f)
  identity : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    {X Y : Space.{u} k l} (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    Nonempty (IdentityExtension l E.val r f (p.along E.val f)
      (p.fieldChange E.val E.val (AlgHom.id ℚ_[l] E.val) f))

/-- The specified scalar comparisons are mates for the canonical raw adjunctions,
with the same normalization in all continuous ambient modules, linearity, shifts,
and identity and successive coefficient extensions.

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
agent-derived scalar mate calculation
(blueprint: lem-per-arbitrary-field-adjunction-scalars).

Proof plan:
1. Finite-type schemes over k are noetherian and finite-dimensional, and the
invertibility of l in k supplies their coefficient hypotheses. Use
lem-weil-pbc-finite-type-over-noetherian and lem-kun-dimension-finite-type.
2. Use lem-per-continuous-rational-derived-realization and
lem-a1-rational-direct-image-realization to identify the actual integral operations,
raw scalar localizations, adjunction units and counits with the ordinary ambient
continuous-module derived operations. The raw category has no Karoubi envelope.
3. Use lem-pur-sheaf-ring-derived-coefficient-adjunction for tensor extension left
adjoint to exact restriction, with unit x ↦ x tensor 1. The two factorizations of
the same coefficient square give the restriction comparison d by
lem-weil-pbc-ringed-topoi-derived-pushforward-composition. Its universal-unit equation
is restriction_normalization; the same square before deriving is
moduleRestrictionComparison. The comparison b is the coefficient transpose through d inverse.
4. Apply lem-sfb-ringed-comparison-tensor-adjunction to these two factorizations.
The left comparison is the inverse balanced tensor comparison a, and its conjugate
is d inverse. For Z = T_X K, transpose D_E(eta_X) followed by d inverse under the
composite adjunctions (def-weil-pbc-composite-adjunction). Naturality of the geometric
counit and of the balanced comparison moves eta_X past them; the coefficient
triangle identity cancels T_X(eta_X) against its coefficient counit. The remaining
map is a inverse at D_E K followed by T_X(epsilon_E). This proves the ambient mate
identity and identifies the constructed conjugate d with the universal composition
comparison, without an assertion that direct image preserves K-injectives.
5. The two realization comparisons carry precisely a and b to their ambient
counterparts: use the finite-extension clauses of the two realization nodes and
prop-weil-pbc-scalar-extension. They carry the actual counits as well. Faithfulness
of J therefore reflects the ambient mate identity to the raw mate equation on every raw object.
6. For w : P_E A → B, use naturality of a and the adjunction Hom equivalence to
obtain forward from the raw mate equation. The geometric adjunction triangle identity cancels
the inserted unit and counit.
7. Apply the inverse Hom bijection to forward, then use its inverse identities,
to obtain inverse for every v : A → D_E B.
8. Direct image is coefficient-linear by prop-weil-pbc-rational-transport. The
formula h(w) = eta followed by D(w) is linear, and the inverse of a bijective
linear map is linear. The canonical operation shifts come from shifted K-flat
and K-injective resolutions (lem-cbc-completed-pullback-triangles and
lem-pc-right-derived-functor-triangulated). Use lem-weil-pbc-derived-adjunction-shift
for the ambient unit/counit equations, then the exact realization and its actual
unit/counit identifications for the raw equations. The universal comparison
units/counits specify these shift structures; the scalar proposition gives
shift compatibility of the comparisons and associators.
9. The tensor unit maps multiply by one, so after their normalization the identity
extension has identity scalar transitions and comparisons. For E → F → G use the
specified scalar associators of prop-weil-pbc-scalar-extension. Paste the two
forward identities and use naturality of the associators; the resulting equation
is the direct one for the composite embedding. The inverse and counit equations
follow by their Hom bijections. Lem-weil-pbc-mate-pasting(1) identifies the
composite mate with the pasted mates. The same holds ambiently by the two
realization comparisons and ringed-topos composition. The scalar pentagon makes
longer towers independent of parenthesization. -/
theorem arbitrary_field_adjunction_scalars (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (r : Family.{u} l) (p : DirectImage.Package k l r) :
    Compatibility k l Ω r p := by
  sorry

end ScalarAdjunction
end AlgebraicGeometry.Scheme.ContinuousRational.DirectImage

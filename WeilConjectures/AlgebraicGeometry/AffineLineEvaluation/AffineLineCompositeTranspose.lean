/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Compactification.NagataCompactification

/-! # Affine-line evaluation and the composite exceptional transpose

Source: main-20261015, sec-smooth-purity/sk-prop-an, Integration paragraph
(blueprint: lem-pur-affine-line-composite-transpose).

The affine-space comparison module supplies the literal one-line source and inverse
exceptional compositor. Here the counit is the normalized tensor-integration composite.
All transposes use bounded-below etale-origin inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineLineEvaluation
open AffineLinePurity VectorIntegrationSite AffineSpacePurity

private def projectionNatural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)) :
    (derivedTensor V Y).flip.obj
        ((rightDerivedLowerShriekOfCompactification V c).obj F) ⟶
      (upperStar V f).leftDerivedFunctor ⋙ (derivedTensor V X).flip.obj F ⋙
        rightDerivedLowerShriekOfCompactification V c :=
  (symmetry V Y).hom.flipApp _ ≫
    (projectionMapOfCompactification V c).app F ≫
      Functor.whiskerLeft (upperStar V f).leftDerivedFunctor
        (Functor.whiskerRight ((symmetry V X).hom.app F)
          (rightDerivedLowerShriekOfCompactification V c))

private theorem projection_natural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)} (h : K ⟶ L) :
    ((derivedTensor V Y).map h).app
        ((rightDerivedLowerShriekOfCompactification V c).obj F) ≫ projection V c F L =
      projection V c F K ≫ (rightDerivedLowerShriekOfCompactification V c).map
        (((derivedTensor V X).map ((upperStar V f).leftDerivedFunctor.map h)).app F) := by
  have he (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)) :
      (projectionNatural V c F).app Z = projection V c F Z := by
    unfold projectionNatural projection
    rfl
  have hn := (projectionNatural V c F).naturality h
  rw [he, he] at hn
  exact hn

private theorem coefficientRightUnit_natural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u})
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)} (h : K ⟶ L) :
    ((derivedTensor V Y).map h).app _ ≫ (coefficientRightUnit V Y L).hom =
      (coefficientRightUnit V Y K).hom ≫ h := by
  have hn := ((derivedTensor V Y).map h).naturality (coefficientUnitIso V Y).hom
  unfold coefficientRightUnit
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hn, Category.assoc]
  simpa only [derivedTensor, curriedTensor, Category.assoc] using
    congrArg (fun z ↦ ((derivedTensor V Y).obj K).map (coefficientUnitIso V Y).hom ≫ z)
      (rightUnitor_naturality h)

set_option allowUnsafeReducibility true in
attribute [local reducible] projectionSourceObject projectionTargetObject lineSource

private theorem projectionTensorTrace_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L)
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj F ⟶
      unit A Y)
    (hK : ProjectionInvertible A c F K) (hL : ProjectionInvertible A c F L) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map h)).app F) ≫
      projectionTensorTrace A c F L t hL = projectionTensorTrace A c F K t hK ≫ h := by
  let Q := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let T := derivedTensor (ModuleCat.{u + 1} A) Y
  let a := ((derivedTensor (ModuleCat.{u + 1} A) X).map
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map h)).app F
  let b := (T.map h).app (Q.obj F)
  have hp := projection_natural (ModuleCat.{u + 1} A) c F h
  unfold ProjectionInvertible at hK hL
  let := hK
  let := hL
  have hi : Q.map a ≫ inv (projection (ModuleCat.{u + 1} A) c F L) =
      inv (projection (ModuleCat.{u + 1} A) c F K) ≫ b := by
    symm
    apply (IsIso.inv_comp_eq (projection (ModuleCat.{u + 1} A) c F K)).2
    change b = projection (ModuleCat.{u + 1} A) c F K ≫ Q.map a ≫
      inv (projection (ModuleCat.{u + 1} A) c F L)
    rw [← Category.assoc, ← hp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  unfold projectionTensorTrace inverseProjection
  dsimp only [Iso.symm_hom, asIso_inv]
  change Q.map a ≫ (inv (projection (ModuleCat.{u + 1} A) c F L) ≫
    (T.obj L).map t ≫ (moduleRightUnit A Y L).hom) =
      (inv (projection (ModuleCat.{u + 1} A) c F K) ≫
        (T.obj K).map t ≫ (moduleRightUnit A Y K).hom) ≫ h
  rw [← Category.assoc, hi]
  simp only [Category.assoc]
  have ht := ((T.map h).naturality t).symm
  change b ≫ (T.obj L).map t = (T.obj K).map t ≫ (T.map h).app _ at ht
  rw [reassoc_of% ht]
  unfold moduleRightUnit
  have hr := coefficientRightUnit_natural (ModuleCat.{u + 1} A) Y h
  exact congrArg (fun z ↦ inv (projection (ModuleCat.{u + 1} A) c F K) ≫
    (T.obj K).map t ≫ z) hr

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Canonical change of compactification evaluated using the retained etale origin.
Source: compactification coherence in the Integration paragraph
(blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def changeSupport (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (M : Plus A X) (W : Scheme.FixedEtaleOriginWitness X A M) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj M.obj :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso W.iso.symm ≪≫
    (fixedCompactSupportOriginIso A c d).app W.complex ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso W.iso

/-- The actual tensor-integration evaluation b, in its specified chart compactification.
Source: b_{u,H} display (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def evaluation (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (H : D P B) (He : Etale.DerivedCategoryModule (Ring P) B)
    (hHe : etaleFiniteTor (Ring P) B He) (eH : (comparison (Ring P) B).obj He ≅ H) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification B)).obj ((lineSource P B).obj H) ⟶ H :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
    (affineTraceLineCompactification B)).map (eqToHom (lineSource_obj_eq P B H)) ≫
      augmentation P.coefficients.l P.extension (P.level - 1) B P.level (annihilates P)
        (primeUnit P B aB) P.field.k aB H He hHe eH

/-- Naturality of the specified evaluation for every map between finite-Tor inputs.
Source: Integration paragraph (blueprint: lem-pur-affine-line-composite-transpose).
Proof: Step 2 of the node applies naturality of the canonical projection map, inverts
it, and inserts the two tensor symmetries. Tensor bifunctoriality commutes the map h
past 1 tensor integration. Naturality of the right unitor completes the equality.
The chosen etale representatives only certify projection invertibility. -/
theorem evaluation_naturality (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (H H' : D P B) (He He' : Etale.DerivedCategoryModule (Ring P) B)
    (hHe : etaleFiniteTor (Ring P) B He) (hHe' : etaleFiniteTor (Ring P) B He')
    (eH : (comparison (Ring P) B).obj He ≅ H)
    (eH' : (comparison (Ring P) B).obj He' ≅ H') (h : H ⟶ H') :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification B)).map ((lineSource P B).map h) ≫
        evaluation P B aB H' He' hHe' eH' = evaluation P B aB H He hHe eH ≫ h := by
  let : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  have hn := projectionTensorTrace_natural (Ring P) (affineTraceLineCompactification B)
    (coefficient P.coefficients.l P.extension (P.level - 1) B P.level (annihilates P)) h
    (integration P.coefficients.l P.extension (P.level - 1) B P.level
      (annihilates P) (primeUnit P B aB))
    (projection_isIso P.coefficients.l P.extension (P.level - 1) B P.level
      (annihilates P) P.field.k aB (primeUnit P B aB) H He hHe eH)
    (projection_isIso P.coefficients.l P.extension (P.level - 1) B P.level
      (annihilates P) P.field.k aB (primeUnit P B aB) H' He' hHe' eH')
  have heq (J : D P B) : eqToHom (lineSource_obj_eq P B J) = 𝟙 _ := by
    rfl
  have hev (J : D P B) (Je : Etale.DerivedCategoryModule (Ring P) B)
      (hj : etaleFiniteTor (Ring P) B Je) (ej : (comparison (Ring P) B).obj Je ≅ J) :
      evaluation P B aB J Je hj ej =
        augmentation P.coefficients.l P.extension (P.level - 1) B P.level
          (annihilates P) (primeUnit P B aB) P.field.k aB J Je hj ej := by
    unfold evaluation
    rw [heq]
    have hid := (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Ring P)) (affineTraceLineCompactification B)).map_id
      ((lineSource P B).obj J)
    rw [hid, Category.id_comp]
  rw [hev, hev]
  simpa only [augmentation, lineSource, AffineSpacePurity.tensor, inverseImage,
    Functor.comp_map, Functor.flip_obj_map] using hn

/-- The canonical left unitor with the compared coefficient unit, at general coefficients.
Source: tensor-unit identifications (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def comparedLeftUnit (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    ((derivedTensor B T).obj ((comparisonUpperStar B T).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B))))).obj K ≅ K :=
  ((derivedTensor B T).mapIso (coefficientUnitIso B T)).app K ≪≫ leftUnitor K

/-- The tensor-unit source identification, cached before coefficient specialization.
Source: canonical tensor-unit identifications
(blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def unitTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {T B : Scheme.{u}} (f : T ⟶ B) (F : C A T) :
    projectionSourceObject A f F (unit A B) ≅ F := by
  unfold projectionSourceObject
  exact ((derivedTensor (ModuleCat.{u + 1} A) T).mapIso (pullbackUnit A f)).app F ≪≫
    comparedLeftUnit (ModuleCat.{u + 1} A) T F

/-- The canonical tensor-unit identification F_u(A_B) = A_L(1)[2].
Source: tensor-unit identifications in the Integration paragraph
(blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def unitSource (B : Scheme.{u}) :
    (lineSource P B).obj (unit (Ring P) B) ≅
      coefficient P.coefficients.l P.extension (P.level - 1) B P.level (annihilates P) :=
  eqToIso (lineSource_obj_eq P B (unit (Ring P) B)) ≪≫
    unitTensor (Ring P) (AffineSpace PUnit.{u + 1} B ↘ B)
      (coefficient P.coefficients.l P.extension (P.level - 1) B P.level (annihilates P))

/-- Normalized integration with the derived Noetherian witness inserted internally.
Source: t_B in the Integration paragraph
(blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def trace (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  integration P.coefficients.l P.extension (P.level - 1) B P.level (annihilates P)
    (primeUnit P B aB)

/-- At constants the evaluation is exactly normalized affine-line integration.
Source: Integration paragraph (blueprint: lem-pur-affine-line-composite-transpose).
Proof: Step 3 unfolds the actual proper and open projection maps at the tensor unit.
ProjectionMateExact gives the proper normalization; open tensor normalization and full
faithfulness of extension by zero give the open normalization. The inner symmetry is
identity and the outer symmetry is the inverse left unitor. Naturality of that unitor,
and equality of the two unitors at the unit, leave precisely integration. -/
theorem evaluation_unit (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (He : Etale.DerivedCategoryModule (Ring P) B)
    (hHe : etaleFiniteTor (Ring P) B He)
    (eH : (comparison (Ring P) B).obj He ≅ unit (Ring P) B) :
    evaluation P B aB (unit (Ring P) B) He hHe eH =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
        (affineTraceLineCompactification B)).map (unitSource P B).hom ≫
      trace P B aB := by
  sorry

/-- The retained bounded-below source in the literal functor coordinates.
Source: admissibility in Step 1 (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def linePlus (B : Scheme.{u}) (H : D P B)
    (He : Etale.DerivedCategoryModule (Ring P) B) (hHe : etaleFiniteTor (Ring P) B He)
    (eH : (comparison (Ring P) B).obj He ≅ H) :
    Plus (Ring P) (AffineSpace PUnit.{u + 1} B) :=
  ⟨(lineSource P B).obj H,
    DerivedCategory.TStructure.t.plus.prop_of_iso (eqToIso (lineSource_obj_eq P B H)).symm
      (source_plus P.coefficients.l P.extension (P.level - 1) B P.level
        (annihilates P) H He hHe eH)⟩

/-- The actual ordinary source and comparison isomorphism, with no choice of antecedent.
Source: admissibility in Step 1 (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def lineWitness (B : Scheme.{u}) (H : D P B)
    (He : Etale.DerivedCategoryModule (Ring P) B) (hHe : etaleFiniteTor (Ring P) B He)
    (eH : (comparison (Ring P) B).obj He ≅ H) :
    Scheme.FixedEtaleOriginWitness (AffineSpace PUnit.{u + 1} B) (Ring P)
      (linePlus P B H He hHe eH) where
  complex := (sourceWitness P.coefficients.l P.extension (P.level - 1) B P.level
    (annihilates P) H He hHe eH).complex
  iso := (sourceWitness P.coefficients.l P.extension (P.level - 1) B P.level
    (annihilates P) H He hHe eH).iso ≪≫ (eqToIso (lineSource_obj_eq P B H)).symm

/-- Compact support with its source-implied Nagata instance, rather than an extra assumption.
Source: separated finite-type domain (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def support {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P)) f

/-- Exceptional inverse image with the same standing compactification as compact support.
Source: exceptional convention (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def exceptionalImage {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  rightDerivedUpperShriek (Ring P) f

/-- The canonical ordinary antecedent of the exceptional image.
Source: exceptional comparison formula (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def exceptionalAntecedent {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : D P B) : Etale.DerivedCategoryModule (Ring P) T :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  (Etale.rightDerivedUpperShriek (Ring P) f).obj
    ((comparisonLowerStar (ModuleCat.{u + 1} (Ring P)) B).rightDerivedFunctor.obj K)

/-- The actual counit, evaluated only at a bounded-below target.
Source: restricted adjunction convention (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def counit {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : Plus (Ring P) B) :
    (support P aB f).obj ((exceptionalImage P aB f).obj K.obj) ⟶ K.obj :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  rightDerivedUpperShriekCounit f K.obj K.property

/-- The canonical antecedent of Rp^!K is finite-Tor constructible, with no added hypothesis.
Source: Step 1, ordinary etale exceptional preservation and constructible origin
(blueprint: lem-pur-affine-line-composite-transpose).
Proof: the bounded-below comparison adjunction unit, followed by Rnu_*(eK), identifies
Ke with Rnu_* K. Transport finite-Tor constructibility along this isomorphism. The
coefficient exponent is positive, annihilates the ring, and is invertible on B, so the
existing ordinary etale exceptional preservation theorem applies. Its output is the
ordinary antecedent exceptionalAntecedent by definition. -/
theorem exceptionalInput {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : Plus (Ring P) B) (Ke : Etale.DerivedCategoryModule (Ring P) B)
    (hKe : etaleFiniteTor (Ring P) B Ke) (eK : (comparison (Ring P) B).obj Ke ≅ K.obj) :
    etaleFiniteTor (Ring P) T (exceptionalAntecedent P aB f K.obj) := by
  let : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  let : HasInvertibleExponent (Ring P) B :=
    ⟨P.coefficients.l ^ (P.level + 1),
      pow_pos (Fact.out : P.coefficients.l.Prime).pos _, annihilates P,
      exponentUnit P B aB⟩
  let U := (comparisonLowerStar (ModuleCat.{u + 1} (Ring P)) B).rightDerivedFunctor
  have hu := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (Ring P)) B Ke hKe.1.1.1
  let e : Ke ≅ U.obj K.obj :=
    asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring P)) B).unit.app Ke) ≪≫
      U.mapIso eK
  have hU : etaleFiniteTor (Ring P) B (U.obj K.obj) :=
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) B).prop_of_iso
      e hKe
  exact Etale.constructibleFiniteTor_rightDerivedUpperShriek (Ring P) aB f hU

/-- Rp^!K as a bounded-below object, from the published preservation of lower bounds.
Source: Step 1 (blueprint: lem-pur-affine-line-composite-transpose). -/
@[implicit_reducible]
def exceptionalPlus {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    {T : Scheme.{u}} (f : T ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : Plus (Ring P) B) : Plus (Ring P) T :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  ⟨(exceptionalImage P aB f).obj K.obj, plus_rightDerivedUpperShriek_obj f K.property⟩

/-- The same b in the standing compactification, using its canonical origin comparison.
Source: b_{q,M} in the composite formula (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def standingEvaluation (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (H : D P B) (He : Etale.DerivedCategoryModule (Ring P) B)
    (hHe : etaleFiniteTor (Ring P) B He) (eH : (comparison (Ring P) B).obj He ≅ H) :
    (support P aB (AffineSpace PUnit.{u + 1} B ↘ B)).obj ((lineSource P B).obj H) ⟶ H :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  (changeSupport (Ring P) (HasCompactification.compactification
    (AffineSpace PUnit.{u + 1} B ↘ B)) (affineTraceLineCompactification B)
    (linePlus P B H He hHe eH) (lineWitness P B H He hHe eH)).hom ≫
    evaluation P B aB H He hHe eH

/-- The normalized compact-support compositor alpha at the actual twisted source.
Source: thm-sf-comp-composition (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def compositor {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (M : D P X) (Me : Etale.DerivedCategoryModule (Ring P) X)
    (hMe : etaleFiniteTor (Ring P) X Me) (eM : (comparison (Ring P) X).obj Me ≅ M) :
    (support P aY p).obj ((support P (p ≫ aY)
      (AffineSpace PUnit.{u + 1} X ↘ X)).obj ((lineSource P X).obj M)) ≅
      (support P aY ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ p)).obj
        ((lineSource P X).obj M) :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  (originCompositionAmbient (Ring P) (AffineSpace PUnit.{u + 1} X ↘ X) p).app
    ⟨_, ⟨(lineWitness P X M Me hMe eM).complex.obj,
      (lineWitness P X M Me hMe eM).complex.property,
      ⟨(lineWitness P X M Me hMe eM).iso⟩⟩⟩

/-- Exactly the inverse adjunction conjugate c, evaluated at K.
Source: composite adjunction and conjugate conventions
(blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def inverseConjugate {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (K : Plus (Ring P) Y) :
    (exceptionalImage P (p ≫ aY) (AffineSpace PUnit.{u + 1} X ↘ X)).obj
      ((exceptionalImage P aY p).obj K.obj) ⟶
    (exceptionalImage P aY ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ p)).obj K.obj :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  compositionInverse (Ring P) (AffineSpace PUnit.{u + 1} X ↘ X) p K

/-- The actual composite exceptional transpose, before applying the composite counit.
Source: Theta display (blueprint: lem-pur-affine-line-composite-transpose). -/
@[irreducible]
def theta {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (M : D P X) (K : Plus (Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke) (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (t : M ⟶ (exceptionalImage P aY p).obj K.obj) :
    (lineSource P X).obj M ⟶
      (exceptionalImage P aY ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ p)).obj K.obj :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  (lineSource P X).map t ≫
    lineComparison P X (p ≫ aY) (exceptionalPlus P aY p K)
      (exceptionalAntecedent P aY p K.obj) (exceptionalInput P aY p K Ke hKe eK)
      (Iso.refl _) ≫ inverseConjugate P aY p K

/-- The actual exceptional transpose is the previous transpose followed by Rp_!(b).
Source: Integration paragraph (blueprint: lem-pur-affine-line-composite-transpose).
Proof: Step 1 establishes finite-Tor admissibility of N=Rp^!K and etale origin of all
sources. Step 4 inverts the defining Hom transpose of gamma_{q,N}, giving b_{q,N}.
Naturality in Step 2 replaces b_{q,N} Rq_!F_q(t) by t b_{q,M}. Step 5 uses the composite
adjunction counit Rp_!(epsilon_q) epsilon_p and the conjugate equation for precisely
originCompositionAmbient. Apply this equation to Theta and cancel c c^-1. Step 6 uses
functoriality of Rp_! to separate t and b, leaving the stated equality. No isomorphy of
gamma and no adjunction on arbitrary ambient pro-etale objects is used. -/
theorem composite_transpose {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (M : D P X) (Me : Etale.DerivedCategoryModule (Ring P) X)
    (hMe : etaleFiniteTor (Ring P) X Me) (eM : (comparison (Ring P) X).obj Me ≅ M)
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke) (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (t : M ⟶ (exceptionalImage P aY p).obj K.obj) :
    (support P aY ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ p)).map
        (theta P aY p M K Ke hKe eK t) ≫
      counit P aY ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ p) K =
    (compositor P aY p M Me hMe eM).inv ≫
      (support P aY p).map (standingEvaluation P X (p ≫ aY) M Me hMe eM) ≫
      (support P aY p).map t ≫ counit P aY p K := by
  sorry

end AlgebraicGeometry.ProEtale.AffineLineEvaluation

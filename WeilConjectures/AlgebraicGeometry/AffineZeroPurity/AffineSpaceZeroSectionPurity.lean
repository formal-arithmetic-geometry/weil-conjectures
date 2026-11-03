/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientation
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionConstructions
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionProductRecursion
import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionOrientationCoordinates
import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionContractionCoordinates
import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionNormalization
import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineLineComparisonNaturality
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationFusion
import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingFinitePowers
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange

/-! # Zero-section purity for affine space

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.md, and its eight-step DAG proof
(blueprint: cor-pur-affine-space-zero-section-purity).

The ordinary supported Cartier family and the specified exact site comparison
construct the coordinate boundaries. Their supported cup product, including the
empty unit, determines the Thom map by the closed exceptional Hom bijection.
The inverse uses the actual ordered affine-space comparison and the conjugate
of the specified compact-support compositor. No purity isomorphism is chosen.

## Main definitions

- `supportedClass`, `thom`: the actual coordinate product and its exceptional adjunct.
- `gamma`, `normalization`: the recorded comparison and its normalized inverse candidate.
- `classBaseChange`: the canonical closed exchange followed by derived inverse image.

## Main statements

- `zeroSection_purity`: invertibility and both normalized inverse equations.
- `zeroSection_purity_untwisted`: the equivalent negative twist and shift.
- `zeroSection_purity_baseChange`: compatibility with arbitrary base change.
-/

set_option autoImplicit false

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

set_option maxHeartbeats 800000 in
-- Comparing the two root exponents unfolds the finite coefficient presentation.
section NormalizedThom

open AffineSpacePurity

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe v w

private def comparedUnit (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    (comparison (setting P n).Coefficient X).obj
      (Etale.ordinaryFiniteUnit (setting P n).Coefficient X) ≅ unit P n X :=
  (Functor.mapDerivedCategorySingleFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} (setting P n).Coefficient) X) 0).app
      ((setting P n).constantEtale X) ≪≫ (eqToIso (unit_single_eq P n X)).symm

private def comparedLine (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    (comparison (setting P n).Coefficient X).obj
      ((Etale.ordinaryFiniteLine (setting P n).Coefficient (setting P n).diagonalExponent
        (setting P n).diagonalExponent_annihilates X)⟦(2 : ℤ)⟧) ≅
      AffineSpacePurity.shiftedLine (setting P n) X :=
  let Q := setting P n
  let hX := AffineLinePurity.primeUnit Q X aX
  twistDerived P.coefficients.l P.extension n X hX n Q.diagonalExponent_annihilates 1 2 ≪≫
    (twistDerived P.coefficients.l P.extension n X hX (n + 1)
      (AffineSpacePurity.annihilates Q) 1 2).symm

private def comparedOrderedTarget (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) : (c : ℕ) →
    (comparison (setting P n).Coefficient X).obj
      ((setting P n).diagonalTwistEtale X c) ≅ target P n X c
  | 0 => comparedUnit P n X
  | c + 1 => tensorComparison (setting P n).Coefficient X _ _ ≪≫
      AffineSpacePurity.tensorIso (setting P n).Coefficient X
        (comparedOrderedTarget P n X aX c) (comparedLine P n X aX)

private def comparedPositiveTarget (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (comparison (setting P n).Coefficient X).obj
      ((setting P n).functorialCupTarget false X (2 * (c : ℤ)) c) ≅ target P n X c :=
  (comparison (setting P n).Coefficient X).mapIso
    (AdicSmoothDualizing.etalePowerComparison (setting P n) X
      ((setting P n).diagonalExponent_isUnit aX) c).symm ≪≫
    comparedOrderedTarget P n X aX c

private def signedTargetEvaluation (Q : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of Q.field.k)) (a b r s : ℤ)
    (hab : a + b = 0) (hrs : r + s = 0) :
    ((Etale.ordinaryFiniteTensor Q.Coefficient X).obj
      (Q.functorialCupTarget false X a r)).obj (Q.functorialCupTarget false X b s) ≅
        Etale.ordinaryFiniteUnit Q.Coefficient X := by
  let e : Q.functorialCupTwist false X r ⊗ Q.functorialCupTwist false X s ≅
      Q.functorialCupTwist false X 0 :=
    Q.functorialCupTwistProduct false X aX r s ≪≫
      eqToIso (congrArg (Q.functorialCupTwist false X) hrs)
  let inverse : TensorInverse (Q.functorialCupTwist false X r) :=
    { obj := Q.functorialCupTwist false X (-r)
      rightIso := Q.functorialCupTwistProduct false X aX r (-r) ≪≫
        eqToIso (congrArg (Q.functorialCupTwist false X) (add_neg_cancel r))
      leftIso := Q.functorialCupTwistProduct false X aX (-r) r ≪≫
        eqToIso (congrArg (Q.functorialCupTwist false X) (neg_add_cancel r)) }
  let hf : ObjectProperty.flat (Q.functorialCupTwist false X r) := inverse.flat
  exact Etale.derivedTensorShiftIso (ModuleCat.{u + 1} Q.Coefficient) _ _ a b ≪≫
    (shiftFunctor _ (a + b)).mapIso
      (Etale.singleFunctorObjTensorIso _ _ hf ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e) ≪≫
    (shiftFunctorZero' _ (a + b) hab).app _

private def signedTargetPullback (Q : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) (aX : X ⟶ Spec (.of Q.field.k)) (a r : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} Q.Coefficient) i).leftDerivedFunctor.obj
      (Q.functorialCupTarget false X a r) ≅ Q.functorialCupTarget false Z a r :=
  let F := Etale.upperStar (ModuleCat.{u + 1} Q.Coefficient) i
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ i).app _ ≪≫
    (F.mapDerivedCategory.commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (Q.functorialCupSingle false Z).mapIso (Q.functorialCupTwistPullback false i aX r))

private theorem identity_casts_cancel {C : Type v} [Category.{w} C]
    {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ (𝟙 X ≫ f) ≫ 𝟙 Y = f := by
  simp only [Category.id_comp, Category.comp_id]

private theorem transport_normalized {C : Type v} [Category.{w} C]
    {M W R R' S : C} (e : M ≅ W) (d : R ≅ S)
    (u : W ⟶ R) (v : M ⟶ S) (a : R ⟶ R') (a' : R' ⟶ W) (b : S ⟶ M)
    (hv : IsIso v) (hs : u ≫ d.hom = e.inv ≫ v)
    (ht : d.inv ≫ a ≫ a' ≫ e.inv = b) (he : v ≫ b = 𝟙 M) :
    IsIso u ∧ u ≫ a ≫ a' = 𝟙 W := by
  have hu : u = e.inv ≫ v ≫ d.inv := by
    apply (cancel_mono d.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hs
  refine ⟨?_, ?_⟩
  · rw [hu]
    have := hv
    infer_instance
  · apply (cancel_mono e.inv).1
    calc
      (u ≫ a ≫ a') ≫ e.inv = (u ≫ d.hom) ≫ (d.inv ≫ a ≫ a' ≫ e.inv) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = (e.inv ≫ v) ≫ b := by rw [hs, ht]
      _ = 𝟙 W ≫ e.inv := by
        simp only [Category.assoc, he, Category.comp_id, Category.id_comp]

private theorem normalized_successor {C E : Type v} [Category.{w} C] [Category.{w} E]
    (G : E ⥤ C) {T Z : C} {W R : E}
    (t : T ⟶ G.obj W) (u : W ⟶ R) (v : R ⟶ W)
    (d : G.obj R ⟶ Z) (b : Z ⟶ T) (a : G.obj W ⟶ T)
    (hd : d ≫ b = G.map v ≫ a) (hu : u ≫ v = 𝟙 W) (ht : t ≫ a = 𝟙 T) :
    (t ≫ G.map u ≫ d) ≫ b = 𝟙 T := by
  simp only [Category.assoc]
  rw [hd, ← Functor.map_comp_assoc, hu, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ht

private theorem right_inverse_from_left {C : Type v} [Category.{w} C]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (hf : IsIso f) (h : f ≫ g = 𝟙 X) :
    g ≫ f = 𝟙 Y := by
  have := hf
  apply (cancel_epi f).1
  simp only [← Category.assoc, h, Category.id_comp, Category.comp_id]

private theorem section_normalization
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    IsIso (sectionAdjunct P n B aB r) ∧
      sectionAdjunct P n B aB r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).map
          (CoordinateTowerNormalization.targetLineGamma P n B aB r) ≫
        CoordinateTowerNormalization.lineCollapse P n B aB r = 𝟙 _ := by
  let := (tower_geometry aB r).1
  let := (tower_geometry aB r).2.1
  let := (tower_geometry aB r).2.2
  let : IsNoetherian (iteratedAffineLine B r) :=
    tower_noetherian (setting P n) B aB r
  obtain ⟨hI, _, _, _, _, _, hNorm⟩ :=
    CoordinateSectionNormalization.twistedCoordinateSectionNormalization
      (setting P n) (iteratedAffineLine B r) (towerBase aB r)
  obtain ⟨hT, _, _, hp⟩ := hNorm (setting P n).level (annihilates (setting P n))
  obtain ⟨hM, hplus, hpf, hunit, hu, _, he⟩ :=
    hp (CoordinateSectionCoordinates.input P n (iteratedAffineLine B r) r)
      (Or.inr ⟨r, rfl⟩)
  exact transport_normalized
    (CoordinateSectionCoordinates.tateComparison P n _ (towerBase aB r) r)
    (CoordinateSectionCoordinates.orientationTargetComparison P n B aB r)
    (sectionAdjunct P n B aB r) _ _ _ _ hu
    (CoordinateSectionCoordinates.sectionAdjunct_coordinates P n B aB r hI hT hpf)
    (CoordinateSectionCoordinates.lineContraction_coordinates P n B aB r hM hplus hunit) he

/-- Pull back a supported product using the actual closed exchange map, exact
inverse image, and the canonical ordered Tate-line pullback identification.
Its exceptional transpose is the closed exceptional base-change mate.
Source: proof Step 7 (blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def classBaseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c) :
    (cupSingle (setting P n) (iteratedAffineLine B' c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)).obj
        ((setting P n).constant B')) ⟶ target P n (iteratedAffineLine B' c) c :=
  (coordinateSourcePullback P n g c).inv ≫
    (AffineSpacePurity.inverseImage (setting P n).Coefficient (spaceMap g c)).map α ≫
    (targetPullbackIso P n (spaceMap g c) (AffineSpacePurity.towerBase aB c) c).hom
private theorem coordinate_line_law
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    CoordinateTowerNormalization.LineLaw P n B aB c := by
  unfold CoordinateTowerNormalization.LineLaw
  intro r
  let := (tower_geometry aB r.val).1
  let := (tower_geometry aB r.val).2.1
  let := (tower_geometry aB r.val).2.2
  refine ⟨?_, ?_⟩
  · intro K Ke hKe eK
    let : IsNoetherian (iteratedAffineLine B r.val) :=
      tower_noetherian (setting P n) B aB r.val
    obtain ⟨hT, _, h⟩ :=
      (CoordinateLine.coordinateLineAdjunction (setting P n) _ (towerBase aB r.val)).2.2.2.2.2.1
        (setting P n).level (annihilates (setting P n))
    unfold CoordinateTowerNormalization.lineGamma lineComparison
    exact IsIso.comp_isIso' inferInstance
      (IsIso.comp_isIso' (h K Ke hKe eK).2
        (lineExceptionalIso (setting P n).Coefficient
          (iteratedAffineLine B r.val) K.obj).isIso_hom)
  · intro K L Ke Le hKe hLe eK eL f
    unfold CoordinateTowerNormalization.lineGamma
    exact lineComparison_natural (setting P n) _ (towerBase aB r.val)
      K Ke hKe eK L Le hLe eL f

private theorem thom_zero_eq_identityUnit
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] [CompactSpace B] :
    thom P n B aB 0 =
      identityUnit (setting P n).Coefficient B (unit P n B) (unit_origin P n B) := by
  rw [(coordinate_section_product_recursion P n B aB).2.1]
  unfold coordinateIdentityAdjunct coordinateIdentity identityUnit
  rfl

private theorem normalization_zero_eq
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] [CompactSpace B] :
    normalization P n B aB 0 =
      @inv _ _ _ _ (identityUnit (setting P n).Coefficient B
        (unit P n B) (unit_origin P n B))
        (identityUnit_isIso _ _ _ (unit_origin P n B)) := by
  unfold normalization normalizationRaw
  erw [eqToHom_refl, eqToHom_refl]
  · exact identity_casts_cancel
      (@inv _ _ _ _ (identityUnit (setting P n).Coefficient B
        (unit P n B) (unit_origin P n B))
        (identityUnit_isIso _ _ _ (unit_origin P n B)))
  all_goals rfl

private theorem coordinate_composition_eq
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    coordinateExceptionalComposition P n B aB r =
      CoordinateTowerNormalization.closedCompositionInverse P n B aB r := by
  unfold coordinateExceptionalComposition CoordinateTowerNormalization.closedCompositionInverse
  rfl

private theorem assemble_zeroSection (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (hiso : ∀ r : ℕ, IsIso (sectionAdjunct P n B aB r))
    (heval : ∀ r : ℕ, sectionAdjunct P n B aB r ≫
      (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).map
        (CoordinateTowerNormalization.targetLineGamma P n B aB r) ≫
      CoordinateTowerNormalization.lineCollapse P n B aB r = 𝟙 _) (c : ℕ) :
    IsIso (thom P n B aB c) ∧
      thom P n B aB c ≫ normalization P n B aB c = 𝟙 _ ∧
      normalization P n B aB c ≫ thom P n B aB c = 𝟙 _ := by
  let : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  have hthom : ∀ r : ℕ, IsIso (thom P n B aB r) := by
    intro r
    induction r with
    | zero =>
      rw [thom_zero_eq_identityUnit]
      exact identityUnit_isIso _ _ _ (unit_origin P n B)
    | succ r ih =>
      rw [(coordinate_section_product_recursion P n B aB).2.2.2 r]
      have := hiso r
      have := coordinateExceptionalComposition_isIso P n B aB r
      infer_instance
  have hleft : ∀ r : ℕ, thom P n B aB r ≫ normalization P n B aB r = 𝟙 _ := by
    intro r
    induction r with
    | zero =>
      rw [thom_zero_eq_identityUnit, normalization_zero_eq]
      exact @IsIso.hom_inv_id _ _ _ _ _ (identityUnit_isIso _ _ _ (unit_origin P n B))
    | succ r ih =>
      rw [(coordinate_section_product_recursion P n B aB).2.2.2 r]
      have hf := CoordinateTowerNormalization.normalization_fusion P n B aB r
        (coordinate_line_law P n B aB (r + 1))
      rw [← coordinate_composition_eq P n B aB r] at hf
      exact normalized_successor _ _ _ _ _ _ _ hf (heval r) ih
  exact ⟨hthom c, hleft c,
    right_inverse_from_left _ _ (hthom c) (hleft c)⟩

/-- The product of coordinate Kummer boundaries gives the canonical zero-section
purity isomorphism, with precisely the inverse specified by the ordered gamma.
The positive level n+1 ranges over every allowed coefficient level.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity, proof Steps 1--8
(blueprint: cor-pur-affine-space-zero-section-purity).
Proof: polynomial charts establish the finite-type, separated and Cartier geometry.
The standard projective-line compactification and its normalized trace give the
ordinary line adjunction. The zero-divisor Kummer class forgets to c_1(O(1)),
and the trace sends this class to one. Exact monoidal site comparison transports
this equality and its adjoint to the specified pro-etale twists at every level.
Tensor the rank-one calculation with the invertible r-th Tate line and shift 2r;
the projection formula shows that its evaluation is still the identity. Induct
on c, starting with the empty product identity. The closed adjoints of the
successive orientations are exactly the supported cup products defining
supportedClass. Every orientation factor is invertible. Substitute the ordered
recursion defining gamma. Naturality moves gamma_r through the line comparison,
and the twisted rank-one evaluation cancels the last factor. Associativity and
identity coherence of the compact-support compositor and mate pasting reduce
the composite to the dimension-r identity. Thus normalization is the inverse.
Transposing this identity through the composite adjunction says exactly that
integration sends the supported zero-section class to one. Inverting the Tate
line and shifting back gives the untwisted equivalent stated below. -/
theorem zeroSection_purity (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    IsIso (thom P n B aB c) ∧
      thom P n B aB c ≫ normalization P n B aB c = 𝟙 _ ∧
      normalization P n B aB c ≫ thom P n B aB c = 𝟙 _ := by
  exact assemble_zeroSection P n B aB
    (fun r ↦ (section_normalization P n B aB r).1)
    (fun r ↦ (section_normalization P n B aB r).2) c

/-- The equivalent untwisted derived isomorphism, with the specified negative Tate
line and shift. Source: proof Step 8
(blueprint: cor-pur-affine-space-zero-section-purity).
Proof: invert the finite Tate line in zeroSection_purity. The canonical closed
coprojection comparison moves this line through Rz!, and the shift comparison
moves [2c] through it. Tensoring with A(-c)[-2c] gives the displayed isomorphism. -/
theorem zeroSection_purity_untwisted (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    Nonempty
      ((rightDerivedUpperShriek (setting P n).Coefficient
          (zero B c)).obj (unit P n (iteratedAffineLine B c)) ≅
        ((setting P n).functorialCupSingle true B).obj
          ((setting P n).functorialCupTwist true B (-(c : ℤ)))⟦-(2 * (c : ℤ))⟧) := by
  let Q := setting P n
  let X := iteratedAffineLine B c
  let aX := AffineSpacePurity.towerBase aB c
  have : IsNoetherian B := AffineSpacePurity.tower_noetherian Q B aB 0
  have : IsNoetherian X := AffineSpacePurity.tower_noetherian Q B aB c
  let G := Etale.rightDerivedUpperShriek Q.Coefficient (zero B c)
  let GP := rightDerivedUpperShriek Q.Coefficient (zero B c)
  let CB := comparison Q.Coefficient B
  let L := Q.functorialCupTarget false X (2 * (c : ℤ)) c
  let M := Q.functorialCupTarget false X (-(2 * (c : ℤ))) (-(c : ℤ))
  have hL : DerivedCategory.TStructure.t.plus L := by
    let W := (DerivedCategory.singleFunctor _ 0).obj (Q.functorialCupTwist false X c)
    have : W.IsGE 0 := inferInstance
    refine ⟨-(2 * (c : ℤ)), ?_⟩
    change (W⟦2 * (c : ℤ)⟧).IsGE (-(2 * (c : ℤ)))
    exact DerivedCategory.TStructure.t.isGE_shift W 0 (2 * (c : ℤ))
      (-(2 * (c : ℤ))) (by omega)
  have hU : DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit Q.Coefficient X) :=
    ⟨0, inferInstance⟩
  have hUB : DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit Q.Coefficient B) :=
    ⟨0, inferInstance⟩
  have hGL := Etale.plus_rightDerivedUpperShriek_obj Q.Coefficient (zero B c) L hL
  have ht := (zeroSection_purity P n B aB c).1
  let ePro : CB.obj (G.obj L) ≅ CB.obj (Etale.ordinaryFiniteUnit Q.Coefficient B) :=
    (rightDerivedUpperShriekMapDerivedCategoryObjIso (zero B c) L hL).symm ≪≫
      GP.mapIso (comparedPositiveTarget P n X aX c) ≪≫
      (@asIso _ _ _ _ (thom P n B aB c) ht).symm ≪≫ (comparedUnit P n B).symm
  have hηL := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} Q.Coefficient) B (G.obj L) hGL
  have hηU := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} Q.Coefficient) B (Etale.ordinaryFiniteUnit Q.Coefficient B) hUB
  let eOrd : G.obj L ≅ Etale.ordinaryFiniteUnit Q.Coefficient B :=
    asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Q.Coefficient) B).unit.app
      (G.obj L)) ≪≫
    (comparisonLowerStar (ModuleCat.{u + 1} Q.Coefficient) B).rightDerivedFunctor.mapIso ePro ≪≫
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Q.Coefficient) B).unit.app
      (Etale.ordinaryFiniteUnit Q.Coefficient B))).symm
  let e := signedTargetEvaluation Q X aX (2 * (c : ℤ)) (-(2 * (c : ℤ)))
    c (-(c : ℤ)) (add_neg_cancel _) (add_neg_cancel _)
  let e' := signedTargetEvaluation Q X aX (-(2 * (c : ℤ))) (2 * (c : ℤ))
    (-(c : ℤ)) c (neg_add_cancel _) (neg_add_cancel _)
  let eUntwisted : G.obj (Etale.ordinaryFiniteUnit Q.Coefficient X) ≅
      Q.functorialCupTarget false B (-(2 * (c : ℤ))) (-(c : ℤ)) :=
    G.mapIso e.symm ≪≫
      (Etale.derivedTensorRightCompRightDerivedUpperShriekIsoOfTensorIso
        Q.Coefficient (zero B c) M L
          (e ≪≫ Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} Q.Coefficient) X)
          (e' ≪≫ Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} Q.Coefficient) X)).app L ≪≫
      ((Etale.ordinaryFiniteTensor Q.Coefficient B).mapIso
        (eOrd ≪≫ Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} Q.Coefficient) B)).app _ ≪≫
      Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} Q.Coefficient) B _ ≪≫
      signedTargetPullback Q (zero B c) aX (-(2 * (c : ℤ))) (-(c : ℤ))
  let F := Q.functorialCupComparisonFunctor B
  let eTarget : CB.obj (Q.functorialCupTarget false B (-(2 * (c : ℤ))) (-(c : ℤ))) ≅
      Q.functorialCupTarget true B (-(2 * (c : ℤ))) (-(c : ℤ)) :=
    (F.mapDerivedCategory.commShiftIso _).app _ ≪≫
      (shiftFunctor _ _).mapIso ((F.mapDerivedCategorySingleFunctor 0).app _)
  exact ⟨GP.mapIso (comparedUnit P n X).symm ≪≫
    rightDerivedUpperShriekMapDerivedCategoryObjIso (zero B c)
      (Etale.ordinaryFiniteUnit Q.Coefficient X) hU ≪≫ CB.mapIso eUntwisted ≪≫ eTarget⟩

/-- Every base change preserves the specified class, equivalently its exceptional
adjunct thom under the closed exceptional base-change mate classBaseChange.
Source: proof Step 7 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: coordinate equations pull back to the same equations, which remain Cartier.
The normalized Cartier boundaries pull back to their namesakes. The supported
coefficient multiplication restricts and multiplies local constants, operations
that commute with inverse image. The exact monoidal comparison transports the
iterated product and its empty unit. The unique support identifications commute
because they are over X. This proves equality of the displayed supported arrows.
Taking the same closed adjunction on both sides gives precisely the exceptional
base-change square, by mate pasting. No flatness or smoothness of g is used. -/
theorem zeroSection_purity_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType aB'] [QuasiCompact aB'] [IsSeparated aB']
    (hg : g ≫ aB = aB') (c : ℕ) :
    classBaseChange P n g aB c (supportedClass P n B aB c) =
      supportedClass P n B' aB' c := by
  subst aB'
  have h := (coordinate_section_product_baseChange P n g aB c).1
  simpa only [classBaseChange] using h

attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction identityUnit
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

end NormalizedThom

end AlgebraicGeometry.ProEtale.AffineZeroPurity

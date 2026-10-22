module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import Sheaf.Paper.AffineSpaceCoordinateBoundaries
public import Sheaf.Paper.AffineSpaceThomMap
public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.PurityAffineLineOrientation
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.AffineLinePurityComparison

import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Paper.VectorIntegrationSiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

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
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

/-- Pullback of the coefficient unit with its canonical monoidal normalization.
Source: proof Step 1 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def unitPullback (P : PurityFiniteSetting.{u}) (n : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (AffineSpacePurity.inverseImage (setting P n).Coefficient f).obj (unit P n Y) ≅
      unit P n X :=
  (AffineSpacePurity.inverseImage (setting P n).Coefficient f).mapIso
      (eqToIso (unit_single_eq P n Y)) ≪≫
    pullbackSingle (setting P n).Coefficient f ((setting P n).constant Y)
      ((setting P n).constant X) ((setting P n).frameConstantPullback f) ≪≫
    (eqToIso (unit_single_eq P n X)).symm

/-- Keep the canonical constant-pullback comparison at its literal computed endpoints.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def targetSourceRaw (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) :
    (c : ℕ) → Σ M N : D P n (iteratedAffineLine B c), M ≅ N
  | 0 => ⟨_, _, Iso.refl (unit P n B)⟩
  | c + 1 => ⟨_, _, (AffineSpacePurity.action
      ((AffineSpacePurity.tensor (setting P n).Coefficient (iteratedAffineLine B (c + 1))).flip.obj
        (AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B (c + 1))))
          (c + 1)).mapIso (unitPullback P n (iteratedAffineLineProj B (c + 1))).symm⟩

/-- The raw comparison starts at the ordered tensor target, including the empty unit.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: at zero both objects are the coefficient unit. At a successor, mapIso
starts at the tensor action on the coefficient unit of the total affine space,
which is precisely target. -/
theorem targetSourceRaw_left (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) :
    (targetSourceRaw P n B c).1 = target P n (iteratedAffineLine B c) c := by
  sorry

/-- The raw comparison ends at the recorded ordered source on the coefficient unit.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: at zero orderedSource is the identity. At a successor, unfold orderedSource
and twistAction: its object is the same tensor action on the total inverse image
of the base coefficient unit. This is the endpoint of mapIso in targetSourceRaw. -/
theorem targetSourceRaw_right (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) :
    (targetSourceRaw P n B c).2.1 =
      (AffineSpacePurity.orderedSource (setting P n) B c).obj (unit P n B) := by
  sorry

/-- The canonical constant-pullback identification of the product target with the
source of the recorded ordered comparison. The equalities only expose the
literal computed endpoints; the map is the actual constant-pullback comparison.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def targetSourceIso (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (c : ℕ) :
    target P n (iteratedAffineLine B c) c ≅
      (AffineSpacePurity.orderedSource (setting P n) B c).obj (unit P n B) :=
  (eqToIso (targetSourceRaw_left P n B c)).symm ≪≫
    (targetSourceRaw P n B c).2.2 ≪≫ eqToIso (targetSourceRaw_right P n B c)

/-- Finite-Tor constructibility of the ordinary coefficient unit.
Source: proof Step 1 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: the constant coefficient sheaf is locally free of rank one, hence
constructible and flat. Its degree-zero complex has Tor amplitude [0,0]. -/
theorem unit_finiteTor (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) :
    AffineSpacePurity.etaleFiniteTor (setting P n).Coefficient B
      ((DerivedCategory.singleFunctor _ 0).obj ((setting P n).constantEtale B)) := by
  sorry

/-- The ordered affine-space comparison at the coefficient unit, with its actual
ordinary witness and canonical comparison isomorphism. Source: proof Step 6
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def gamma (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    AffineSpacePurity.ComparisonHom (setting P n) B (unit P n B) c :=
  AffineSpacePurity.affineSpacePurityComparison (setting P n) B aB
    ⟨unit P n B, (unit_origin P n B).plus⟩
    ((DerivedCategory.singleFunctor _ 0).obj ((setting P n).constantEtale B))
    (unit_finiteTor P n B)
    (((Functor.mapDerivedCategorySingleFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} (setting P n).Coefficient) B) 0).app
        ((setting P n).constantEtale B)) ≪≫ (eqToIso (unit_single_eq P n B)).symm) c

/-- The affine projection composed with the zero vector is the identity.
Source: proof Step 1 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: the projection discards the zero coordinates, so the composite is the
identity structure map, by the universal property of the affine tower. -/
theorem zero_proj (B : Scheme.{u}) (c : ℕ) :
    zero B c ≫ iteratedAffineLineProj B c = 𝟙 B := by
  sorry

/-- The identity exceptional unit is fixed by the actual compact-support identity.
Source: proof Steps 3 and 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def identityUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) [CompactSpace B]
    (K : AffineSpacePurity.C A B)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) B K) :
    K ⟶ (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (𝟙 B)).obj K :=
  rightDerivedUpperShriekHomEquiv (𝟙 B) hK hK.plus
    (((originCompactSupportId A B).hom.app ⟨K, hK⟩).hom)

/-- The identity-adjunction normalization is invertible on its actual origin domain.
Source: proof Steps 3 and 6 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: the identity compact-support comparison identifies its left adjoint with
identity on the origin class. Conjugation identifies the right adjoint with
identity, with unit precisely identityUnit. The triangular identities give its inverse. -/
theorem identityUnit_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) [CompactSpace B]
    (K : AffineSpacePurity.C A B)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) B K) :
    IsIso (identityUnit A B K hK) := by
  sorry


/-- Collapse the pasted exceptional adjunction using the equality pz=id.
The map is the inverse conjugate of the published compact-support compositor,
followed by equality transport and the inverse of the normalized identity unit.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def collapse (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (iteratedAffineLineProj B c)).obj (unit P n B)) ⟶ unit P n B :=
  letI : IsNoetherian B := AffineSpacePurity.tower_noetherian (setting P n) B aB 0
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  letI : HasCompactification (iteratedAffineLineProj B c) :=
    (AffineSpacePurity.projection_geometry B c).2
  letI : HasCompactification (zero B c ≫ iteratedAffineLineProj B c) :=
    HasCompactification.of_eq (f := 𝟙 B) (zero_proj B c).symm
  AffineSpacePurity.compositionInverse (setting P n).Coefficient (zero B c)
      (iteratedAffineLineProj B c) ⟨unit P n B, (unit_origin P n B).plus⟩ ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero_proj B c)).hom.app (unit P n B) ≫
    @inv _ _ _ _ (identityUnit (setting P n).Coefficient B (unit P n B) (unit_origin P n B))
      (identityUnit_isIso (setting P n).Coefficient B (unit P n B) (unit_origin P n B))

/-- The dimension-zero zero section is the literal identity morphism.
Source: proof Steps 1 and 5 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: unfold zero and the empty-coordinate equation of toIteratedAffineLine;
the supplied base map is the identity. -/
theorem zero_zero (B : Scheme.{u}) : zero B 0 = 𝟙 B := by
  sorry

/-- Compute the prescribed inverse candidate at its literal derived endpoints.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def normalizationRaw (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (c : ℕ) → Σ M N : D P n B, M ⟶ N
  | 0 =>
    letI : IsNoetherian B := AffineSpacePurity.tower_noetherian (setting P n) B aB 0
    letI hId : HasCompactification (𝟙 B) := HasCompactification.of_isProper (𝟙 B)
    letI hZero : HasCompactification (zero B 0 : B ⟶ B) :=
      @HasCompactification.of_eq B B (𝟙 B) (zero B 0) hId (zero_zero B).symm
    ⟨_, _, (@rightDerivedUpperShriekCongr
        (ModuleCat.{u + 1} (setting P n).Coefficient) inferInstance inferInstance inferInstance
        B B (zero B 0) (𝟙 B) (zero_zero B) hZero hId
        (@Etale.isLeftAdjoint_rightDerivedLowerShriek B B (zero B 0) hZero
          (setting P n).Coefficient inferInstance inferInstance)
        (@Etale.isLeftAdjoint_rightDerivedLowerShriek B B (𝟙 B) hId
          (setting P n).Coefficient inferInstance inferInstance)).hom.app (unit P n B) ≫
      @inv _ _ _ _ (identityUnit (setting P n).Coefficient B (unit P n B) (unit_origin P n B))
        (identityUnit_isIso (setting P n).Coefficient B (unit P n B) (unit_origin P n B))⟩
  | c + 1 => by
    letI : HasCompactification (iteratedAffineLineProj B (c + 1)) :=
      (AffineSpacePurity.projection_geometry B (c + 1)).2
    have γ := gamma P n B aB (c + 1)
    unfold AffineSpacePurity.ComparisonHom AffineSpacePurity.exceptional at γ
    exact ⟨_, _, (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B (c + 1))).map
        ((targetSourceIso P n B (c + 1)).hom ≫ γ) ≫
      collapse P n B aB (c + 1)⟩

/-- The inverse candidate starts at the exceptional inverse image of the Tate target.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: at zero the tensor action is the identity and the affine space is B.
At a successor functoriality of Rz! gives exactly the source of targetSourceIso.
The subsequent arrows change only the codomain. -/
theorem normalizationRaw_left (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    (normalizationRaw P n B aB c).1 =
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (zero B c)).obj (target P n (iteratedAffineLine B c) c) := by
  sorry

/-- The inverse candidate ends at the coefficient unit, through its identity normalization.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity).
Proof: the zero case ends in the inverse identity unit. The positive case ends
in collapse, whose codomain is the same coefficient unit by definition. -/
theorem normalizationRaw_right (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    (normalizationRaw P n B aB c).2.1 = unit P n B := by
  sorry

/-- The displayed inverse candidate Rz!gamma followed by the adjunction-preserving
composition identification. Dimension zero uses the normalized identity adjunction.
The transports only expose the literal computed source and target.
Source: proof Step 6 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def normalization (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (zero B c)).obj (target P n (iteratedAffineLine B c) c) ⟶ unit P n B :=
  eqToHom (normalizationRaw_left P n B aB c).symm ≫
    (normalizationRaw P n B aB c).2.2 ≫ eqToHom (normalizationRaw_right P n B aB c)

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
  sorry

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
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B c)).obj (unit P n (iteratedAffineLine B c)) ≅
        ((setting P n).functorialCupSingle true B).obj
          ((setting P n).functorialCupTwist true B (-(c : ℤ)))⟦-(2 * (c : ℤ))⟧) := by
  sorry


/-- Coordinate-preserving base change of the ordered affine tower.
Source: proof Step 7 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def spaceMap {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    iteratedAffineLine B' c ⟶ iteratedAffineLine B c :=
  Scheme.Hom.toIteratedAffineLine (iteratedAffineLineProj B' c ≫ g)
    (iteratedAffineLine.coord B' c)

/-- The zero-section square is Cartesian for every base change, including identity
and nonflat base changes. Source: proof Step 7
(blueprint: cor-pur-affine-space-zero-section-purity).
Proof: on polynomial charts the square is base change of the augmentation
R[t_1,...,t_c] to R. Tensoring this presentation with the new base gives its
augmentation. These pullback squares glue; c=0 is the identity square. -/
theorem zero_square {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    IsPullback g (zero B' c) (zero B c) (spaceMap g c) := by
  sorry

/-- The canonical chosen pullback identification from the Cartesian zero square.
Source: proof Step 7 (blueprint: cor-pur-affine-space-zero-section-purity). -/
def zeroSquare {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    ChosenCartesianSquare g (zero B' c) (zero B c) (spaceMap g c) where
  toCommSq := (zero_square g c).toCommSq
  isoPullback := (zero_square g c).isoPullback
  hom_fst := (zero_square g c).isoPullback_hom_fst
  hom_snd := (zero_square g c).isoPullback_hom_snd

/-- Pullback of the ordered Tate tensor power through the canonical tensor and
finite-root-line comparisons. Source: proof Step 7
(blueprint: cor-pur-affine-space-zero-section-purity). -/
def targetPullbackIso (P : PurityFiniteSetting.{u}) (n : ℕ) {X' X : Scheme.{u}}
    (v : X' ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (AffineSpacePurity.inverseImage (setting P n).Coefficient v).obj (target P n X c) ≅
      target P n X' c :=
  AffineSpacePurity.actionPullbackIso
    ((AffineSpacePurity.tensor (setting P n).Coefficient X).flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X))
    ((AffineSpacePurity.tensor (setting P n).Coefficient X').flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X'))
    (AffineSpacePurity.inverseImage (setting P n).Coefficient v)
    (fun M ↦ AffineSpacePurity.inverseImageTensorIso (setting P n).Coefficient v M
      (AffineSpacePurity.shiftedLine (setting P n) X) ≪≫
        AffineSpacePurity.tensorIso (setting P n).Coefficient X' (Iso.refl _)
          (AffineSpacePurity.shiftedLinePullback (setting P n) v aX)) (unit P n X) c ≪≫
    (AffineSpacePurity.action
      ((AffineSpacePurity.tensor (setting P n).Coefficient X').flip.obj
        (AffineSpacePurity.shiftedLine (setting P n) X')) c).mapIso (unitPullback P n v)

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
  (cupSingle (setting P n) (iteratedAffineLine B' c)).map
      ((setting P n).functorialCupExchange true (zero B c) (zero B' c)
        (spaceMap g c) g (zeroSquare g c)).inv ≫
    (Functor.mapDerivedCategorySingleFunctor
      (upperStar (ModuleCat.{u + 1} (setting P n).Coefficient) (spaceMap g c)) 0).inv.app
        ((setting P n).functorialCupSource true (zero B c)) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (setting P n).Coefficient) (spaceMap g c)).inv.app _ ≫
    (AffineSpacePurity.inverseImage (setting P n).Coefficient (spaceMap g c)).map α ≫
    (targetPullbackIso P n (spaceMap g c) (AffineSpacePurity.towerBase aB c) c).hom

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
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity

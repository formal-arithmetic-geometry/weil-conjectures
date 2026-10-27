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

public import Sheaf.Paper.AffineSpaceZeroSectionConstructions
public import Sheaf.Paper.CoordinateZeroBaseChange
import Sheaf.Paper.CoordinateSectionProductRecursion

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

end AlgebraicGeometry.ProEtale.AffineZeroPurity

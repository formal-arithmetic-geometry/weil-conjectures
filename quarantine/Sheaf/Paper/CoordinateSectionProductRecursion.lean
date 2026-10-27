module

public import Sheaf.Paper.CoordinateZeroBaseChange
public import Sheaf.Paper.CoordinateProductPresentations
import Sheaf.Paper.CoordinateSupportedProductRecursion
import Sheaf.Paper.CoordinateAdjunctionComposition

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: lem-pur-coordinate-section-product-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The ordinary etale witness of an actual arrow, obtained by the canonical
bounded-below comparison Hom bijection with its specified endpoint identifications.
Source: proof Step 9 (blueprint: lem-pur-coordinate-section-product-recursion). -/
@[irreducible]
def ordinaryWitness (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.TStructure.t.plus L)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N) (α : M ⟶ N) : K ⟶ L :=
  (Equiv.ofBijective
    (fun f : K ⟶ L ↦ (VectorIntegrationSite.comparison A X).map f)
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)).symm
      (eK.hom ≫ α ≫ eL.inv)

/-- Equality in every ordinary etale witness presentation of the specified parallel
arrows. All arrows are lifted by the exact comparison Hom bijection, including
compositions and their canonical projection and adjunction comparisons.
Source: proof Step 9 (blueprint: lem-pur-coordinate-section-product-recursion). -/
def OrdinaryWitnessEquation (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α β : M ⟶ N) : Prop :=
  ∀ (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : DerivedCategory.TStructure.t.plus L)
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N),
    ordinaryWitness A X hL eK eL α = ordinaryWitness A X hL eK eL β

/-- Exact comparison preserves the uniquely specified ordinary witness arrow,
with the given endpoint identifications. Source: proof Step 9
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: apply the defining inverse property of the bounded-below comparison Hom
bijection. For Cartier factors this is realizeBoundary; exact monoidality,
proper projection comparison and bounded adjunction transposition identify the
lifts of all cup products, projection components, counits and composition maps
with their ordinary etale constructions. No unbounded full faithfulness is used. -/
theorem ordinaryWitness_compare (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hL : DerivedCategory.TStructure.t.plus L)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (eK : (VectorIntegrationSite.comparison A X).obj K ≅ M)
    (eL : (VectorIntegrationSite.comparison A X).obj L ≅ N) (α : M ⟶ N) :
    (VectorIntegrationSite.comparison A X).map (ordinaryWitness A X hL eK eL α) =
      eK.hom ≫ α ≫ eL.inv := by
  unfold ordinaryWitness
  exact (Equiv.ofBijective
    (fun f : K ⟶ L ↦ (VectorIntegrationSite.comparison A X).map f)
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)).apply_symm_apply _

private theorem compactProduct_adjunct (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let := tower_noetherian (setting P n) B aB c
    rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
      (target_plus P n _ (towerBase aB c) c) (compactProduct P n B aB c) =
        thom P n B aB c := by
  let := tower_noetherian (setting P n) B aB c
  unfold compactProduct
  exact (rightDerivedUpperShriekHomEquiv (zero B c) (unit_origin P n B)
    (target_plus P n _ (towerBase aB c) c)).apply_symm_apply _

set_option maxRecDepth 2048 in
/-- Rank-zero normalization and the two recursive identities for the actual maps.
Source: proof Steps 1--6 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: coordinate nonzerodivisors remain Cartier after adjoining or killing the
other coordinates. Pull back the first r factors. The cup coefficient map and
the proper projection at the supported coefficient unit both multiply restricted
sections, so agree, with the tensor symmetry. Naturality of projection at C_r
then gives the supported recursion. Transpose it: substitute both exceptional
counits, use their naturality, and paste them to the composite-adjunction counit.
Conjugating the compact-support compositor gives precisely the displayed
exceptional recursion. At zero, the empty product and identity adjunction give
the two identity formulas. All reordered shifts are even, with sign +1. -/
theorem coordinate_section_product_recursion (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    compactProduct P n B aB 0 = coordinateIdentity P n B ∧
    thom P n B aB 0 =
      coordinateIdentityAdjunct P n B aB ∧
    (∀ r : ℕ, compactProduct P n B aB (r + 1) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r) ∧
    ∀ r : ℕ, thom P n B aB (r + 1) =
      thom P n B aB r ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r := by
  obtain ⟨h₀, hC⟩ := coordinate_supported_product_recursion P n B aB
  refine ⟨h₀, ?_, hC, ?_⟩
  · rw [← compactProduct_adjunct P n B aB 0, h₀]
    unfold coordinateIdentityAdjunct
    rfl
  · intro r
    let := isNoetherian_of_locallyOfFiniteType aB
    let := tower_noetherian (setting P n) B aB r
    let := tower_noetherian (setting P n) B aB (r + 1)
    rw [← compactProduct_adjunct P n B aB (r + 1), hC r]
    rw [coordinateAdjunction_composition P n B aB r,
      compactProduct_adjunct P n B aB r]


/-- Arbitrary base-change identities for the actual supported product and its
specified exceptional adjunct, with canonical source and Tate identifications.
Source: proof Steps 7--9 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: every coordinate divisor pulls back to the corresponding coordinate
Cartier divisor even over a nonflat base. Cartier naturality and the cup pullback
law give the first equality. Transpose the second through the closed adjunction.
The mate's defining counit equation and naturality of closed exchange turn its
transpose into the first equality. Bijectivity gives the asserted equality of
adjuncts, without asserting invertibility of the exceptional mate. -/
theorem coordinate_section_product_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      supportedClass P n B' (g ≫ aB) c ∧
    (unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map
            (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      thom P n B' (g ≫ aB) c := by
  sorry

/-- Coordinate permutations preserve the actual map: every adjacent interchange
has Koszul sign (-1)^(2*2)=1. Source: proof Step 10
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: apply the supported cup associativity and signed symmetry laws to adjacent
factors, then the normalized Tate multiplication. Their degree is two, hence
the sign is one. The support exchange is the unique map over the zero section.
Adjacent transpositions generate all permutations. Transposition under the same
closed adjunction therefore also preserves theta and every recursion identity. -/
theorem coordinate_section_product_permutation (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (σ : Equiv.Perm (Fin c)) :
    permutedClass P n B aB c σ = supportedClass P n B aB c := by
  sorry

/-- Exponent independence is equality of the factors used in the actual recursive
product, hence also of its adjuncts and the displayed identities.
Source: proof Step 10 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: both ordinary Kummer witnesses realize the same normalized Cartier family.
The realization axiom and root-power transition identify their arrows through
the common inverse-limit Tate target. Cancelling its comparison gives the stated
equality. Substitution in product and in the fixed Hom bijections leaves all
products, section arrows, adjuncts and identities unchanged. -/
theorem coordinate_section_product_exponent (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) (i : Fin c) (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : (setting P n).Coefficient) = 0) :
    boundaryAtExponent P n B aB c i r hA = boundary P n B aB c i := by
  sorry

/-- The same recursive equations in every bounded ordinary etale witness, with
exact comparison preserving the specified arrows. The witness of a Cartier
factor is ordinaryBoundary; witnesses of cup products, proper projection,
compositors and exceptional adjuncts use the comparison Hom bijection above.
Source: proof Steps 1--6 and 9 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: ordinary closed constants and Tate lines are bounded. Their actual
Cartier maps realize boundary. Exact monoidality identifies the iterated cups,
the closed exchanges and normalized Tate multiplication. Finite proper projection
comparison identifies sectionArrow. The bounded site adjunction-transpose theorem
identifies sectionAdjunct, the pasted counits, and the conjugate compositor.
Consequently both sides of every ordinary equation realize the corresponding
specified pro-etale side. Faithfulness gives these ordinary equalities. This
argument works in every endpoint presentation and assumes no unbounded comparison
adjunction or relative supported Kunneth isomorphism. -/
theorem coordinate_section_product_ordinary (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    OrdinaryWitnessEquation (setting P n).Coefficient B
      (compactProduct P n B aB 0) (coordinateIdentity P n B) ∧
    OrdinaryWitnessEquation (setting P n).Coefficient B
      (thom P n B aB 0) (coordinateIdentityAdjunct P n B aB) ∧
    (∀ r : ℕ, OrdinaryWitnessEquation (setting P n).Coefficient
      (iteratedAffineLine B (r + 1)) (compactProduct P n B aB (r + 1))
      ((coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r)) ∧
    ∀ r : ℕ, OrdinaryWitnessEquation (setting P n).Coefficient B
      (thom P n B aB (r + 1))
      (thom P n B aB r ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B r)).map (sectionAdjunct P n B aB r) ≫
        coordinateExceptionalComposition P n B aB r) := by
  obtain ⟨h₀, hθ₀, hC, hθ⟩ := coordinate_section_product_recursion P n B aB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K L hL eK eL
    rw [h₀]
  · intro K L hL eK eL
    rw [hθ₀]
  · intro r K L hL eK eL
    rw [hC r]
  · intro r K L hL eK eL
    rw [hθ r]

/-- Ordinary witnesses of arbitrary base change, with the same closed exchange
and the specified exceptional mate. Source: proof Steps 7--9
(blueprint: lem-pur-coordinate-section-product-recursion).
Proof: coordinate Cartier pullbacks stay Cartier without flatness. Ordinary
Cartier naturality and cup pullback give the supported identity. Transpose it
through the ordinary closed adjunction: the mate is pullback of the counit
following inverse closed exchange. The defining counit equation and naturality
give the exceptional identity. Exact comparison preserves every map in that
calculation, by closed exchange and bounded site adjunction transposition. -/
theorem coordinate_section_product_ordinary_baseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    OrdinaryWitnessEquation (setting P n).Coefficient (iteratedAffineLine B' c)
      ((coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom)
      (supportedClass P n B' (g ≫ aB) c) ∧
    OrdinaryWitnessEquation (setting P n).Coefficient B'
      ((unitPullback P n g).inv ≫
        (inverseImage (setting P n).Coefficient g).map (thom P n B aB c) ≫
        coordinateExceptionalExchange P n g aB c ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map
            (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom)
      (thom P n B' (g ≫ aB) c) := by
  obtain ⟨hC, hθ⟩ := coordinate_section_product_baseChange P n g aB c
  constructor
  · intro K L hL eK eL
    rw [hC]
  · intro K L hL eK eL
    rw [hθ]

/-- Exponent and permutation independence also hold in every ordinary witness.
Source: proof Steps 9--10 (blueprint: lem-pur-coordinate-section-product-recursion).
Proof: Cartier exponent transitions fix every normalized factor. Exact comparison
identifies the ordinary factors and the cups with their realized maps. The
supported symmetry has sign (-1)^(2*2)=1; uniqueness of total-support transport
identifies the source comparison. Faithfulness yields both ordinary equalities. -/
theorem coordinate_section_product_ordinary_invariance (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (∀ σ : Equiv.Perm (Fin c), OrdinaryWitnessEquation (setting P n).Coefficient
      (iteratedAffineLine B c) (permutedClass P n B aB c σ) (supportedClass P n B aB c)) ∧
    ∀ (i : Fin c) (r : ℕ)
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : (setting P n).Coefficient) = 0),
      OrdinaryWitnessEquation (setting P n).Coefficient (iteratedAffineLine B c)
        (boundaryAtExponent P n B aB c i r hA) (boundary P n B aB c i) := by
  constructor
  · intro σ K L hL eK eL
    rw [coordinate_section_product_permutation P n B aB c σ]
  · intro i r hA K L hL eK eL
    rw [coordinate_section_product_exponent P n B aB c i r hA]

end AlgebraicGeometry.ProEtale.AffineZeroPurity

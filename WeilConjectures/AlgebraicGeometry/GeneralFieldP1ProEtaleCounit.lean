/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldCompactScalarSiteSquare
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.UnboundedCompactSupportProperComposition
public import WeilConjectures.AlgebraicGeometry.FiniteP1CoefficientSplitting
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.GeneralFieldChartAdjunctionRealization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-!
# General-field projective-line counits under finite coefficient change

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-pur-general-field-p1-proetale-counit).

The pro-etale formulas are written in finite-site coordinates. Existence of these
coordinates for every intrinsic finite-ctf input is part of the theorem, and every
presentation is allowed. The proper functor uses its trivial compactification.
The counit, right scalar comparison, splitting and geometric classes are actual
composites of the published canonical maps, with no freely chosen comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The actual compact-support site comparison, followed by the proper identification
with ordinary direct image. Source: Charts, finite-site transport
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1SiteIso (A : Type u) [CommRing A] [Finite A]
    (S : Scheme.{u})
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) (ProjectiveLine S))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (reductionCompactSupport A (𝟙 (ProjectiveLine S)) (ProjectiveLine S ↘ S)).obj
        ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj L) ≅
      (finiteCoefficientIntrinsicDerivedComparison S A).obj
        ((Etale.ordinaryFinitePushforward (ULift.{u + 1, u} A)
          (ProjectiveLine S ↘ S)).obj L) :=
  (canonicalCompactSupportSiteIso A
    (Compactification.ofIsProper (ProjectiveLine S ↘ S)) ⟨L, hL⟩).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison S A).mapIso
      ((Etale.unboundedEtaleProperCandidateIso (ULift.{u + 1, u} A)
        (ProjectiveLine S ↘ S)
        (Compactification.ofIsProper (ProjectiveLine S ↘ S))).app L)

/-- The transported Kummer-normalized actual counit. Its ordinary counit is the
inverse proper projection followed by tensor with the second-summand trace.
Source: Charts, projective-line integration and finite-site transport
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1CounitOfOrigin (A : Type u) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1, u} A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) S)
    (hG : DerivedCategory.TStructure.t.plus
      ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) :
    (reductionCompactSupport A (𝟙 (ProjectiveLine S)) (ProjectiveLine S ↘ S)).obj
        ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
          ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) ⟶
      (finiteCoefficientIntrinsicDerivedComparison S A).obj L :=
  (generalFieldP1SiteIso A S _ hG).hom ≫
    (finiteCoefficientIntrinsicDerivedComparison S A).map
      ((Etale.projectiveLineTraceDatum N hN (ULift.{u + 1, u} A) hA S hS).adjunction.counit.app L)

/-- The canonical scalar/tensor/pullback/Tate/shift comparison in site coordinates.
The Tate map is balancing on roots, not a choice of a basis or orientation.
Source: Charts, canonical right comparison
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1RightScalarOfOrigin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ)
    (hA : (N : ULift.{u + 1, u} A) = 0) (hB : (N : ULift.{u + 1, u} B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) S) :
    (scalarExtensionFunctor φ (ProjectiveLine S)).obj
        ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
          ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) ≅
      (finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) B).obj
        ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} B) N hB S).obj
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).obj L)) :=
  (canonicalSiteScalarIso φ (ProjectiveLine S)).app _ ≪≫
    (finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) B).mapIso
      (reductionEtaleP1ScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        S N hA hB hS L)

/-- Transport the normalized free rank-one splitting, using the actual proper site
comparison. Its source is the comparison image of the ordered biproduct.
Source: Charts, twisted-unit/Kummer splitting
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1SplittingOfOrigin (A : Type u) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : ULift.{u + 1, u} A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (hL : DerivedCategory.TStructure.t.plus
      ((Etale.ordinaryFiniteLine (ULift.{u + 1, u} A) N hA
        (ProjectiveLine S))⟦(2 : ℤ)⟧)) :=
  (finiteCoefficientIntrinsicDerivedComparison S A).mapIso
      (Etale.projectiveLineTraceDatum N hN (ULift.{u + 1, u} A) hA S hS).decomposition ≪≫
    (generalFieldP1SiteIso A S _ hL).symm

/-- The ordinary etale counit equation, invertibility of its proper coefficient map,
and the precise inverse-mate characterization. Source: Charts, actual counit
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def GeneralFieldP1EtaleCounit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1, u} A) = 0) (hB : (N : ULift.{u + 1, u} B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∀ (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) S),
    Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} A) S L →
    ∃ hb : IsIso ((Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ)
      (ProjectiveLine S ↘ S)).app
        ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)),
      (reductionEtaleP1ScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        S N hA hB hS L).hom =
      (Etale.projectiveLineTraceDatum N hN (ULift.{u + 1, u} B) hB S hS).adjunction.homEquiv _ _
          (@inv _ _ _ _ ((Etale.scalarMate
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ProjectiveLine S ↘ S)).app
              ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) hb ≫
            (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
              ((Etale.projectiveLineTraceDatum N hN
                (ULift.{u + 1, u} A) hA S hS).adjunction.counit.app L))

/-- The pro-etale counit square and uniqueness of its transpose, for every finite-ctf
input and every etale-origin presentation. The final scalar/site comparison identifies
the B presentation with the scalar extension of the given input.
Source: Charts, transport of counits and uniqueness of transposes
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def GeneralFieldP1ProEtaleCounit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1, u} A) = 0) (hB : (N : ULift.{u + 1, u} B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∀ K : spFiniteConstructibleTorCategory S A,
    (∃ L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) S,
      Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} A) S L ∧
        Nonempty ((finiteCoefficientIntrinsicDerivedComparison S A).obj L ≅ K.obj)) ∧
    ∀ (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) S)
      (_hL : Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} A) S L)
      (η : (finiteCoefficientIntrinsicDerivedComparison S A).obj L ≅ K.obj),
      ∃ (hGA : DerivedCategory.TStructure.t.plus
          ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L))
        (hGB : DerivedCategory.TStructure.t.plus
          ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} B) N hB S).obj
            ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).obj L))),
      IsIso ((reductionDirectImageComparison φ (𝟙 (ProjectiveLine S))
        (ProjectiveLine S ↘ S)).app
          ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
            ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L))) ∧
      ∀ b : (scalarExtensionFunctor φ (ProjectiveLine S)).obj
          ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
            ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) ⟶
        (finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) B).obj
          ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} B) N hB S).obj
            ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).obj L)),
        ((reductionDirectImageComparison φ (𝟙 (ProjectiveLine S))
            (ProjectiveLine S ↘ S)).app
            ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
              ((Etale.ordinaryFiniteP1Right (ULift.{u + 1, u} A) N hA S).obj L)) ≫
          (reductionCompactSupport B (𝟙 (ProjectiveLine S)) (ProjectiveLine S ↘ S)).map b ≫
          generalFieldP1CounitOfOrigin B N hN hB S hS _ hGB ≫
          (canonicalSiteScalarIso φ S).inv.app L ≫
          (scalarExtensionFunctor φ S).map η.hom =
        (scalarExtensionFunctor φ S).map
          (generalFieldP1CounitOfOrigin A N hN hA S hS L hGA ≫ η.hom)) ↔
        b = (generalFieldP1RightScalarOfOrigin φ N hA hB S hS L).hom

/-- Scalar extension of an etale-origin object, followed by its specified ordinary
coefficient identification. Source: Charts, scalar/site square and balanced endpoints
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1ScalarOfOrigin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    {L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T}
    {M : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T}
    (e : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).obj L ≅ M) :
    (scalarExtensionFunctor φ T).obj
        ((finiteCoefficientIntrinsicDerivedComparison T A).obj L) ≅
      (finiteCoefficientIntrinsicDerivedComparison T B).obj M :=
  (canonicalSiteScalarIso φ T).app L ≪≫
    (finiteCoefficientIntrinsicDerivedComparison T B).mapIso e

/-- The ordinary Kummer class of O(Delta), the dual of the diagonal ideal.
Source: Charts, diagonal class on the projective-line square
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def generalFieldP1DiagonalClass (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤))) :=
  Etale.ordinaryFiniteFirstChern A N hA _ hW
    (@Scheme.Pic.ofIsInvertible _
      (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)
      (Etale.projectiveLine_diagonal_ker_isInvertible S).isInvertible_dual_toModules)

/-- The free splitting and diagonal Kummer morphism commute with scalar extension
on both sites. Endpoints are the existing generator-normalized multiplication and
Tate balancing maps. Source: Charts, Kummer and diagonal classes and free summands
(blueprint: lem-pur-general-field-p1-proetale-counit). -/
def GeneralFieldP1GeometricClasses
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1, u} A) = 0) (hB : (N : ULift.{u + 1, u} B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∀ (eS : Etale.P1KummerScalarEndpoints (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        N hA hB S)
    (eP : Etale.P1KummerScalarEndpoints (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        N hA hB (ProjectiveLine S)),
    ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
        (Etale.projectiveLineTraceDatum N hN (ULift.{u + 1, u} A) hA S hS).decomposition.hom ≫
      (Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteLine (ULift.{u + 1, u} A) N hA
            (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (Etale.ordinaryFinitePushforward (ULift.{u + 1, u} B)
        (ProjectiveLine S ↘ S)).map eP.shiftedLineIso.hom =
    biprod.lift
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
          biprod.fst ≫ eS.shiftedLineIso.hom)
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
          biprod.snd ≫ eS.unitIso.hom) ≫
      (Etale.projectiveLineTraceDatum N hN (ULift.{u + 1, u} B) hB S hS).decomposition.hom) ∧
    (∃ (hLA : DerivedCategory.TStructure.t.plus
          ((Etale.ordinaryFiniteLine (ULift.{u + 1, u} A) N hA
            (ProjectiveLine S))⟦(2 : ℤ)⟧))
        (hLB : DerivedCategory.TStructure.t.plus
          ((Etale.ordinaryFiniteLine (ULift.{u + 1, u} B) N hB
            (ProjectiveLine S))⟦(2 : ℤ)⟧)),
      (scalarExtensionFunctor φ S).map
          (generalFieldP1SplittingOfOrigin A N hN hA S hS hLA).hom ≫
        (reductionDirectImageComparison φ (𝟙 (ProjectiveLine S))
          (ProjectiveLine S ↘ S)).app
            ((finiteCoefficientIntrinsicDerivedComparison (ProjectiveLine S) A).obj
              ((Etale.ordinaryFiniteLine (ULift.{u + 1, u} A) N hA
                (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
        (reductionCompactSupport B (𝟙 (ProjectiveLine S)) (ProjectiveLine S ↘ S)).map
          (generalFieldP1ScalarOfOrigin φ (ProjectiveLine S) eP.shiftedLineIso).hom =
      (canonicalSiteScalarIso φ S).hom.app _ ≫
        (finiteCoefficientIntrinsicDerivedComparison S B).map
          (biprod.lift
            ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
              biprod.fst ≫ eS.shiftedLineIso.hom)
            ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S).map
              biprod.snd ≫ eS.unitIso.hom)) ≫
        (generalFieldP1SplittingOfOrigin B N hN hB S hS hLB).hom) ∧
    ∀ (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
          (ProjectiveLine S ↘ S), ⊤)))
      (eW : Etale.P1KummerScalarEndpoints (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        N hA hB (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))),
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ)
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))).map
          (generalFieldP1DiagonalClass (ULift.{u + 1, u} A) N hA S hW) ≫
        eW.shiftedLineIso.hom =
      eW.unitIso.hom ≫ generalFieldP1DiagonalClass (ULift.{u + 1, u} B) N hB S hW) ∧
      ((scalarExtensionFunctor φ
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))).map
          ((finiteCoefficientIntrinsicDerivedComparison
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) A).map
              (generalFieldP1DiagonalClass (ULift.{u + 1, u} A) N hA S hW)) ≫
        (generalFieldP1ScalarOfOrigin φ _ eW.shiftedLineIso).hom =
      (generalFieldP1ScalarOfOrigin φ _ eW.unitIso).hom ≫
        (finiteCoefficientIntrinsicDerivedComparison
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) B).map
            (generalFieldP1DiagonalClass (ULift.{u + 1, u} B) N hB S hW))

/-- General-field projective-line counit, its inverse-mate characterization, and its
geometric normalizations, on both the etale and pro-etale finite-ctf domains.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts;
det-sp-trace-basic, Proof (2)
(blueprint: lem-pur-general-field-p1-proetale-counit).

Proof: (1) Finite type over k gives Noetherian schemes and p unequal to ell makes
N invertible. The chart-realization theorem gives finite-site origins and the
canonical right-functor identification, retaining all Tor intervals even for nonflat
coefficient maps. (2) Apply lem-pur-ordinary-chart-p1-counit-scalar to the actual
Kummer-normalized ordinary counits. The free splitting and diagonal class identities
are lem-sp-finite-p1-coefficient-splitting, with the normalized Tate and unit endpoints.
(3) Use the chart-realization counit formula and the compact scalar/site square of
lem-pur-general-field-compact-scalar-site-square. Their right comparison is the
balanced scalar/tensor/pullback/shift composite by its root-generator normalization.
(4) Paste the two squares: the ordinary counit equation gives the pro-etale one;
the same pasting at the Tate line and the unit transports the splitting. Apply the
scalar/site comparison to the ordinary diagonal class identity. Naturality transports
the equation through every etale-origin presentation. (5) Proper finite coefficient
comparison makes beta invertible on the etale side, and the compact scalar/site
square gives its pro-etale invertibility. Cancel beta and use the adjunction Hom
bijection to obtain exactly the inverse-mate formula and uniqueness of the transpose.
-/
theorem generalFieldP1ProEtaleCounit
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (_hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ)
    (hA : ((ell ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
    (hB : ((ell ^ n : ℕ) : ULift.{u + 1, u} B) = 0) :
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType (S ↘ Spec (.of k))
    ∃ hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)),
      GeneralFieldP1EtaleCounit φ (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
        hA hB S hS ∧
      GeneralFieldP1ProEtaleCounit φ (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
        hA hB S hS ∧
      GeneralFieldP1GeometricClasses φ (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
        hA hB S hS := by
  sorry

end AlgebraicGeometry.ProEtale

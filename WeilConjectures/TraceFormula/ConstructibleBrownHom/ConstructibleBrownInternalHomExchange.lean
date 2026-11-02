/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Compactification.Dense
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement

/-!
# Constructible Brown exceptional internal-Hom exchange

Source: current DAG lem-trf-exceptional-internal-hom-exchange, statement and proof,
with the November 2 general finite-coefficient repair (Wei Yang #3 and #19).
Blueprint: sec-trace-formula/sk-d-trace-class/lem-trf-exceptional-internal-hom-exchange.
(blueprint: lem-trf-exceptional-internal-hom-exchange).

All categories are the recorded ordinary derived categories of internal modules over
pulled-back condensed coefficients. The Brown adjunction is only on the constructible
finite-Tor full subcategories. The comparison is specified by the actual compactification
projection, evaluation, and the counit of that adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.ConstructibleBrownHom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ordinary ambient module-derived category already used by the dependencies.
Source: sk-def-localizing-closure, ambient category
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
abbrev Ambient (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))

/-- The existing finite constant-model constructible finite-Tor predicate.
Source: sk-def-sfb-constructible, final paragraph
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
abbrev ctf (T : Scheme.{u}) : ObjectProperty (Ambient Λ T) :=
  constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K

/-- Both inputs of the existing ambient derived internal Hom.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
abbrev hom (T : Scheme.{u}) := Functor.uncurry.obj (derivedHom Λ T)

/-- Packaging of the restricted Brown adjunction of sk-thm-existence (2)--(4).
The lower functor is identified on both objects and morphisms with the actual
compactification composite; no ambient exceptional adjoint is postulated.
Source: sk-thm-existence, restricted adjunction
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
structure BrownAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  lower : (ctf Λ X).FullSubcategory ⥤ (ctf Λ Y).FullSubcategory
  lowerIso : lower ⋙ (ctf Λ Y).ι ≅
    (ctf Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c
  upper : (ctf Λ Y).FullSubcategory ⥤ (ctf Λ X).FullSubcategory
  adjunction : lower ⊣ upper

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The source bifunctor RHom(Lf*M,f!N), with ordinary first variable.
Source: displayed comparison of the item
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
def source (B : BrownAdjunction Λ c) :
    (ctf Λ Y).FullSubcategoryᵒᵖ × (ctf Λ Y).FullSubcategory ⥤ Ambient Λ X :=
  (((ctf Λ Y).ι ⋙ (upperStar Λ f).leftDerivedFunctor).op.prod
    (B.upper ⋙ (ctf Λ X).ι)) ⋙ hom Λ X

/-- The internal Hom of the two constructible inputs, in the original ambient category.
Source: right side of the displayed comparison, before exceptional pullback
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
def baseHom :
    (ctf Λ Y).FullSubcategoryᵒᵖ × (ctf Λ Y).FullSubcategory ⥤ Ambient Λ Y :=
  ((ctf Λ Y).ι.op.prod (ctf Λ Y).ι) ⋙ hom Λ Y

/-- The target bifunctor f!RHom(M,N). Its membership proof merely restricts the
recorded internal Hom to its constructible domain.
Source: right side of the displayed comparison
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
def target (B : BrownAdjunction Λ c)
    (hQ : ∀ P, ctf Λ Y ((baseHom Λ).obj P)) :
    (ctf Λ Y).FullSubcategoryᵒᵖ × (ctf Λ Y).FullSubcategory ⥤ Ambient Λ X :=
  (ctf Λ Y).lift (baseHom Λ) hQ ⋙ B.upper ⋙ (ctf Λ X).ι

/-- The published Koszul braiding of the ordinary derived module category.
Source: derived tensor symmetry, used only for the evaluation order
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
@[instance_reducible]
def braiding (T : Scheme.{u}) : BraidedCategory (Ambient Λ T) :=
  DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))

/-- The actual evaluation/projection/counit pairing, in left-tensor order.
The two lowerIso components only express the restricted lower shriek in the
ambient category. All other arrows are the published canonical constructions.
Source: item proof step 3, displayed double-transpose normalization
(blueprint: lem-trf-exceptional-internal-hom-exchange). -/
def pairing (B : BrownAdjunction Λ c)
    (M N : (ctf Λ Y).FullSubcategory)
    (hH : ctf Λ X ((source Λ B).obj (op M, N))) :
    M.obj ⊗ (B.lower.obj ⟨(source Λ B).obj (op M, N), hH⟩).obj ⟶ N.obj :=
  ((braiding Λ Y).braiding M.obj (B.lower.obj ⟨_, hH⟩).obj).hom ≫
    (B.lowerIso.hom.app ⟨_, hH⟩ ▷ M.obj) ≫
    exceptionalProjectionMorphismOfCompactification Λ c
      ((source Λ B).obj (op M, N)) M.obj ≫
    (rightDerivedLowerShriekOfCompactification Λ c).map
      (((braiding Λ X).braiding ((source Λ B).obj (op M, N))
          ((upperStar Λ f).leftDerivedFunctor.obj M.obj)).hom ≫
        (ihom.ev ((upperStar Λ f).leftDerivedFunctor.obj M.obj)).app
          (B.upper.obj N).obj) ≫
    B.lowerIso.inv.app (B.upper.obj N) ≫ (B.adjunction.counit.app N).hom

/-- The canonical exceptional exchange, natural contravariantly in M and covariantly
in N, for every finite commutative ell-primary coefficient ring. The existential
membership witnesses are conclusions, not admissibility assumptions. Nonemptiness
supplies the constructible Brown adjunction; the exchange applies to every such
adjunction and is uniquely fixed by the evaluation/counit double transpose.

Source: current item statement and its four-step DAG proof, with the November 2
arbitrary finite-A repair, Wei Yang #3 and #19
(blueprint: lem-trf-exceptional-internal-hom-exchange).

Proof: sk-thm-existence restricts the Brown adjunction to Dctf over the algebraically
closed base. Pullback and tensor preserve Dctf. Independent stratified internal-Hom
preservation puts Q=RHom(M,N) and H=RHom(Lf*M,f!N) in Dctf. For each test P in Dctf,
tensor-Hom, the Brown adjunction, the projection formula, tensor-Hom, and Brown give
Hom(P,H) equiv Hom(P,f!Q), naturally in every variable. Finite A is Noetherian,
and finite-Tor etale comparison checks the domain of the earlier projection formula.
Yoneda on Dctf takes the identity of H to the comparison, and the inverse image
of the identity of f!Q is its inverse. Unwinding this image gives precisely pairing,
first transposed by tensor-Hom and then by the restricted Brown adjunction.
Naturality of each bijection gives the asserted bifunctor isomorphism; fullness
makes the normalization an equality of original ambient derived morphisms.
-/
theorem exceptionalInternalHomExchange
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (_hA : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : A) = 0)
    {C Z : Over (Spec (.of D.k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : C ⟶ Z) :
    Nonempty (BrownAdjunction (Profinite.continuousCoefficientRingObj A)
      (compactificationOverField g)) ∧
      ∀ B : BrownAdjunction (Profinite.continuousCoefficientRingObj A)
          (compactificationOverField g),
        ∃ (hQ : ∀ P, ctf (Profinite.continuousCoefficientRingObj A) Z.left
            ((baseHom (Profinite.continuousCoefficientRingObj A)).obj P))
          (hH : ∀ P, ctf (Profinite.continuousCoefficientRingObj A) C.left
            ((source (Profinite.continuousCoefficientRingObj A) B).obj P)),
          ∃! e : source (Profinite.continuousCoefficientRingObj A) B ≅
              target (Profinite.continuousCoefficientRingObj A) B hQ,
            ∀ M N : (ctf (Profinite.continuousCoefficientRingObj A) Z.left).FullSubcategory,
              e.hom.app (op M, N) =
                (B.adjunction.homEquiv
                  ⟨(source (Profinite.continuousCoefficientRingObj A) B).obj (op M, N),
                    hH (op M, N)⟩
                  ⟨(baseHom (Profinite.continuousCoefficientRingObj A)).obj (op M, N),
                    hQ (op M, N)⟩
                  (ObjectProperty.homMk (curry
                    (pairing (Profinite.continuousCoefficientRingObj A) B M N
                      (hH (op M, N)))))).hom := by
  sorry

/-- The warning in the statement: the analogous universal formula with exceptional
pullback in both variables is false for an allowed coefficient ring. As in DAG proof
step 4, one allowed coefficient example suffices, and the cited finite-coefficient
purity theorem is used only within its coefficient scope, at A = F_ell = A_(Q_ell,1).
The zero ring stays allowed in exceptionalInternalHomExchange.

Source: item statement, last sentence, and DAG proof step 4
(blueprint: lem-trf-exceptional-internal-hom-exchange).

Proof: take A = F_ell (lifted to Type u, with the discrete topology), within the
distinguished family of def-trf-coefficient-conventions; it is finite, killed by ell,
and nonzero. Use the affine line over D.k mapping to Spec D.k, and M=N=A in degree zero.
The Brown adjunction exists by sk-thm-existence. Finite-coefficient smooth purity
identifies g!A with A(1)[2]. Since D.k is algebraically closed, a primitive ell-th
root of unity trivializes A(1). Closed tensor-Hom identifies RHom(A,A) with A, and
cancellation of equal shifts gives RHom(g!A,g!A) isomorphic to A. In contrast,
g!RHom(A,A) is A(1)[2]. The nonzero cohomology occurs in degree zero in the former
and degree minus two in the latter, so cohomology rules out an isomorphism. Both
schemes are separated and finite type.
-/
theorem exceptionalFirstVariableFails
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p) :
    ¬ (∀ (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
      [DiscreteTopology A] [IsTopologicalRing A],
      (∃ n : ℕ, 0 < n ∧ (ℓ ^ n : A) = 0) →
      ∀ (C Z : Over (Spec (.of D.k)))
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
      (g : C ⟶ Z)
      (B : BrownAdjunction (Profinite.continuousCoefficientRingObj A)
        (compactificationOverField g))
      (M N : (ctf (Profinite.continuousCoefficientRingObj A) Z.left).FullSubcategory),
      ∃ hQ : ctf (Profinite.continuousCoefficientRingObj A) Z.left
          ((baseHom (Profinite.continuousCoefficientRingObj A)).obj (op M, N)),
        Nonempty ((hom (Profinite.continuousCoefficientRingObj A) C.left).obj
          (op (B.upper.obj M).obj, (B.upper.obj N).obj) ≅
            (B.upper.obj
              ⟨(baseHom (Profinite.continuousCoefficientRingObj A)).obj (op M, N), hQ⟩).obj)) := by
  sorry

end WeilConjectures.ConstructibleBrownHom

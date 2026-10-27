/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation

import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.RationalCoefficientCategoryComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.Triangulated.BoundedPostnikovTower
import Sheaf.AlgebraicGeometry.ConstructibleModuleObjectsEssentiallySmall
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Triangulated.ExtensionProductEssentiallySmall
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarFunctionCoefficients
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Ordinary realization in locally finite adic modules

Source: Bhatt--Scholze, Section 6.8, Lemma 6.8.2, Definitions 6.8.3 and 6.8.8,
and Proposition 6.8.14; blueprint main-20261015, common-field passage in
`cor-coef-verdier-weil-equivariance.proof.md`.
(blueprint: lem-sf-locally-finite-adic-constructible-realization).

The source is the published common-field pair category with raw rational finite stages.
The target is the framework's ordinary derived category of the native internal modules
(its Grothendieck-abelian derived localization), with the existing full bounded
constructible subcategory `ProEtale.DerivedCategory.boundedAdicConstructible`.
The coefficient presentations below specify
actual inverse-limit and localization maps, and the integral comparison specifies
realization on all morphisms, hence on fractions as well as integral numerators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The native locally finite coefficient ring, read in abelian sheaves.
Source: Bhatt--Scholze, 6.8.1--6.8.2, native coefficient specialization
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
abbrev abRing :=
  (ProEtale.weilCoefficientsForgetAb l X).obj (ProEtale.adicConstantSheaf l X)

/-- The sectionwise ring of the native internal coefficient. Its underlying sections
are exactly the same locally finite continuous functions, with pointwise operations.
Source: Bhatt--Scholze, 6.8.1--6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def ringSheaf [IsCommMonObj (abRing l X)] :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology X) (abRing l X)

/-- The canonical section-module functor, retaining the native module action.
Source: internal-module convention of def-sf-native-weil-derived-framework and
Bhatt--Scholze, 6.8.1
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def sections [IsCommMonObj (abRing l X)] :=
  ProEtale.AdicSheaf.forgetAb l X ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) (abRing l X)).functor

/-- The specified finite-field inclusion, undoing only the published size transport.
Source: common finite-field convention and Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def embedding (E : Index l (PadicAlgCl l)) :
    Coefficient.{u} l (PadicAlgCl l) E →ₐ[Padic l] PadicAlgCl l :=
  E.val.val.comp (Shrink.algEquiv (Padic l) E.val).toAlgHom

/-- The inverse-limit and localization identifications used in one integral formula.
All ring maps are fixed pointwise, and all finite-quotient isomorphisms fix constants.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure CoefficientPresentation [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) where
  integral : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ≅
    completedIntegralCommRingSheafUnrestricted l E X
  finite : ∀ n : ℕ,
    integralCoefficientCommRingSheaf l E X n ≅
      finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : finiteCoefficientRing l E n)
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (finiteCoefficientRing l E n))).app U a)) x = a
  integral_residues : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l
        E X n ≫ (finite n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  localization : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  localization_normalized : integralCoefficientLocalizationNormalized l
    E X localization.hom
  integralInclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l X
      E ⟶
    rationalCoefficientSheaf l X E
  integralInclusion_normalized : integralRationalCoefficientNormalized l
    E X integralInclusion
  rationalInclusion : rationalCoefficientSheaf l X E ⟶
    ringSheaf l X
  rationalInclusion_normalized : ∀ (U : X.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X
        E).obj.obj U) (x : U.unop.left),
    (rationalInclusion.hom.app U s).down.1 x =
      i (rationalCoefficientValue l E X U s x)

/-- The actual structural ring map B_integral to B_native. It is the composite of the
normalized completion identification, integral inclusion and finite-field inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def CoefficientPresentation.integralMap [IsCommMonObj (abRing l X)]
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {i : E →ₐ[Padic l] PadicAlgCl l} (C : CoefficientPresentation l X E i) :
    completedIntegralCommRingSheafUnrestricted l
      E X ⟶ ringSheaf l X :=
  C.integral.inv ≫ C.integralInclusion ≫ C.rationalInclusion

/-- One ordinary realization, with its exact essential image and full derived Hom
bijections. The comparison to the universal derived tensor functor is natural on
integral arrows; functoriality then sends inverse uniformizer powers to their inverses.
The common-stage category already uses balanced extension and eventual equality of
representatives, so its arrows, including arrows between different finite stages, are
realized by the same functor. The `common_field` equation fixes its transition
isomorphisms by the canonical completion map and balanced derived tensor associator;
HEq retains the published literal-object transports instead of selecting new isomorphisms.
Source: Bhatt--Scholze, Proposition 6.8.14 and the native smallness addendum
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure RealizationCore where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X
  J : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
    DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
    ∃ A, Nonempty (J.obj A ≅ K)
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
        J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((coefficient E).integralMap l X)
  sourceSmall : EssentiallySmall.{u + 1}
    (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
  targetSmall : EssentiallySmall.{u + 1}
    (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory

/-- The specific completion map, read through the canonical derived tensor presentation.
This is the published map characterized by its quotient-completion chain map and counit.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def completedTensorComparison
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) :
    pbcDerivedExtend.{u} (completedCoefficientMap l E L i X) ⟶
      integralScalarExtensionOfUniverses l E L i X :=
  completedScalarComparison l E L i X

/-- The common-field identification is the specified completion and balanced-tensor map.
Source: Bhatt--Scholze, Proposition 6.8.14, and the completion-map scalar comparison
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
def commonField (R : RealizationCore l X) : Prop :=
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
          (R.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨E, (sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom)))
      ((R.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((R.coefficient L).integralMap l X) ((R.coefficient E).integralMap l X)
          (R.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((R.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (R.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- A realization with its canonical common-field transition normalization.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-constructible-realization). -/
structure Realization extends RealizationCore l X where
  common_field : commonField l X toRealizationCore

/-- Ordinary common-field constructible realization in the native locally finite adic
coefficient sheaf, for every finite-type scheme over the chosen algebraic closure.
No separatedness is required and no individual finite stage is asserted equivalent.
Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.3 and 6.8.8, Proposition 6.8.14;
blueprint common-field passage in cor-coef-verdier-weil-equivariance.proof.md
(blueprint: lem-sf-locally-finite-adic-constructible-realization).

Proof:
1. The geometric point is Noetherian. Finite type gives Noetherian X and finite
Krull dimension, with l invertible, using lem-weil-pbc-finite-type-over-noetherian
and lem-kun-dimension-finite-type. Every locally closed stratum has these properties.
2. The condensed coefficient of prop-weil-pbc-qbar-condensed-two-colimit is the
sheafification of functions valued in one finite coefficient field, by
lem-weil-pbc-condensed-qbar-function-coefficients. A finite-dimensional Q_l-span lies
in the finite field generated by a basis. Thus sheafification is the native locally
finite function sheaf, compatibly with every finite-field inclusion. The finite
coefficient identifications are those of lem-weil-pbc-continuous-coefficient-realizations
and lem-per-continuous-rational-derived-realization.
3. Forgetting the restricted constant-field action identifies the native internal
modules with modules in abelian sheaves: the unit fixes that action and the tensor
action factors through the balanced quotient. Apply
 def-weil-pbc-internal-abelian-sheaf-module-equivalence and
lem-weil-sheaf-scalar-extension-ring-iso, then
lem-weil-pbc-exact-functor-derived-factorization. The two lfp-local-triviality lemmas
identify constructibility. A finite open cover globalizes the local stratifications
by partitioning into U_i minus the preceding opens and restricting the strata.
4. At finite E, lem-per-continuous-rational-derived-realization supplies the normalized
raw realization on all derived Homs. The integral-stratified-perfect characterization
identifies its integral domain. The coefficient-category-comparison supplies the
identity equivalences between the two raw presentations and their completion-map
scalar comparisons. At field coefficients finite Tor means this same category.
5. Compose these comparisons with lem-per-rational-realization-scalar-coherence and
lem-weil-pbc-condensed-flat-coefficient-calculus. The ringed derived monoidal comparisons
identify iterated extension with B_native tensor over B_integral: flatten
b tensor (e tensor k) to be tensor k. The inverse inserts one. Completion comparisons
and these balanced associators respect identity and successive field extension,
including ramification. They therefore descend to the pair category. Integral
naturality and inversion send a fractional arrow to the same inverse uniformizer
power times its numerator. Common-field representatives give identity and composition.
6. Finite-field full faithfulness identifies each stage Hom with its realized derived
Hom. The transition maps agree by step 5. The Hom-colimit bijection of
prop-weil-pbc-qbar-condensed-two-colimit gives full faithfulness at Omega, also after
every integer shift, so this is not merely a comparison of hearts.
7. Descend a target object to finite E by that two-colimit theorem, then lift through
the finite-E equivalence. Tensor transitivity gives the required image. Common-field
triangles remain distinguished, and full faithfulness lifts every target cone.
8. The constructible-module essential-smallness theorem gives a small family of
cohomology objects. Bounded Postnikov towers use finitely many shifted members.
The small-extension-classes theorem bounds their extension objects by small Hom sets.
Taking the union over all finite integer intervals gives target essential smallness.
Preimages of these representatives under the established equivalence give source
essential smallness in the same site/coefficient universe. -/
theorem locally_finite_adic_constructible_realization
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k]
    [Algebra k₀ k] [IsAlgClosure k₀ k]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k₀)
    (T : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    Nonempty (Realization l T.left) := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization

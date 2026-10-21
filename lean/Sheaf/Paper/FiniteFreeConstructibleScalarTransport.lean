/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.FiniteFreeCoefficientTransport
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Finite-free transport of integral constructible local models

Source: blueprint main-20261015, prop-weil-pbc-scalar-extension, exactness clause;
Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 05CF, 08H3 and 03EL
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).

The coefficient rings are the actual valuation rings. Every auxiliary comparison is
fixed by quotient projections, tensor sections, or the published derived counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
-- Avoid underdetermined max-universe instances from the auxiliary operations framework.
-- The fixed-size PBC instances still provide the same canonical structures.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E F : Type (u + 1)) [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  (i : E →ₐ[Padic l] F)

/-- The existing algebraic extension functor, in the coefficient universe.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
abbrev finiteFreeCoefficientExtension :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l F) :=
  ModuleCat.extendScalars (WeilConjectures.integralScalarIntegerInclusion l E F i)

/-- Additivity inherited from the existing extension/restriction adjunction.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
instance finiteFreeCoefficientExtension_additive :
    (finiteFreeCoefficientExtension l E F i).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E F i)).left_adjoint_additive

/-- The literal termwise B tensor_A P, with differential 1 tensor d_P.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
abbrev finiteFreeCoefficientComplex :=
  (finiteFreeCoefficientExtension l E F i).mapHomologicalComplex (.up ℤ)

/-- A pure section r tensor p in the published completed constant realization.
Source: Bhatt--Scholze 6.6.11; Stacks 03EK
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantTensor (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (N : ModuleCat.{u + 1} A) (U : T.ProEtᵒᵖ)
    (r : (pbcAdicCompletion T d).obj.obj U) (p : N) :
    ((integralConstantModule T d).obj N).val.obj U :=
  adicDatumTensorSection T
    (adicDatumScalar T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite })
    ((adicLisseConstantModules T A).obj N) U
    ((pbcCompletedComparison T d).inv.hom.app U r)
    (completedConstantGenerator T A N U p)

/-- The ordinary balancing isomorphism, specified on all tensor generators.
The formula is ((r tensor p) tensor s) ↦ c(r)s tensor (1 tensor p).
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).
Proof: the displayed balanced section formula has inverse
s tensor (b tensor p) ↦ (1 tensor p) tensor sb. The A-balancing holds since the
coefficient square commutes; R- and B-balancing move their scalars into S. Both
composites are the identity. Sheafification gives inverse module maps, natural in
N and in restriction. These local generators determine the transformation uniquely. -/
theorem finiteFreeConstantBalance_existsUnique (T : Scheme.{u}) :
    ∃! b : integralConstantModule T (pbcPadicCoefficientDatum l E) ⋙
        pbcExtend (finiteFreeCompletedCoefficientMap l E F i T) ≅
      finiteFreeCoefficientExtension l E F i ⋙
        integralConstantModule T (pbcPadicCoefficientDatum l F),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)).obj.obj U)
        (s : (pbcAdicCompletion T (pbcPadicCoefficientDatum l F)).obj.obj U) (p : N),
        (b.hom.app N).val.app U
          (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
            ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N) U s
            (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N U r p)) =
          finiteFreeConstantTensor T (pbcPadicCoefficientDatum l F) _ U
            ((finiteFreeCompletedCoefficientMap l E F i T).hom.app U r * s)
            ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              WeilConjectures.integralScalarIntegerInclusion l E F i] p) := by
  sorry

/-- The balancing fixed by the preceding pure-tensor formula, rather than a chosen model.
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantBalance (T : Scheme.{u}) :=
  (finiteFreeConstantBalance_existsUnique l E F i T).exists.choose

/-- Apply the specified balancing degreewise to complexes.
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantComplexBalance (T : Scheme.{u}) :=
  Functor.mapHomologicalComplexCompIso
    (F := integralConstantModule T (pbcPadicCoefficientDatum l E))
    (G := pbcExtend (finiteFreeCompletedCoefficientMap l E F i T)) (Iso.refl _) (.up ℤ) ≪≫
  NatIso.mapHomologicalComplex (finiteFreeConstantBalance l E F i T) (.up ℤ) ≪≫
  (Functor.mapHomologicalComplexCompIso
    (F := finiteFreeCoefficientExtension l E F i)
    (G := integralConstantModule T (pbcPadicCoefficientDatum l F)) (Iso.refl _) (.up ℤ)).symm

/-- The localization factorization for the published completed constant realization.
Source: Bhatt--Scholze 6.6.11
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantFactors (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    completedConstantQ (ModuleCat.{u + 1} A) ⋙ integralConstantDerived T d ≅
      (integralConstantModule T d).mapHomologicalComplex (.up ℤ) ⋙
        (DerivedCategory.Q.{u + 2, u + 1, u + 2}
          (C := pbcModules T (pbcAdicCompletion T d))) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategoryFactors.{u + 2, u + 2,
    u + 1, u + 1, u + 2, u + 2}

/-- The canonical derived model map: localization factorization, K-flat counit,
ordinary balancing, and the inverse target realization factorization, in that order.
Source: Stacks 06YY and 08H3; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeDerivedModelMap (T : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    (finiteFreeCompletedScalar l E F i T).obj
        ((integralConstantDerived T (pbcPadicCoefficientDatum l E)).obj
          ((completedConstantQ _).obj P)) ⟶
      (integralConstantDerived T (pbcPadicCoefficientDatum l F)).obj
        ((completedConstantQ _).obj ((finiteFreeCoefficientComplex l E F i).obj P)) :=
  (finiteFreeCompletedScalar l E F i T).map
      ((finiteFreeConstantFactors T (pbcPadicCoefficientDatum l E)).hom.app P) ≫
    pbcComplexCounit (finiteFreeCompletedCoefficientMap l E F i T)
      (((integralConstantModule T (pbcPadicCoefficientDatum l E)).mapHomologicalComplex
        (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((finiteFreeConstantComplexBalance l E F i T).hom.app P) ≫
    (finiteFreeConstantFactors T (pbcPadicCoefficientDatum l F)).inv.app
      ((finiteFreeCoefficientComplex l E F i).obj P)

/-- Transport a specified local model, using the normalized restriction comparison,
then scalar extension of that very isomorphism, then the displayed balancing map.
Source: Bhatt--Scholze 6.6.11; Stacks 03EL, 06YY and 08H3
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeLocalModelMap {X T : Scheme.{u}} (g : X ⟶ T)
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (e : (pbcActualDerivedPull g (pbcPadicCoefficientDatum l E)).obj K ≅
      (integralConstantDerived X (pbcPadicCoefficientDatum l E)).obj
        ((completedConstantQ _).obj P)) :
    (pbcActualDerivedPull g (pbcPadicCoefficientDatum l F)).obj
        ((finiteFreeCompletedScalar l E F i T).obj K) ⟶
      (integralConstantDerived X (pbcPadicCoefficientDatum l F)).obj
        ((completedConstantQ _).obj ((finiteFreeCoefficientComplex l E F i).obj P)) :=
  (finiteFreeScalarRestriction l E F i g).hom.app K ≫
    (finiteFreeCompletedScalar l E F i X).map e.hom ≫
    finiteFreeDerivedModelMap l E F i X P

/-- Finite-free coefficient extension preserves the full integral constructible category
and transports the specified finite-projective models on the same strata and covers.

Source: blueprint main-20261015, prop-weil-pbc-scalar-extension, exactness clause;
Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 05CF, 08H3 and 03EL
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).

Proof: apply the forward integral stratified-perfect characterization to K to obtain
finite strata and pro-etale covering members with bounded finite-projective A-models.
For the precise assertion start with the supplied strata and isomorphism e instead.
In every degree choose finitely many generators of P and split the resulting finite
free surjection by projectivity. Tensor both splitting maps with B. Their composite
is still the identity; hence every B tensor_A P term is finite projective. Zero
terms remain zero, so the same interval [a,b] works, including the zero complex.
On the chosen stratum and its covering member, the completed coefficient comparison
identifies the inverse-image coefficients with the completed rings. Equivalently
work on the small pro-etale site of that covering scheme, canonically equivalent
to the slice site. The scalar coefficient square commutes at every finite quotient,
so it commutes at the limit. The published K-flat-normalized scalar/pullback
comparison therefore identifies restriction of C(K) with C of the restriction.
The strict-perfect pullback model computes the completed realization of P by its
termwise tensor complex and proves that complex K-flat; this is projectivity of
its coefficient modules, not projectivity in the global sheaf category.
Apply scalar extension to the supplied e. The universal K-flat counit, followed
by the ordinary balancing, identifies its model with S tensor_B (B tensor_A P).
The balancing is exactly ((r tensor p) tensor s) ↦ c(r)s tensor (1 tensor p),
with inverse s tensor (b tensor p) ↦ (1 tensor p) tensor sb. Its section formulas
respect balancing, restrictions and differentials. Thus finiteFreeLocalModelMap
is an isomorphism and retains the original model isomorphism, strata and covers.
Finally the reverse stratified-perfect characterization over B proves all three
membership conditions: intrinsic completeness, uniform bounded constructible
reductions with common models, and compatible etale-origin witnesses. -/
theorem finiteFreeConstructibleScalarTransport (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n) (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K) :
    PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l F)
        ((finiteFreeCompletedScalar l E F i T).obj K) ∧
      ∀ (s : FiniteLocallyClosedStratification T)
        (V : ∀ k : Fin s.n, Sieve (⊤_ (s.domain k).ProEt)),
        (∀ k : Fin s.n, V k ∈ ProEt.topology (s.domain k) (⊤_ (s.domain k).ProEt)) →
        ∀ (P : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt), V k f →
              CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
          (a b : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt), V k f → ℤ),
          (∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
            (P k U f hf).IsStrictlyGE (a k U f hf) ∧
            (P k U f hf).IsStrictlyLE (b k U f hf) ∧
            ∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E)
                ((P k U f hf).X q) ∧
              Module.Finite (Padic.coefficientExtensionIntegers l E) ((P k U f hf).X q)) →
          ∀ e : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
              (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
              (pbcActualDerivedPull (U.hom ≫ s.immersion k)
                (pbcPadicCoefficientDatum l E)).obj K ≅
              (integralConstantDerived U.left (pbcPadicCoefficientDatum l E)).obj
                ((completedConstantQ _).obj (P k U f hf)),
            ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
              (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
              CochainComplex.IsStrictlyGE
                  ((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)) (a k U f hf) ∧
              CochainComplex.IsStrictlyLE
                  ((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)) (b k U f hf) ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l F)
                  (((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)).X q) ∧
                Module.Finite (Padic.coefficientExtensionIntegers l F)
                  (((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)).X q)) ∧
              IsIso (finiteFreeLocalModelMap l E F i (U.hom ≫ s.immersion k) K
                (P k U f hf) (e k U f hf)) := by
  sorry

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.Paper.CompatibleFiniteDerivedTrivializations
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.NilpotentReductionLissity
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.RingTheory.RlimPerfectComplete

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
/-!
# Perfect local lifting of a lisse residue reduction

Source: Stacks Project, proetale.tex, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8 and
Proposition 6.6.11 (blueprint: lem-weil-pbc-residue-lisse-perfect-lift).

Constant complexes use the existing constant-module sheafification. The coefficient
maps below are fixed uniquely on constant sections. Restriction means the actual
localized site, without identifying it with a separately chosen small skeleton.

## Main definitions

- `residueLisseDerivedConstant`: the exact constant module functor on derived categories.
- `residueLisseConstantComparison`: the normalized quotient coefficient comparison.

## Main statements

- `residue_lisse_perfect_lift`: the local perfect realization over completed coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- Constant module sheafification is additive.
Source: Stacks Tags 03CY and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift).
Proof: the constant presheaf functor is sectionwise additive. Pullback of presheaves
precomposes each component. Module sheafification is additive, since its underlying
abelian sheafification preserves addition. Composition gives the asserted structure. -/
@[instance]
theorem residueLisseConstant_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (koszulConstantFunctor X A).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map
        (f + g))) = _
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    (((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map f)) +
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map g))) = _
  exact Functor.map_add _

/-- Constant module sheafification preserves finite limits.
Source: Stacks Tags 03CY and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift).
Proof: finite kernels and products of constant module presheaves are computed on the
constant modules. Associated sheafification is left exact, so preserves these limits. -/
@[instance]
theorem residueLisseConstant_preservesFiniteLimits
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    PreservesFiniteLimits (koszulConstantFunctor X A) := by
  have : PreservesFiniteLimits (koszulConstantFunctor X A ⋙
      SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A)) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} A)) AddCommGrpCat.{t + 1} ⋙
        constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A))

/-- Constant module sheafification preserves finite colimits.
Source: Stacks Tags 03CY and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift).
Proof: the constant presheaf functor preserves cokernels and finite sums, sectionwise.
Sheafification is a left adjoint and preserves them. Thus their composite is exact. -/
@[instance]
theorem residueLisseConstant_preservesFiniteColimits
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    PreservesFiniteColimits (koszulConstantFunctor X A) := by
  have := (koszulConstantUnit_local X A).1
  have := (koszulConstantUnit_local X A).2
  have : PreservesFiniteColimits
      (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)) := by
    constructor
    intro J _ _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun U ↦ ?_)⟩
    exact hc
  exact comp_preservesFiniteColimits _ _

/-- The standard algebraic localization, with no equality imposed on site universes.
Source: Stacks Tags 05RU and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
instance residueLisseAlgebraHasDerivedCategory (A : Type u) [CommRing A] :
    HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The standard localization for arbitrary coefficient sheaves on the small site.
Source: Stacks Tag 05RU (blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
instance residueLisseRingHasDerivedCategory (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) :=
  HasDerivedCategory.standard _

/-- The constant complex functor uses the canonical module-universe lift and scalar
restriction along ULift.ringEquiv before the recorded exact constant module functor.
Source: Stacks Tags 05RU and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
def residueLisseDerivedConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  let e := (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom
  letI : (ModuleCat.restrictScalars.{t + 1} e).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{t + 1, t + 1, t} e).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{t + 1} e).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t} e).isRightAdjoint
  (ModuleCat.uliftFunctor.{t + 1, t} A ⋙
    ModuleCat.restrictScalars.{t + 1} e ⋙
      koszulConstantFunctor X A).mapDerivedCategory

/-- The constant-to-component comparison is fixed on all constant quotient sections.
Source: Stacks Tags 0H7J and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift).
Proof: send a constant to its constant continuous function on components and sheafify.
Every continuous function to a discrete ring is locally constant on its inverse-image
clopen cover. Equality is checked on that cover. These maps are therefore invertible;
local generation by constants proves uniqueness. -/
theorem residueLisseConstantComparison_exists (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! φ : adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n,
      IsIso φ ∧ ∀ (U : X.ProEtᵒᵖ) (a : completedAdicQuotient d n),
        φ.hom.app U ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
          (finiteCoefficientScalarMap X (completedAdicQuotient d n)).app U a := by
  sorry

/-- The normalized constant-to-component quotient coefficient comparison.
Source: Stacks Tags 0H7J and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
def residueLisseConstantComparison (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n :=
  (residueLisseConstantComparison_exists X d n).exists.choose

/-- Exact sheafification infrastructure on the actual localized small pro-etale site.
Source: Stacks Tags 03DA and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
instance residueLisseSliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  hasSheafifyEssentiallySmallSite.{t, t + 1, t + 1, t + 2, t + 1} _ _

/-- The locally bijective description on the same localized site.
Source: Stacks Tags 03DA and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
instance residueLisseSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _

/-- The standard localization on each slice, with its inherited coefficient ring.
Source: Stacks Tags 05RU and 09C6
(blueprint: lem-weil-pbc-residue-lisse-perfect-lift). -/
instance residueLisseSliceHasDerivedCategory (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

/-- A derived-complete complex whose residue reduction is etale locally a constant
perfect complex is pro-etale locally the completed realization of a perfect A-complex.
The sieve on the final object expresses the covering, including an empty covering
when X is empty. Perfectness is exactly the recorded bounded finite-projective model.

Source: Stacks Project, proetale.tex, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8 and
Proposition 6.6.11 (blueprint: lem-weil-pbc-residue-lisse-perfect-lift).

Proof plan:
1. Restrict to the given etale residue-trivializing cover, then to the connected clopen
   components of Noetherian affine opens. Slice restriction is exact and preserves
   products, constants and the quotient-completion unit. Use the localization equivalence
   of lem-weil-proetale-weakly-etale-localization and constant-completion equivalence.
2. Let [a,b] bound the perfect residue model. Induct on n using the coefficient triangle
   for I^n/I^(n+1), derived balancing on K-flat resolutions, and the long exact cohomology
   sequence. Finite locally constant sheaves form a Serre subcategory. Thus every M_n
   has finite locally constant cohomology in the same [a,b], without assuming M bounded.
3. Use the one-stratum constructible partition and finite-ring etale derived origin to
   obtain L_n. Full faithfulness uniquely lifts the datum's normalization isomorphisms;
   faithfulness gives the quotient cocycles. Nilpotent-reduction lissity makes all
   cohomology sheaves of L_n finite locally constant on the etale site.
4. Apply an exact geometric stalk to these same normalizations, retaining their scalar
   extension units. The stalk tower has the required quotient cocycles. The algebraic
   perfect inverse-limit reconstruction lemma yields a bounded finite-projective
   A-complex P with compatible reductions to these stalk complexes.
5. The finite locally constant isomorphism sheaves have nonempty stalks on the connected
   neighborhood. Compatible finite derived trivialization yields one pro-etale cover
   and compatible identifications of all reductions of P with M_n there.
6. For each projective term of P choose an idempotent on a finite free module. Its finite
   quotient sheaves have sectionwise surjective transitions. The Roos 1-shift map is
   sectionwise surjective by recursive lifting. The inverse limit is the same idempotent
   summand of B_X^r, hence B_X tensor_A P. Exact products and boundedness identify the
   derived limit with this bounded complex; finite projectivity computes derived tensor.
   On M the quotient-completion comparison and exact slice restriction identify the
   right limit with M|U. The compatible tower isomorphism gives the asserted isomorphism.
   Assemble the connected affine covers; use the empty covering for the empty scheme. -/
theorem residue_lisse_perfect_lift (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hcomplete : IsCompletedAdicDerivedComplete X d r a ha M)
    (_hresidue : ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
      ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
        ∃ P : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V)
                ((completedAdicQuotientReduction X d 0).obj M) ≅
              ringedSiteDerivedRestrictionOfUniverses
                (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V)
                ((completedAdicDerivedChange X
                    (residueLisseConstantComparison X d 0)).obj
                  ((residueLisseDerivedConstant X (A ⧸ d.ideal ^ (0 + 1))).obj P)))) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ P : DerivedCategory (ModuleCat.{t} A),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                (completedAdicRing X d) U M ≅
              ringedSiteDerivedRestrictionOfUniverses
                (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  ((residueLisseDerivedConstant X A).obj P))) := by
  sorry

end AlgebraicGeometry.Scheme

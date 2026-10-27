/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralCoefficientPresentationComparison
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.SixFunctors.RegularRoosKoszulUnit
import Sheaf.Paper.CompletedCoefficientRegularQuotients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.WeilCompletedTensorReflector

/-! # The actual quotient completion is the completed-coefficient reflector

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E, and
sites-cohomology.tex, Tag 0941
(blueprint: lem-sf-quotient-completion-actual-reflector).

The strict tower and its augmentation are computed on a single flat-term K-flat
representative. The limit is the total right derived inverse limit of strict towers.
The intrinsic completion is specified by its published fiber and unit, transported
along the projection-normalized coefficient isomorphism. Index n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralQuotientCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- Fixed-size abelian sheafification for the published small site.
Source: Stacks 03DA (blueprint: lem-sf-quotient-completion-actual-reflector). -/
local instance (priority := 5000) abelianSheafify :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

/-- The fixed-size locally bijective criterion, with no free coefficient universe.
Source: Stacks 03DA (blueprint: lem-sf-quotient-completion-actual-reflector). -/
local instance (priority := 5000) abelianLocallyBijective :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

/-- The published site is small in the coefficient universe.
Source: Stacks 09A5 (blueprint: lem-sf-quotient-completion-actual-reflector). -/
local instance (priority := 5000) siteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

/-- The standard ordinary derived category of the abelian category of strict towers.
Source: Stacks 0941 (blueprint: lem-sf-quotient-completion-actual-reflector). -/
local instance (priority := 5000) towerDerived :
    HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ IntegralOnSlice.Mod.{u, u} l E T none) :=
  HasDerivedCategory.standard _

/-- Transpose the published strict quotient tower into a complex of module towers.
Source: Stacks 0941 and 0A0E (blueprint: lem-sf-quotient-completion-actual-reflector). -/
def strictTower : IntegralOnSlice.Cx.{u, u} l E T none ⥤
    CochainComplex (ℕᵒᵖ ⥤ IntegralOnSlice.Mod.{u, u} l E T none) ℤ :=
  IntegralOnSlice.tower.{u, u} l E T none ⋙
    PrincipalQuotientCompletion.transpose.{u + 1, u, u + 1}
      (completedIntegralCommRingSheafUnrestricted l E T)

/-- Localization of that same strict tower on the resolving class of good representatives.
Source: Stacks 0941 (blueprint: lem-sf-quotient-completion-actual-reflector). -/
def representativeTower : (IntegralOnSlice.Good.{u, u} l E T none).FullSubcategory ⥤
    DerivedCategory (ℕᵒᵖ ⥤ IntegralOnSlice.Mod.{u, u} l E T none) :=
  (IntegralOnSlice.Good.{u, u} l E T none).ι ⋙ strictTower l E T ⋙ DerivedCategory.Q

/-- The actual quotient augmentation gives the reflector, with the actual Koszul unit.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E;
sites-cohomology.tex, Tag 0941
(blueprint: lem-sf-quotient-completion-actual-reflector).

The family q and ring-sheaf isomorphism e are fixed by the residue formulas and every
limit projection, as in lem-weil-pbc-integral-coefficient-presentation-comparison.
The comparison lambda fixes the strict derived quotient functor Q on every good
representative. The equation involving augmentedUnit fixes eta to be the actual
quotient augmentation followed by total right derived limit. The b equation fixes
Lambda and kappa to the transported published Koszul fiber and its (u,0) unit.
Consequently a is a natural comparison of these particular constructions.

Proof:
1. Apply lem-sp-completed-coefficient-regular-quotients and
   sk-def-sp-coefficient-towers: the uniformizer is regular on B_T and its power
   quotients are the actual constant finite coefficient sheaves, with all transitions.
   Apply lem-weil-proetale-countable-products-exact for exact countable products.
2. Use lem-weil-pbc-integral-coefficient-presentation-comparison to transport the
   published intrinsic fiber, tensor, products and unit to B_T. The signed product
   fiber of its singleton Koszul tower has unit ((p tensor 1)_n,0).
   lem-weil-strict-roos-comparison and lem-cbc-exact-product-functor-strict-limit
   identify this fiber with the strict derived limit, preserving that augmentation.
3. Apply lem-sf-regular-roos-koszul-unit. The strict quotient comparison is the
   residue map in degree zero and zero in degree -1. It commutes with every
   transition and carries p tensor 1 to p tensor the residue of 1. Compose its
   natural comparison with Step 2 to get a and kappa followed by a equals eta.
4. Apply lem-weil-pbc-ringed-koszul-completion-reflector. Transport its local
   completeness and Hom bijection across a. For each f the equality
   kappa followed by a followed by f equals eta followed by f identifies the
   Hom maps themselves. The Koszul Hom map is bijective as well.
5. The regular-unit theorem identifies local completeness, the Koszul-unit
   criterion, the quotient Roos-triangle predicate and invertibility of eta.
   The normalized comparisons identify the Koszul unit with kappa. This works
   for arbitrary unbounded inputs and never assumes completeness of the input. -/
theorem actual_reflector :
    ∃ (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
      (e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T),
      (∀ (n : ℕ) (x : PbcIntegralRing l E),
        q n (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down)) ∧
      (∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫
          (IntegralCoefficientPresentation.level l E T q n).hom) ∧
      ∃ (Q : IntegralOnSlice.D.{u, u} l E T none ⥤
          DerivedCategory (ℕᵒᵖ ⥤ IntegralOnSlice.Mod.{u, u} l E T none))
        (lam : IntegralOnSlice.qGood.{u, u} l E T none ⋙ Q ≅ representativeTower l E T)
        (η : 𝟭 (IntegralOnSlice.D.{u, u} l E T none) ⟶
          Q ⋙ koszulRlim.{u + 1, u, u + 1, u + 2}
            (completedIntegralCommRingSheafUnrestricted l E T))
        (Λ : IntegralOnSlice.D.{u, u} l E T none ⥤ IntegralOnSlice.D.{u, u} l E T none)
        (κ : 𝟭 (IntegralOnSlice.D.{u, u} l E T none) ⟶ Λ)
        (a : Λ ≅ Q ⋙ koszulRlim.{u + 1, u, u + 1, u + 2}
          (completedIntegralCommRingSheafUnrestricted l E T)),
        (∀ P : (IntegralOnSlice.Good.{u, u} l E T none).FullSubcategory,
          η.app ((IntegralOnSlice.qGood.{u, u} l E T none).obj P) ≫
            (koszulRlim.{u + 1, u, u + 1, u + 2}
              (completedIntegralCommRingSheafUnrestricted l E T)).map
              (lam.hom.app P) =
          RegularRoosKoszul.augmentedUnit.{u + 1, u, u + 1, u + 2}
            (completedIntegralCommRingSheafUnrestricted l E T) P.obj
            ((IntegralOnSlice.tower.{u, u} l E T none).obj P.obj)
            ((IntegralOnSlice.augmentation.{u, u} l E T none).app P.obj)) ∧
        (∀ C : CochainComplex
            (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
          ∃ b : Λ.obj ((pbcDerivedRestrict e.inv).obj (DerivedCategory.Q.obj C)) ≅
              (pbcDerivedRestrict e.inv).obj (DerivedCategory.Q.obj
                (intrinsicCompletionComplex T (pbcIntegralDatum l E) 1
                  (fun _ : Fin 1 ↦ pbcUniformizer l E) C)),
            κ.app ((pbcDerivedRestrict e.inv).obj (DerivedCategory.Q.obj C)) ≫ b.hom =
              (pbcDerivedRestrict e.inv).map (DerivedCategory.Q.map
                (intrinsicCompletionComplexUnit T (pbcIntegralDatum l E) 1
                  (fun _ : Fin 1 ↦ pbcUniformizer l E) C))) ∧
        (∀ H : IntegralOnSlice.D.{u, u} l E T none, κ.app H ≫ a.hom.app H = η.app H) ∧
        (∀ (H : IntegralOnSlice.D.{u, u} l E T none) (U : T.ProEt)
            (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
          (∃ S : Sieve U, S ∈ ProEt.topology T U ∧
            ∀ (V : T.ProEt) (f : V ⟶ U), S f →
              ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
                s.val (op (Over.mk f)) = integralCompletionScalarValue l E T (op V) * c) →
            IsZero (integralCompletionLocalTest l E T
              ((Q ⋙ koszulRlim.{u + 1, u, u + 1, u + 2}
                (completedIntegralCommRingSheafUnrestricted l E T)).obj H) U s)) ∧
        (∀ (H L : IntegralOnSlice.D.{u, u} l E T none),
          (∀ (U : T.ProEt)
              (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
            (∃ S : Sieve U, S ∈ ProEt.topology T U ∧
              ∀ (V : T.ProEt) (f : V ⟶ U), S f →
                ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
                  s.val (op (Over.mk f)) = integralCompletionScalarValue l E T (op V) * c) →
              IsZero (integralCompletionLocalTest l E T L U s)) →
            Function.Bijective (fun f :
              (Q ⋙ koszulRlim.{u + 1, u, u + 1, u + 2}
                (completedIntegralCommRingSheafUnrestricted l E T)).obj H ⟶ L ↦
                η.app H ≫ f) ∧
            Function.Bijective (fun g : Λ.obj H ⟶ L ↦ κ.app H ≫ g) ∧
            ∀ f : (Q ⋙ koszulRlim.{u + 1, u, u + 1, u + 2}
                (completedIntegralCommRingSheafUnrestricted l E T)).obj H ⟶ L,
              κ.app H ≫ (a.hom.app H ≫ f) = η.app H ≫ f) ∧
        (∀ H : IntegralOnSlice.D.{u, u} l E T none,
          List.TFAE [
            (∀ (U : T.ProEt)
                (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
              (∃ S : Sieve U, S ∈ ProEt.topology T U ∧
                ∀ (V : T.ProEt) (f : V ⟶ U), S f →
                  ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
                    s.val (op (Over.mk f)) = integralCompletionScalarValue l E T (op V) * c) →
                IsZero (integralCompletionLocalTest l E T H U s)),
            IsIso (κ.app H),
            IntegralOnSlice.IsComplete.{u, u} l E T none H,
            IsIso (η.app H)]) := by
  sorry

end WeilConjectures.IntegralQuotientCompletion

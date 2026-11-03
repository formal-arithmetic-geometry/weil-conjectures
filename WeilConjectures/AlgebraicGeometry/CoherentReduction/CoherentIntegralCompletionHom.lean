/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.Semilinear.DerivedSystemMappingHom
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Integral Hom from the actual coherent mapping system

Source: Bhatt--Scholze, Section 6.8, and Stacks Tags 08J9 and 0B6E.
(blueprint: lem-sfb-coherent-integral-completion-hom)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

/-- The ordinary Hom bifunctor with its genuine pre- and postcomposition maps.
Source: Stacks 08J9 (blueprint: lem-sfb-coherent-integral-completion-hom). -/
abbrev homPairs (D : Type*) [Category D] : Dᵒᵖ × D ⥤ Type _ :=
  Functor.uncurry.obj coyoneda

/-- Transposition is natural in the tensor factor because evaluation is natural there.
Source: Stacks 08J9 (blueprint: lem-sfb-coherent-integral-completion-hom).
Proof: transpose both sides, apply evaluation naturality, then interchange the two
tensor factors. The inverse transposition identity recovers the original map. -/
theorem closedTranspose_source_naturality
    {D : Type*} [Category* D] (H : Dᵒᵖ × D ⥤ D)
    (S : WeilConjectures.CoefficientClosedStructure H)
    {T P P' Q : D} (f : P' ⟶ P)
    (g : (@MonoidalCategory.tensorRight D _ S.monoidal P).obj T ⟶ Q) :
    (S.adjunction P').homEquiv T Q
        ((@MonoidalCategory.tensorLeft D _ S.monoidal T).map f ≫ g) =
      (S.adjunction P).homEquiv T Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q)) := by
  let := S.monoidal
  let t : T ⟶ H.obj (op P, Q) := (S.adjunction P).homEquiv T Q g
  have hg : (@MonoidalCategory.tensorRight D _ S.monoidal P).map t ≫
      (S.adjunction P).counit.app Q = g :=
    ((S.adjunction P).homEquiv T Q).symm_apply_apply g
  apply ((S.adjunction P').homEquiv T Q).symm.injective
  simp only [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    S.evaluation_naturality]
  change (T ◁ f) ≫ g = (t ▷ P') ≫ (H.obj (op P, Q) ◁ f) ≫
    (S.adjunction P).counit.app Q
  rw [← MonoidalCategory.whisker_exchange_assoc]
  exact congrArg (fun k ↦ (T ◁ f) ≫ k) hg.symm

/-- The scalar-action/closed-Hom adjunction is natural in the Hom source.
Source: Stacks 08J9 (blueprint: lem-sfb-coherent-integral-completion-hom).
Proof: first use source naturality of closed transposition, then right naturality
of the scalar realization/sections adjunction. -/
theorem scalarClosedHom_source_naturality
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (a : F ⊣ G)
    (H : Dᵒᵖ × D ⥤ D) (S : WeilConjectures.CoefficientClosedStructure H)
    {U : C} {M M' N : D} (f : M' ⟶ M)
    (g : (@MonoidalCategory.tensorRight D _ S.monoidal M).obj (F.obj U) ⟶ N) :
    (a.comp (S.adjunction M')).homEquiv U N
        ((@MonoidalCategory.tensorLeft D _ S.monoidal (F.obj U)).map f ≫ g) =
      (a.comp (S.adjunction M)).homEquiv U N g ≫
        G.map (H.map (Prod.mkHom f.op (𝟙 N))) := by
  simp only [Adjunction.comp_homEquiv]
  change a.homEquiv U (H.obj (op M', N))
      ((S.adjunction M').homEquiv (F.obj U) N
        ((@MonoidalCategory.tensorLeft D _ S.monoidal (F.obj U)).map f ≫ g)) =
    a.homEquiv U (H.obj (op M, N)) ((S.adjunction M).homEquiv (F.obj U) N g) ≫
      G.map (H.map (Prod.mkHom f.op (𝟙 N)))
  exact (congrArg (a.homEquiv U (H.obj (op M', N)))
    (closedTranspose_source_naturality H S f g)).trans
      (a.homEquiv_naturality_right _ _)

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary inverse limit is additive because it preserves binary products and zero.
Source: Stacks 0941 (blueprint: lem-sfb-coherent-integral-completion-hom). -/
theorem scalarLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) ⥤ _).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact constant-system functor is additive, section by section.
Source: Stacks 0941 (blueprint: lem-sfb-coherent-integral-completion-hom). -/
theorem scalarConstantAdditive :
    (Functor.const ℕᵒᵖ : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).Additive :=
  { map_add := by intros; rfl }

/-- The actual derived constant free scalar module, without an existence choice.
Source: Stacks 0941, 08JA (blueprint: lem-sfb-coherent-integral-completion-hom). -/
def scalarLimitSource : DScalarTowers.{u + 1, u, u + 1}
    (Padic.coefficientExtensionIntegers l E) := by
  let O := Padic.coefficientExtensionIntegers l E
  let M := ModuleCat.{u + 1} O
  let D := (Functor.const ℕᵒᵖ : M ⥤ (ℕᵒᵖ ⥤ M))
  let : D.Additive := scalarConstantAdditive l E
  exact D.mapDerivedCategory.obj ((DerivedCategory.singleFunctor M 0).obj (ModuleCat.of O O))

/-- Take the actual total derived inverse limit of O-module systems, then H^0.
The derived limit retains the possible lim^1 contribution.
Source: Stacks 0B6E (blueprint: lem-sfb-coherent-integral-completion-hom). -/
def limitH0 : DScalarTowers.{u + 1, u, u + 1}
    (Padic.coefficientExtensionIntegers l E) ⥤ Type (u + 1) := by
  let L := (lim : (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E)) ⥤ _)
  let : L.Additive := scalarLimitAdditive l E
  let : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) := scalarLimitKInjective l E
  exact L.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ 0 ⋙ forget _

/-- Degree-zero total scalar limit is represented by the derived constant free module.
The equivalences are allowed to cross localization universes.
Source: Stacks 0941, 08JA
(blueprint: lem-sfb-coherent-integral-completion-hom).

Proof: derive the exact constant-system/ordinary-limit adjunction. Morphisms
from O[0] compute H^0 because O is projective. Evaluation at 1 identifies
Hom_O(O,M) with M. Adjoint naturality, functoriality of homology and evaluation
at 1 give the displayed naturality equation. -/
theorem scalarLimitHomRepresentation :
    ∃ e : ∀ K, (scalarLimitSource l E ⟶ K) ≃ (limitH0 l E).obj K,
        ∀ {K L} (f : K ⟶ L) (g : scalarLimitSource l E ⟶ K),
          e L (g ≫ f) = (limitH0 l E).map f (e K g) := by
  let O := Padic.coefficientExtensionIntegers l E
  let M := ModuleCat.{u + 1} O
  let D := (Functor.const ℕᵒᵖ : M ⥤ (ℕᵒᵖ ⥤ M))
  let L := (lim : (ℕᵒᵖ ⥤ M) ⥤ M)
  let : D.Additive := scalarConstantAdditive l E
  let : L.Additive := scalarLimitAdditive l E
  let : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ M) := scalarLimitKInjective l E
  let FD : DerivedCategory.{u + 1} M ⥤ DScalarTowers.{u + 1, u, u + 1} O :=
    D.mapDerivedCategory
  let RL : DScalarTowers.{u + 1, u, u + 1} O ⥤ DerivedCategory.{u + 1} M :=
    L.rightDerivedFunctor
  let a : FD ⊣ RL := (constLimAdj : D ⊣ L).mapDerivedCategoryRightDerivedAdjunction
  let P := ModuleCat.of O O
  let U := scalarLimitSource l E
  let e (K : DScalarTowers.{u + 1, u, u + 1} O) : (U ⟶ K) ≃ (limitH0 l E).obj K :=
    (a.homEquiv _ K).trans
      ((DerivedCategory.singleFunctorZeroHomEquiv P (RL.obj K)).trans
        (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf O O _).toEquiv))
  refine ⟨e, ?_⟩
  intro K K' f g
  change (((DerivedCategory.singleFunctorCompHomologyFunctorIso M 0).inv.app P ≫
      (DerivedCategory.homologyFunctor M 0).map (a.homEquiv _ K' (g ≫ f))).hom (1 : O)) =
    ((DerivedCategory.homologyFunctor M 0).map (RL.map f)).hom
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso M 0).inv.app P ≫
        (DerivedCategory.homologyFunctor M 0).map (a.homEquiv _ K g)).hom (1 : O))
  rw [a.homEquiv_naturality_right, Functor.map_comp]
  rfl

/-- Completion computes the ordinary integral Hom groups by the coherent
O-module valued mapping system, naturally in both integral arguments.

Source: Bhatt--Scholze, Section 6.8; Stacks Tags 08J9 and 0B6E; step 3 of
`lem-sfb-dc-proper-pushforward-left-adjoint-oe-general-field`.
(blueprint: lem-sfb-coherent-integral-completion-hom)

Proof: apply the integral completion unit to the second argument. It is an
isomorphism on bounded constructible objects over a Noetherian scheme. Resolve
the actual derived quotient system simultaneously by a K-injective system.
The coefficient tensor/restriction adjunction identifies Hom into each level
with the same finite-coefficient mapping complex used by mapping. These are
identifications of systems: their transition maps are the scalar-adjunction
transposes of the quotient maps, with their original integral scalar action.
Global derived Hom commutes with this total derived limit by
lem-sfb-ringed-site-global-rhom-derived-limits. The zeroth cohomology of global
derived Hom is ordinary derived-category Hom, by its specified representing
bijection. These constructions are natural in both arguments, since all maps
come from the tensor units, evaluation and the completion augmentation.
No finite cohomological-dimension assumption on a base field is used; zero
objects and empty schemes are included.
-/
theorem coherent_integral_completion_hom
    (X : Scheme.{u}) [IsNoetherian X] :
    Nonempty (homPairs (Bc l E X) ≅
      (reductionBc l E X).op.prod (reductionBc l E X) ⋙
        mapping l E X ⋙ limitH0 l E) := by
  sorry

end AlgebraicGeometry.ProEtale.CoherentReduction

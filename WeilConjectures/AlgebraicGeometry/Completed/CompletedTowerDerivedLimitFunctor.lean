/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.ProperBaseChange.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# The functorial completed-coefficient derived inverse limit

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1242;
Stacks Tags 08TC, 079P and 0BK7 (blueprint: prop-weil-pbc-rlim-functoriality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Strict module towers have K-injective resolutions in the unrestricted module category.
Source: Stacks Tags 079B and 079Q (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: the strict tower category is Grothendieck abelian by the adic datum's diagram
category theorem after small-site transport. Grothendieck abelian categories have
K-injective resolutions. Transport back preserves quasi-isomorphisms and homotopies. -/
@[instance]
theorem completedTowers_hasKInjectiveResolutions (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (pbcTowers T R) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : IsGrothendieckAbelian.{u + 1} (pbcTowers T R) :=
    reductionTower_isGrothendieckAbelian T ((adicLisseForget T).obj R)
  infer_instance

/-- The limit functor on strict module towers is additive.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: a map between limits is determined by its composites with the projections.
Both addition and the limit maps have their specified component maps, giving the equality. -/
@[instance]
theorem completedTowerLimit_additive (T : Scheme.{u}) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d)).Additive := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact Functor.additive_of_preserves_binary_products _

/-- Derived strict inverse limit, computed from the actual inverse-limit functor.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerRlim (T : Scheme.{u}) :
    DerivedCategory (pbcTowers T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
    pbcModules T (pbcAdicCompletion T d)).rightDerivedFunctor


/-- Constant strict towers, with all transitions equal to the identity.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerConstant (T : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : pbcModules T (pbcAdicCompletion T d) ⥤
    pbcTowers T (pbcAdicCompletion T d))

/-- Constant towers are additive and exact, since tower exactness is levelwise.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: all evaluations of the constant functor are the identity functor. Kernels,
cokernels and addition are computed at each level, proving the three assertions. -/
theorem completedTowerConstant_exact (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive ∧
    PreservesFiniteLimits (completedTowerConstant d T) ∧
    PreservesFiniteColimits (completedTowerConstant d T) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the specified constant tower functor.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_additive (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive := (completedTowerConstant_exact d T).1

/-- Exactness on kernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.1

/-- Exactness on cokernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.2

/-- Constant towers on derived objects by exact termwise descent.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedDerivedConstant (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapDerivedCategory

/-- The ordinary unit into the limit of a constant tower, with identity components.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedConstantLimitUnit (T : Scheme.{u}) :
    𝟭 (pbcModules T (pbcAdicCompletion T d)) ⟶
      completedTowerConstant d T ⋙ lim :=
  (constLimAdj : completedTowerConstant d T ⊣ lim).unit

/-- The derived unit is uniquely determined by the ordinary unit and the universal
right-derived comparison, on every representative, rather than by a cone choice.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: apply the right-derived unit to the constant tower of each complex after the
ordinary constant-limit unit. Naturality holds on chain maps and homotopies. Since
constant towers preserve quasi-isomorphisms, localization gives the displayed unit.
Essential surjectivity of localization and naturality give its uniqueness. -/
theorem completedConstantRlimUnit_exists (T : Scheme.{u}) :
    ∃! η : 𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
        completedDerivedConstant d T ⋙ completedTowerRlim d T,
      ∀ C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        η.app (DerivedCategory.Q.obj C) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (completedConstantLimitUnit d T)
              (.up ℤ)).app C) ≫
          (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
            pbcModules T (pbcAdicCompletion T d)).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj
                (((completedTowerConstant d T).mapHomologicalComplex (.up ℤ)).obj C)) ≫
          (completedTowerRlim d T).map
            (((completedTowerConstant d T).mapDerivedCategoryFactors).inv.app C) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let Δ := completedTowerConstant d T
  let L : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d) := lim
  let Q : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) := DerivedCategory.Q
  let τ : Q ⟶ Q ⋙ (completedDerivedConstant d T ⋙ completedTowerRlim d T) :=
    Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (completedConstantLimitUnit d T) (.up ℤ))
        DerivedCategory.Q ≫
      Functor.whiskerLeft (Δ.mapHomologicalComplex (.up ℤ))
        (Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
          L.rightDerivedFunctorUnit) ≫
      Functor.whiskerRight Δ.mapDerivedCategoryFactors.inv (completedTowerRlim d T)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ))
    (DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
  let η : 𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
      completedDerivedConstant d T ⋙ completedTowerRlim d T :=
    ff.preimage (X := 𝟭 _) (Y := completedDerivedConstant d T ⋙ completedTowerRlim d T) τ
  have hη : Functor.whiskerLeft Q η = τ := ff.map_preimage (X := 𝟭 _)
      (Y := completedDerivedConstant d T ⋙ completedTowerRlim d T) τ
  refine ⟨η, ?_, ?_⟩
  · intro C
    exact NatTrans.congr_app hη C
  · intro η' hη'
    apply Localization.natTrans_ext Q
      (HomologicalComplex.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ))
    intro C
    exact (hη' C).trans (NatTrans.congr_app hη C).symm

/-- The canonical map K → Rlim ΔK, defined by its unique representative normalization.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedConstantRlimUnit (T : Scheme.{u}) :
    𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
      completedDerivedConstant d T ⋙ completedTowerRlim d T :=
  (completedConstantRlimUnit_exists d T).exists.choose

/-- The inverse-limit functor is triangulated, computed by limits of K-injective
strict resolutions; any other universal right-derived pair gives the same functor.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: the additive limit functor on complexes preserves shifts and mapping cones.
The K-injective total-right-derived theorem supplies its triangulated structure.
Any two such pairs are uniquely isomorphic by the universal derived property. -/
theorem completedTowerRlim_properties (T : Scheme.{u}) :
    (∃ (_ : (completedTowerRlim d T).CommShift ℤ),
      (completedTowerRlim d T).IsTriangulated) ∧
    ∀ (RF : DerivedCategory (pbcTowers T (pbcAdicCompletion T d)) ⥤
        DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
      (η : (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
        pbcModules T (pbcAdicCompletion T d)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor η
        (HomotopyCategory.quasiIso (pbcTowers T (pbcAdicCompletion T d)) (.up ℤ)) →
      Nonempty (RF ≅ completedTowerRlim d T) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  constructor
  · exact ⟨inferInstance, inferInstance⟩
  · intro RF η hRF
    exact ⟨Functor.rightDerivedUnique RF _ η
      (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
        pbcModules T (pbcAdicCompletion T d)).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso _ (.up ℤ))⟩

/-- The functorial construction has the sequential derived-limit Roos triangle.
Source: Stacks Tags 08TC and 0BK7 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: resolve the tower K-injectively. Evaluations are K-injective and all transition
maps of each injective term split. Hence 1-shift on their product is epimorphic with
kernel the limit. The resulting short exact sequence of complexes gives the natural
Roos triangle. Transport through the universal derived comparison. -/
theorem completedTowerRlim_roos (T : Scheme.{u})
    (M : DerivedCategory (pbcTowers T (pbcAdicCompletion T d))) :
    ∃ (_ : HasProduct (completedTowerDerivedSequence T d M))
      (p : (completedTowerRlim d T).obj M ⟶ ∏ᶜ (completedTowerDerivedSequence T d M))
      (δ : ∏ᶜ (completedTowerDerivedSequence T d M) ⟶
        ((completedTowerRlim d T).obj M)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (completedTowerDerivedStep T d M)
        ((completedTowerRlim d T).obj M) p δ := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let B := pbcModules T (pbcAdicCompletion T d)
  have : HasFiniteBiproducts B := CategoryTheory.Abelian.hasFiniteBiproducts
  have : CountableAB4Star B := by
    have : (lim (J := Discrete ℕ) (C := B)).PreservesEpimorphisms :=
      { preserves := by
          intro F G f hf
          have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) :=
            (ProEt.countableProducts_exact.{u, u, 0} T (pbcAdicCompletion T d)).2.2
              ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
              (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map f = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi B (Discrete ℕ)
    exact CountableAB4Star.of_hasExactLimitsOfShape_nat B
  have : HasCountableProducts (DerivedCategory B) :=
    (derivedCategory_countableProducts_core.{0} B).choose
  have : HasProduct (completedTowerDerivedSequence T d M) := by
    change HasProduct (fun n : ℕ ↦
      (completedTowerDerivedSequence T d M n : DerivedCategory B))
    exact HasLimitsOfShape.has_limit (C := DerivedCategory B)
      (Discrete.functor (fun n : ℕ ↦
        (completedTowerDerivedSequence T d M n : DerivedCategory B)))
  refine ⟨inferInstance, completedRlimRoosProjection T d M, ?_⟩
  exact completedRlim_roos T d M

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint

/-!
# Acyclic components of injective coefficient towers

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-acyclic.md` and its proof; Stacks Tags 03FD, 015E and 05TH
(blueprint: det-sp-tower-injective-components).

Index n denotes the positive level n+1. The tower direct image is the actual
product-site module pushforward. Its scalar map is the existing constant-section
map, so both coefficients and transitions are fixed, including for the identity map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Enough injectives for the recorded tower category, from its Grothendieck structure.
Source: Stacks 079H; blueprint proof, step 1
(blueprint: det-sp-tower-injective-components). -/
instance spTowerEnoughInjectives (T : Scheme.{t}) :
    EnoughInjectives (spCoefficientTowers l E T) :=
  letI := (Classical.choice (sp_coefficient_towers_abelian l E T)).grothendieck
  inferInstance

/-- The standard ordinary localization of the actual tower category.
Source: blueprint proof, step 1 (blueprint: det-sp-tower-injective-components). -/
instance spTowerHasDerived (T : Scheme.{t}) :
    HasDerivedCategory (spCoefficientTowers l E T) := HasDerivedCategory.standard _

/-- Enough injectives for ring-sheaf modules in the common larger universe.
Source: Stacks 079H; blueprint proof, step 1
(blueprint: det-sp-tower-injective-components). -/
instance spRingModulesEnoughInjectives (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    EnoughInjectives (ringedSiteModules.{max u (t + 1)} R) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, max u (t + 1), 0}
    (Scheme.ProEt.topology T) R
  inferInstance

/-- Standard derived localization at a coefficient level.
Source: blueprint proof, step 1 (blueprint: det-sp-tower-injective-components). -/
instance spRingModulesHasDerived (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (ringedSiteModules.{max u (t + 1)} R) := HasDerivedCategory.standard _

/-- Sections of module sheaves form an additive functor.
Source: blueprint proof, step 3 (blueprint: det-sp-tower-injective-components). -/
instance spModuleEvaluationAdditive (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) (U : T.ProEtᵒᵖ) :
    (SheafOfModules.evaluation.{max u (t + 1)} R U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Evaluation uses the published, sectionwise normalized uncurrying equivalence.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationAdditive (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spCoefficientEvaluation l E T d.equivalence n).Additive :=
  letI := d.equivalenceAdditive
  inferInstance

/-- Exact evaluation preserves finite limits, by the recorded coefficient-tower theorem.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationLimits (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    PreservesFiniteLimits (spCoefficientEvaluation l E T d.equivalence n) :=
  d.evaluationLimits n

/-- Exact evaluation preserves finite colimits, by the recorded coefficient-tower theorem.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationColimits (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    PreservesFiniteColimits (spCoefficientEvaluation l E T d.equivalence n) :=
  d.evaluationColimits n

variable {T S : Scheme.{t}} (g : T ⟶ S)

/-- Base change on the level/site product, fixing the level.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerBaseChange : ℕ × S.ProEt ⥤ ℕ × T.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)

/-- The canonical constant-section scalar map at a product-site object.
Source: Stacks 0H7J; blueprint, coefficient identification
(blueprint: det-sp-tower-injective-components). -/
def spTowerRingMapApp (X : (ℕ × S.ProEt)ᵒᵖ) :
    (spCoefficientPresheaf l E S).obj X ⟶
      (spCoefficientPresheaf l E T).obj ((spTowerBaseChange g).op.obj X) :=
  (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
    ((Scheme.coefficientProEtaleDirectRingMap g
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (X.unop.1 + 1))))).hom.app
          (op X.unop.2))

/-- Constant-section coefficient maps commute with restrictions and quotient reductions.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components).
Proof: site naturality is naturality of the published constant-section map. For level
maps both composites send an integer to its reduction as a constant section; uniqueness
of the extension through sheafification makes them equal. A product arrow factors as
its level arrow and site arrow, giving the displayed naturality for every arrow. -/
theorem spTowerRingMap_naturality {X Y : (ℕ × S.ProEt)ᵒᵖ} (f : X ⟶ Y) :
    (spCoefficientPresheaf l E S).map f ≫ spTowerRingMapApp l E g Y =
      spTowerRingMapApp l E g X ≫
        (spCoefficientPresheaf l E T).map ((spTowerBaseChange g).op.map f) := by
  sorry

/-- The structural ring map on the product site, with the actual coefficient reductions.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerRingMap : spCoefficientPresheaf l E S ⟶
    (spTowerBaseChange g).op ⋙ spCoefficientPresheaf l E T where
  app := spTowerRingMapApp l E g
  naturality := fun {_ _} f ↦ spTowerRingMap_naturality l E g f

/-- Product-site module pushforward preserves the levelwise sheaf condition.
Source: blueprint, definition of g_(star,bullet)
(blueprint: det-sp-tower-injective-components).
Proof: at level n the underlying abelian presheaf is precomposition with base change.
That site functor is continuous, so it sends a sheaf to a sheaf by ordinary direct
image. Restricting the scalar action does not change this underlying abelian sheaf. -/
theorem spTowerPush_sheaf (M : spCoefficientTowers l E T) :
    spCoefficientTowerSheafCondition l E S
      ((PresheafOfModules.pushforward (spTowerRingMap l E g)).obj M.obj) := by
  sorry

/-- Ordinary direct image of coefficient towers, defined on actual product-site modules.
Every section, restriction, transition and morphism is pushed forward componentwise.
Source: blueprint, definition of g_(star,bullet)
(blueprint: det-sp-tower-injective-components). -/
def spTowerPush : spCoefficientTowers l E T ⥤ spCoefficientTowers l E S where
  obj M := ⟨(PresheafOfModules.pushforward (spTowerRingMap l E g)).obj M.obj,
    spTowerPush_sheaf l E g M⟩
  map f := ObjectProperty.homMk
    ((PresheafOfModules.pushforward (spTowerRingMap l E g)).map f.hom)

/-- Ordinary module direct image at the positive level n+1, using the canonical
constant-section coefficient map in the common coefficient universe.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
abbrev spLevelPush (n : ℕ) :=
  Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))

/-- The componentwise tower direct image is additive and left exact.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components).
Proof: addition is componentwise. Kernels and finite limits are levelwise in the tower
category. Each ordinary module direct image is a right adjoint and preserves finite
limits; their universal factorizations respect transitions, giving the tower limits. -/
theorem spTowerPush_properties :
    (spTowerPush l E g).Additive ∧ PreservesFiniteLimits (spTowerPush l E g) := by
  sorry

/-- Componentwise additivity of tower direct image.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
instance spTowerPushAdditive : (spTowerPush l E g).Additive :=
  (spTowerPush_properties l E g).1

/-- Left exactness of tower direct image.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
instance spTowerPushLimits : PreservesFiniteLimits (spTowerPush l E g) :=
  (spTowerPush_properties l E g).2

/-- The published ordinary module direct image is additive.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
instance spCoefficientModulePushAdditive (A : CommRingCat.{max u (t + 1)}) :
    (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The published ordinary module direct image is left exact, being a right adjoint.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
instance spLevelPushLimits (n : ℕ) : PreservesFiniteLimits (spLevelPush l E g n) :=
  inferInstance

variable (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)

/-- Evaluation commutes with the actual tower direct image, by the identity on sections.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components).
Proof: both composites have sections M_(n+1)(T times_S U), with the action through the
same constant-section coefficient map. The four normalization fields of dT and dS
identify their restrictions and linear maps. The identity of these sections is a
natural linear isomorphism. Sectionwise faithfulness proves its uniqueness. -/
theorem spTowerEvaluationIso_existsUnique (n : ℕ) :
    ∃! e : spTowerPush l E g ⋙ spCoefficientEvaluation l E S dS.equivalence n ≅
        spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n,
      ∀ (M : spCoefficientTowers l E T) (U : S.ProEtᵒᵖ)
        (x : ((spCoefficientEvaluation l E S dS.equivalence n).obj
          ((spTowerPush l E g).obj M)).val.obj U),
        HEq ((e.hom.app M).val.app U x) x := by
  sorry

/-- The canonical underived evaluation identity, fixed by the identity on sections.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerEvaluationIso (n : ℕ) :
    spTowerPush l E g ⋙ spCoefficientEvaluation l E S dS.equivalence n ≅
      spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n :=
  (spTowerEvaluationIso_existsUnique l E g dT dS n).exists.choose

/-- The same evaluation identity on bounded below homotopy categories.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
def spTowerEvaluationHomotopyIso (n : ℕ) :
    (spTowerPush l E g).mapHomotopyCategoryPlus ⋙
        (spCoefficientEvaluation l E S dS.equivalence n).mapHomotopyCategoryPlus ≅
      (spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus ⋙
        (spLevelPush l E g n).mapHomotopyCategoryPlus :=
  letI : (spLevelPush l E g n).Additive :=
    spCoefficientModulePushAdditive g (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
  letI : (spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n).Additive :=
    inferInstance
  Functor.mapHomotopyCategoryPlusCompIso
      (F := spTowerPush l E g)
      (G := spCoefficientEvaluation l E S dS.equivalence n)
      (H := spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n)
      (spTowerEvaluationIso l E g dT dS n) ≪≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (F := spCoefficientEvaluation l E T dT.equivalence n)
      (G := spLevelPush l E g n)
      (H := spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n)
      (Iso.refl (spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n))).symm

/-- The finite-product retract and both acyclicity conclusions for injective towers.
Source: blueprint main-20261015, tower-level acyclicity lemma, paragraphs 1--2;
Stacks 03FD (blueprint: det-sp-tower-injective-components).

Proof:
1. Work in the common larger universe on the small pro-etale site. The ringed-site
Grothendieck theorem and Stacks 079H give enough injectives at every level; the tower
Grothendieck theorem does the same for towers.
2. By det-sp-tower-evaluation-adjoint embed I in the product of the right-adjoint
systems r_n J_n with J_n injective. Extend the identity of I across this monomorphism
by injectivity to split it. Products of towers are levelwise. At level r+1 only the
indices n+1 <= r+1 contribute, giving exactly the displayed finite product of actual
scalar restrictions. Evaluating the splitting gives the retract.
3. By lem-sc-injective-module-abelian-acyclic-zariski (Stacks 03FD), every J_n has
vanishing positive abelian-sheaf cohomology on every object. Scalar restriction leaves
that abelian sheaf unchanged. The module/abelian evaluation comparison transports
this vanishing to the R_(r+1)-module section functor.
4. Resolve the finitely many restricted J_n by injective R_(r+1)-module resolutions.
Their finite product is an injective resolution: maps extend coordinatewise and
kernels and images are coordinatewise in finite sums. Sections and cohomology commute
with these finite products. Apply the higher section functors to the retract; its
identity factors through zero, so all positive section functors vanish on I_(r+1).
5. For an injective resolution L of I_(r+1), g_* L has sections L(T times_S V).
Their positive cohomology vanishes by step 4. Kernels are sectionwise and cokernels
are sheafified sectionwise, so the positive cohomology sheaves of g_* L vanish.
This is precisely g_*-acyclicity. No infinite-product exactness or injectivity after
restriction of scalars is asserted. -/
theorem sp_tower_injective_components (I : spCoefficientTowers l E T) [Injective I] :
    (∀ r : ℕ, ∃ J : (n : Fin (r + 1)) →
        systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n.val,
      (∀ n : Fin (r + 1), Injective (J n)) ∧
      Nonempty (Retract ((spCoefficientEvaluation l E T dT.equivalence r).obj I)
        (∏ᶜ fun n : Fin (r + 1) ↦
          (systemRestriction.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)
            (Nat.le_of_lt_succ n.isLt)).obj (J n)))) ∧
    (∀ (r : ℕ) (U : T.ProEt),
      (SheafOfModules.evaluation.{max u (t + 1)} (spCoefficientRing l E T r) (op U)).rightAcyclic
        ((spCoefficientEvaluation l E T dT.equivalence r).obj I)) ∧
    (∀ r : ℕ, (spLevelPush l E g r).rightAcyclic
      ((spCoefficientEvaluation l E T dT.equivalence r).obj I)) := by
  sorry

/-- Evaluating any bounded below injective tower complex gives a complex computing
finite-level derived direct image: its canonical right-derived unit is invertible.
Source: blueprint, last paragraph; Stacks 015E and 05TH
(blueprint: det-sp-tower-injective-components).

Proof: evaluation is exact by det-sp-coefficient-towers-abelian, hence sends any
quasi-isomorphism into the tower complex to a quasi-isomorphism into its component.
It preserves the lower bound. The preceding component theorem gives termwise
g_*-acyclicity. Apply src-right-derived-functor-plus-acyclic-unit (Stacks 015E) to
obtain exactly the displayed invertible unit. An evaluated injective tower resolution
therefore computes the finite-level derived image of its source. Bounded below
injective resolutions are K-injective by lem-weil-pbc-bounded-below-injectives-kinjective,
so the D+ computation agrees with the ordinary unbounded derived direct image. -/
theorem sp_tower_injective_complex_computes (n : ℕ)
    (I : CochainComplex.Plus (spCoefficientTowers l E T))
    (hI : ∀ k : ℤ, Injective (I.obj.X k)) :
    IsIso ((spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
      ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))) := by
  sorry

/-- The explicitly supplied bounded below injective resolution computes the finite-level
image of its source C. The equation specifies the isomorphism by the derived units
and the resolution isomorphism C to Q(I), rather than by an arbitrary identification.
Source: blueprint, last paragraph; Stacks 015E and 05TH
(blueprint: det-sp-tower-injective-components).
Proof: exact evaluation makes its derived unit invertible on every complex and sends
the resolution isomorphism to the evaluated resolution isomorphism. The preceding
acyclic-complex theorem makes the finite-level direct-image derived unit invertible
on the evaluated I. Compose these two invertible units and the inverse image of the
resolution isomorphism, exactly in the order displayed below. Thus g_* I_n represents
Rg_* C_n for the given resolution and not just for a selected resolution. -/
theorem sp_tower_injective_resolution_computes (n : ℕ)
    (C : DerivedCategory.Plus (spCoefficientTowers l E T))
    (I : CochainComplex.Plus (spCoefficientTowers l E T))
    (ρ : C ≅ DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))
    (hI : ∀ k : ℤ, Injective (I.obj.X k)) :
    ∃ e : DerivedCategory.Plus.Qh.obj
        ((spLevelPush l E g n).mapHomotopyCategoryPlus.obj
          ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))) ≅
      ((spLevelPush l E g n).rightDerivedFunctorPlus.obj
        ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus.obj C)),
      e.hom = (spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
          ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
        (spLevelPush l E g n).rightDerivedFunctorPlus.map
          ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
        (spLevelPush l E g n).rightDerivedFunctorPlus.map
          ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus.map ρ.inv) :=
  by sorry

/-- Exact evaluation on D+ is termwise evaluation: its derived unit is always invertible.
This identifies the evaluation functors in the final comparison with C maps to C_n,
as defined by the coefficient-tower abelian theorem, including arbitrary lower bounds.
Source: blueprint, meaning of C_n and last paragraph
(blueprint: det-sp-tower-injective-components).
Proof: evaluation preserves kernels and cokernels by det-sp-coefficient-towers-abelian,
so it preserves quasi-isomorphisms of complexes and descends termwise to the ordinary
derived category. On D+ the same descent has invertible localization unit on every
bounded below complex. Uniqueness for right derived functors identifies this descent
and its unit with the published rightDerivedFunctorPlus construction. -/
theorem sp_tower_evaluation_derived_unit (n : ℕ)
    (L : HomotopyCategory.Plus (spCoefficientTowers l E T)) :
    IsIso ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app L) :=
  by sorry

/-- Derived tower direct image commutes naturally with evaluation. The compatibility
with both derived units fixes the comparison induced by the underived evaluation
identity; it is independent of every injective resolution.
Source: blueprint, last paragraph; Stacks 05TI and 05TH
(blueprint: det-sp-tower-injective-components).

Proof:
1. The tower direct image is additive and left exact, checked levelwise above, and
its source has enough injectives. The right-derived-plus theorem supplies its total
right derived functor and its unit, invertible on bounded below injective complexes.
2. Exact evaluation identifies its evaluated representative with g_* I_n. By
sp_tower_injective_complex_computes this same representative computes Rg_* C_n.
Exact evaluation itself is its own derived functor, identified by its derived unit.
3. The underived evaluation identity and these derived units give a comparison on
the bounded below homotopy category. The universal property of the right derived
functor descends it to D+. The preceding injective computation proves it is invertible.
4. Uniqueness for right derived functors proves independence of the resolution and
naturality in C. It also gives the displayed compatibility with the two units on
every bounded below complex, which uniquely characterizes the natural isomorphism. -/
theorem sp_tower_derived_direct_image_evaluation (n : ℕ) :
    ∃! e : (spTowerPush l E g).rightDerivedFunctorPlus ⋙
        (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlus ≅
      (spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus ⋙
        (spLevelPush l E g n).rightDerivedFunctorPlus,
      ∀ L : HomotopyCategory.Plus (spCoefficientTowers l E T),
        (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlusUnit.app
            ((spTowerPush l E g).mapHomotopyCategoryPlus.obj L) ≫
          (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlus.map
            ((spTowerPush l E g).rightDerivedFunctorPlusUnit.app L) ≫
          e.hom.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map
            ((spTowerEvaluationHomotopyIso l E g dT dS n).hom.app L) ≫
          (spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
            ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj L) ≫
          (spLevelPush l E g n).rightDerivedFunctorPlus.map
            ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app L) :=
  by sorry

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

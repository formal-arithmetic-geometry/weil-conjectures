/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.ConstantCompletionCore

/-!
# Constant coefficient completion: InverseImage

Tower restriction, derived limit restriction, inverse-image data and ringed pullbacks.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation


variable {J A I}

/-- Levelwise restriction on strict module towers. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (ℕᵒᵖ ⥤ Mod B) ⥤ (ℕᵒᵖ ⥤ Mod R) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)

/-- Levelwise restriction is additive and exact, since evaluation computes these laws.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Restriction is additive and exact on module sheaves
by siteRestrictScalars_exact, and finite limits and colimits of functors are pointwise. -/
theorem tres_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive ∧ PreservesFiniteLimits (tres φ) ∧
      PreservesFiniteColimits (tres φ) := by
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  change ((Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)).Additive ∧ _
  dsimp only [tres, res]
  refine ⟨inferInstance, ⟨fun K _ _ ↦ ?_⟩, ⟨fun K _ _ ↦ ?_⟩⟩ <;> infer_instance

/-- The additive structure of the specified levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_additive {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive := (tres_exact φ).1

/-- Finite limits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteLimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits (tres φ) := (tres_exact φ).2.1

/-- Finite colimits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteColimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (tres φ) := (tres_exact φ).2.2

/-- Exact levelwise restriction induces restriction on the derived strict tower categories.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tdres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : TD B ⥤ TD R :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategory

/-- The exact levelwise restriction comparison on strict tower complexes.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tresFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TQ R ≅ TQ B ⋙ tdres φ :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategoryFactors.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite comparisons form a strict tower isomorphism, with all quotient transitions.
The normalization identifies each component with the S_n-linear comparison above.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: on s tensor m, transition then comparison and comparison then transition both give
bar(s) tensor m. Sheafification extends equality; naturality in M gives the functor
isomorphism of strict towers. The component formulas determine it uniquely. -/
theorem reductionTowerComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! e : res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
        reductionTower J A I true ⋙ tres (coefficientMap J A I),
      ∀ (M : Mod (completed J A I)) (n : ℕ) (U : Cᵒᵖ)
        (x : ((change (quotient J A I n)).obj ((res (coefficientMap J A I)).obj M)).val.obj U),
        ((e.hom.app M).app (op n)).val.app U x =
          ((finiteComparison J A I n).hom.app M).val.app U x := by
  let φ := coefficientMap J A I
  have hφ (n : ℕ) : φ ≫ projection J A I n = quotient J A I n := by
    exact limit.lift_π (quotientCone J A I) (op n)
  let en (n : ℕ) : res φ ⋙ reduction J A I false n ≅
      reduction J A I true n ⋙ res φ :=
    Functor.isoWhiskerRight (finiteComparison J A I n) (res (quotient J A I n)) ≪≫
      Functor.isoWhiskerLeft (change (projection J A I n))
        (resCompIso φ (projection J A I n) (quotient J A I n) (hφ n)).symm
  have hen (n : ℕ) (M : Mod (completed J A I)) (U : Cᵒᵖ)
      (x : ((change (quotient J A I n)).obj ((res φ).obj M)).val.obj U) :
      ((en n).hom.app M).val.app U x =
        ((finiteComparison J A I n).hom.app M).val.app U x := by
    change ((resCompIso φ (projection J A I n) (quotient J A I n) (hφ n)).inv.app
      ((change (projection J A I n)).obj M)).val.app U
        (((finiteComparison J A I n).hom.app M).val.app U x) = _
    exact resCompIso_inv_apply φ (projection J A I n) (quotient J A I n) (hφ n)
      ((change (projection J A I n)).obj M) U
      (((finiteComparison J A I n).hom.app M).val.app U x)
  have hfinite (n : ℕ) (M : Mod (completed J A I)) (U : Cᵒᵖ)
      (s : (finite J A I n).obj.obj U) (m : M.val.obj U) :
      ((finiteComparison J A I n).hom.app M).val.app U
          (tensorSection (quotient J A I n) ((res φ).obj M) U s m) =
        tensorSection (projection J A I n) M U s m :=
    (finiteComparison_existsUnique J A I n).exists.choose_spec M U s m
  clear_value en
  have hstep (M : Mod (completed J A I)) (n : ℕ) :
      ((reductionTower J A I false).obj ((res φ).obj M)).map
          (homOfLE (Nat.le_succ n)).op ≫ (en n).hom.app M =
        (en (n + 1)).hom.app M ≫
          ((tres φ).obj ((reductionTower J A I true).obj M)).map
            (homOfLE (Nat.le_succ n)).op := by
    simp only [reductionTower, tres, Functor.whiskeringRight_obj_obj,
      Functor.comp_map, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply restrictedTensor_hom_ext (quotient J A I (n + 1)) ((res φ).obj M)
    intro U s m
    change ((en n).hom.app M).val.app U
        (((reductionStep J A I false n).app ((res φ).obj M)).val.app U
          (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m)) =
      ((reductionStep J A I true n).app M).val.app U
        (((en (n + 1)).hom.app M).val.app U
          (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m))
    rw [hen, hen, hfinite]
    rw [show ((reductionStep J A I false n).app ((res φ).obj M)).val.app U
        (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m) =
      tensorSection (quotient J A I n) ((res φ).obj M) U
        ((transition J A I n).hom.app U s) m from
          (reductionStep_existsUnique J A I false n).exists.choose_spec _ U s m]
    rw [hfinite]
    exact ((reductionStep_existsUnique J A I true n).exists.choose_spec M U s m).symm
  let e : res φ ⋙ reductionTower J A I false ≅
      reductionTower J A I true ⋙ tres φ :=
    NatIso.ofComponents
      (fun M ↦ NatIso.ofComponents (fun n ↦ (en n.unop).app M)
        (fun f ↦ (NatTrans.ofOpSequence
          (F := (reductionTower J A I false).obj ((res φ).obj M))
          (G := (tres φ).obj ((reductionTower J A I true).obj M))
          (fun n ↦ (en n).hom.app M) (hstep M)).naturality f))
      (by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (en n.unop).hom.naturality f)
  refine ⟨e, fun M n U x ↦ hen n M U x, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact (he' M n.unop U x).trans (hen n.unop M U x).symm

/-- The strict tower comparison with the prescribed S_n-linear finite components.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
      reductionTower J A I true ⋙ tres (coefficientMap J A I) :=
  (reductionTowerComparison_existsUnique J A I).exists.choose

/-- Restricting before forming the strict quotient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at every tower index the functor is scalar restriction followed by scalar
extension and restriction. All three maps preserve sums of module homomorphisms.
Equality after every evaluation is equality in the strict functor category. -/
theorem restrictionReduction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).Additive := by
  have : (res (coefficientMap J A I)).Additive := inferInstance
  constructor
  intro M N f g
  change (reductionTower J A I false).map
    ((res (coefficientMap J A I)).map (f + g)) = _
  rw [Functor.map_add]
  exact Functor.map_add (reductionTower J A I false)

attribute [instance] restrictionReduction_additive

/-- Reducing and then restricting a completed-coefficient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Scalar extension and both restrictions preserve
addition of module maps, so their composite does as well. -/
theorem reductionRestriction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).Additive := by
  infer_instance

attribute [instance] reductionRestriction_additive

/-- The completed strict reduction followed by restriction preserves zero maps.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the additive identity of reductionRestriction_additive to the zero map. -/
theorem reductionRestriction_preservesZero (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).PreservesZeroMorphisms := by
  infer_instance

attribute [instance] reductionRestriction_preservesZero

-- Use the generic composite-functor instances while elaborating the remaining proofs.
-- Restore the exported instances at the end of the module.
attribute [-instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero


/-- Apply the prescribed strict tower comparison termwise to complexes.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparisonComplex (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionTower J A I false).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionTower J A I true).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  letI := reductionTower_additive J A I false
  letI := reductionTower_additive J A I true
  liftIso (res (coefficientMap J A I)) (reductionTower J A I false)
    (reductionTower J A I true) (tres (coefficientMap J A I))
    (reductionTowerComparison J A I)

/-- The representative computation square for a derived comparison of strict towers.
The functors are abstract here so that checking the equation never unfolds any concrete
scalar-restriction or reduction-tower construction. The four sides are the restriction
computation, the two derived-tower computations, and their strict comparison.
Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def DerivedTowerComparisonFormula
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Category A₅] [Category A₆] [Category A₇]
    {qB : A₀ ⥤ A₄} {qR : A₁ ⥤ A₅} {tqB : A₂ ⥤ A₆} {tqR : A₃ ⥤ A₇}
    {rc : A₀ ⥤ A₁} {tc : A₂ ⥤ A₃} {dr : A₄ ⥤ A₅} {dt : A₆ ⥤ A₇}
    {tr : A₅ ⥤ A₇} {tb : A₄ ⥤ A₆} {redR : A₁ ⥤ A₃} {redB : A₀ ⥤ A₂}
    (α : rc ⋙ qR ≅ qB ⋙ dr) (βR : qR ⋙ tr ⟶ redR ⋙ tqR)
    (γ : rc ⋙ redR ≅ redB ⋙ tc) (δ : tc ⋙ tqR ≅ tqB ⋙ dt)
    (βB : qB ⋙ tb ⟶ redB ⋙ tqB) (e : dr ⋙ tr ≅ tb ⋙ dt) (P : A₀) : Prop :=
  tr.map (α.inv.app P) ≫ βR.app (rc.obj P) ≫ tqR.map (γ.hom.app P) ≫
      δ.hom.app (redB.obj P) = e.hom.app (qB.obj P) ≫ dt.map (βB.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_tower_square
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : r ⋙ q₁ ≅ DerivedCategory.Q ⋙ dr)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : s ⋙ q₃ ≅ q₂ ⋙ ds)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X)) :
    ∃ e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X →
      DerivedTowerComparisonFormula α β γ ε δ e X := by
  let T := b ⋙ s ⋙ q₃
  let a : DerivedCategory.Q ⋙ (dr ⋙ dp) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.inv _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft r β ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ.hom _ ≫
      (Functor.associator _ _ _).hom
  let z : DerivedCategory.Q ⋙ (db ⋙ ds) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight δ _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft b ε.inv
  have ha X (hX : P X) : IsIso (a.app X) := by
    have := hβ X hX
    dsimp only [a, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hz X (hX : P X) : IsIso (z.app X) := by
    have := hδ X hX
    dsimp only [z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, he⟩ := resolving_comparison_iso (dr ⋙ dp) (db ⋙ ds) T P hres a z ha hz
  refine ⟨e, ?_⟩
  intro X hX
  have h := he X hX
  dsimp only [a, z, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [Category.id_comp, Category.comp_id] at h
  have h' : (e.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X)) ≫
      ε.inv.app (b.obj X) =
      dp.map (α.inv.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) := by
    simpa only [Category.assoc] using h
  simpa only [DerivedTowerComparisonFormula, Category.assoc, Iso.app_hom] using
    ((ε.app (b.obj X)).comp_inv_eq.mp h').symm

section
attribute [local irreducible] dres change

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The strict comparison descends through the universal derived-tower construction.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: restrict one flat-term K-flat B-representative, which remains K-flat by flatness
of the coefficient extension. Apply the strict tower comparison and both universal
computation counits. Their invariance under quasi-isomorphisms gives the derived natural
isomorphism, and the formula is exactly its normalized representative computation. -/
theorem derivedReductionTowerComparison (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : dres (coefficientMap J A I) ⋙ (quotientPresentation J A I false).tower ≅
        (quotientPresentation J A I true).tower ⋙ tdres (coefficientMap J A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedTowerComparisonFormula (resFactors (coefficientMap J A I))
          (quotientPresentation J A I false).comparison (reductionTowerComparisonComplex J A I)
          (tresFactors (coefficientMap J A I))
          (quotientPresentation J A I true).comparison e P := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (constant J A))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (completed J A I))
  let φ := coefficientMap J A I
  let r := (res φ).mapHomologicalComplex (.up ℤ)
  let pR := quotientPresentation J A I false
  let pB := quotientPresentation J A I true
  let P (X : Cx (completed J A I)) :=
    X.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (X.X q)
  obtain ⟨e, he⟩ := resolving_tower_square
    (Q (constant J A)) (TQ (completed J A I)) (TQ (constant J A))
    r ((reductionTower J A I true).mapHomologicalComplex (.up ℤ))
    ((reductionTower J A I false).mapHomologicalComplex (.up ℤ))
    ((tres φ).mapHomologicalComplex (.up ℤ))
    (dres φ) pB.tower pR.tower (tdres φ)
    (resFactors φ) pR.comparison (reductionTowerComparisonComplex J A I)
    pB.comparison (tresFactors φ) P (module_flat_kFlat_resolution (J := J))
    (fun X hX ↦ pR.laws.2.1 _
      (restricted_kFlat φ (flat_and_quotients J A I).1 X hX.1)
      (restricted_flat φ (flat_and_quotients J A I).1 X hX.1 hX.2))
    (fun X hX ↦ pB.laws.2.1 X hX.1 hX.2)
  exact ⟨e, fun X hk hf ↦ he X ⟨hk, hf⟩⟩

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary inverse limits commute with scalar restriction by their coordinate maps.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: module restriction preserves limits, computed on underlying additive sheaves.
The limit comparison is invertible degreewise and commutes with differentials. Its
coordinate equations determine it uniquely, so this is a canonical chain isomorphism. -/
theorem limitRestriction_existsUnique {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ∃! e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R,
      ∀ (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ),
        (e.hom.app P).f q ≫
          limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
        (res φ).map (limit.π (P.X q) (op n)) := by
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  have liftIso_hom_f {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K)
      (P : CochainComplex A₀ ℤ) (q : ℤ) :
      ((liftIso F G H K e).hom.app P).f q = e.hom.app (P.X q) := by
    dsimp only [liftIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex, NatTrans.comp_app, HomologicalComplex.comp_f]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let α : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  let e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
    liftIso (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) (res φ) (tres φ)
      (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) α
  have he (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ) :
      (e.hom.app P).f q ≫
        limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
      (res φ).map (limit.π (P.X q) (op n)) := by
    change ((liftIso _ _ _ _ α).hom.app P).f q ≫ _ = _
    rw [liftIso_hom_f]
    exact preservesLimitIso_hom_π (res φ) (P.X q) (op n)
  refine ⟨e, he, ?_⟩
  intro g hg
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  exact (hg P q n.unop).trans (he P q n.unop).symm

/-- The ordinary limit comparison fixed by its actual projections. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitRestriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
  (limitRestriction_existsUnique φ).exists.choose

section ExactScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The proved extension-tensor comparison, selected once for each module. -/
private def extensionTensorComponent {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : Mod R) :
    (SheafOfModules.monoidalCategory R).tensorObj
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M ≅
        (res φ).obj ((change φ).obj M) :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose

/-- Its section formula is the original balanced tensor map. -/
private theorem extensionTensorComponent_pure {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (M : Mod R) (U : Cᵒᵖ) (s : B.obj.obj U) (m : M.val.obj U) :
    (extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R
          ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M U s m) =
      tensorSection φ M U s m :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose_spec U s m

attribute [irreducible] extensionTensorComponent

/-- The pure-tensor comparison is natural in the module argument.
Source: Stacks 03EK; the component is exists_extensionTensorComparison. -/
private def extensionTensorIso {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    MonoidalCategory.tensorLeft ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) ≅
      change φ ⋙ res φ := by
  letI := SheafOfModules.monoidalCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  refine NatIso.ofComponents (extensionTensorComponent φ) ?_
  intro M M' f
  apply SheafOfModules.RingedTensor.pure_hom_ext R N M
  intro U s m
  change (extensionTensorComponent φ M').hom.val.app U
      ((MonoidalCategory.whiskerLeft N f).val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m)) =
    ((change φ).map f).val.app U
      ((extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m))
  rw [← MonoidalCategory.id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  change (extensionTensorComponent φ M').hom.val.app U
      (SheafOfModules.RingedTensor.pure R N M' U s (f.val.app U m)) = _
  rw [extensionTensorComponent_pure, extensionTensorComponent_pure]
  exact (tensorSection_map φ f U s m).symm

/-- Flatness of the target ring makes scalar extension exact.
Source: Stacks 03EK. Identify its restriction with tensoring by the flat target,
reflect finite limits through restriction, and use the extension adjunction for colimits. -/
private theorem change_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    PreservesFiniteLimits (change φ) ∧ PreservesFiniteColimits (change φ) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight N) := hflat.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have : PreservesFiniteLimits (change φ ⋙ res φ) :=
    preservesFiniteLimits_of_natIso (extensionTensorIso φ)
  have : (res φ).ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  have : PreservesFiniteLimits (res φ) := (siteRestrictScalars_exact φ).1
  have : ReflectsFiniteLimits (res φ) :=
    { reflects := fun K _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have hleft : PreservesFiniteLimits (change φ) :=
    preservesFiniteLimits_of_reflects_of_preserves (change φ) (res φ)
  have : PreservesColimitsOfSize.{0, 0} (change φ) :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).leftAdjoint_preservesColimits
  have hright : PreservesFiniteColimits (change φ) := inferInstance
  exact ⟨hleft, hright⟩

end ExactScalarExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact restriction/limit square derives by the tower adjunction.
The abstract ring parameters prevent elaboration from unfolding a completion limit. -/
private theorem derivedLimitRestriction_of_flat {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    ∃ e : rlim B ⋙ dres φ ≅
        tdres φ ⋙ rlim R,
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ,
        (dres φ).map ((limitComparison B).app P) ≫
          e.hom.app ((TQ B).obj P) =
        (resFactors φ).inv.app
            ((ordinaryLimit B).obj P) ≫
          (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app
            (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim R).map ((tresFactors φ).hom.app P) := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with
      toPreadditive := (inferInstance : Preadditive (Mod R)) }
  let : Abelian (Mod B) :=
    { (inferInstance : Abelian (Mod B)) with
      toPreadditive := (inferInstance : Preadditive (Mod B)) }
  let : Abelian (ℕᵒᵖ ⥤ Mod R) :=
    { (inferInstance : Abelian (ℕᵒᵖ ⥤ Mod R)) with
      toPreadditive := (inferInstance : Preadditive (ℕᵒᵖ ⥤ Mod R)) }
  let : Abelian (ℕᵒᵖ ⥤ Mod B) :=
    { (inferInstance : Abelian (ℕᵒᵖ ⥤ Mod B)) with
      toPreadditive := (inferInstance : Preadditive (ℕᵒᵖ ⥤ Mod B)) }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod B)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ Mod B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian J (siteModuleRings B)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have hex := change_exact φ hflat
  have : PreservesFiniteLimits (change φ) := hex.1
  have : PreservesFiniteColimits (change φ) := hex.2
  let E := (Functor.whiskeringRight ℕᵒᵖ (Mod R) (Mod B)).obj (change φ)
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : E.PreservesHomology := {}
  have adj : E ⊣ tres φ :=
    Adjunction.whiskerRight ℕᵒᵖ (SheafOfModules.RingedTensor.tensorAdjunction φ)
  have : (tres φ).PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let c : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  obtain ⟨e, he⟩ := towerComparison_existsLimitIso (res φ) (dres φ) (tdres φ)
    (rlim B) (rlim R) (resFactors φ).hom (tresFactors φ).hom
    (limitComparison B) (limitComparison R)
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    (strictLimit B).computation
    (fun P hP ↦ by
      have := hP
      change IsIso ((limitComparison R).app
        (((tres φ).mapHomologicalComplex (.up ℤ)).obj P))
      exact (strictLimit R).computation _ inferInstance) c
  refine ⟨e, ?_⟩
  intro P
  have h := he P
  have hc : (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P =
      (limitRestriction φ).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change c.hom.app (P.X q) ≫ limit.π _ n = _
    exact (preservesLimitIso_hom_π (res φ) (P.X q) n).trans
      ((limitRestriction_existsUnique φ).exists.choose_spec P q n.unop).symm
  rw [hc] at h
  apply (cancel_epi ((resFactors φ).hom.app ((ordinaryLimit B).obj P))).mp
  change (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (dres φ).map ((limitComparison B).app P) ≫ e.hom.app ((TQ B).obj P) =
    (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (resFactors φ).inv.app ((ordinaryLimit B).obj P) ≫
        (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app (((tres φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            (rlim R).map ((tresFactors φ).hom.app P)
  rw [Iso.hom_inv_id_app_assoc]
  exact h


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction identifies total right derived limits of strict towers, canonically.
The comparison is normalized by the ordinary limit coordinate comparison and both
right-derived universal transformations. Source: Stacks 0940 and 0A07
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: extension of scalars is exact by flat_and_quotients, and restriction is its exact
right adjoint. This adjunction holds levelwise on strict towers, so the right-adjoint
K-injective theorem sends a K-injective tower resolution to one over the constant ring.
Ordinary limits agree by their coordinates. Apply the universal right-derived
comparisons to obtain the natural isomorphism and its displayed normalization. -/
theorem derivedLimitRestriction (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : rlim (completed J A I) ⋙ dres (coefficientMap J A I) ≅
        tdres (coefficientMap J A I) ⋙ rlim (constant J A),
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ,
        (dres (coefficientMap J A I)).map ((limitComparison (completed J A I)).app P) ≫
          e.hom.app ((TQ (completed J A I)).obj P) =
        (resFactors (coefficientMap J A I)).inv.app
            ((ordinaryLimit (completed J A I)).obj P) ≫
          (Q (constant J A)).map ((limitRestriction (coefficientMap J A I)).hom.app P) ≫
          (limitComparison (constant J A)).app
            (((tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim (constant J A)).map ((tresFactors (coefficientMap J A I)).hom.app P) := by
  exact derivedLimitRestriction_of_flat (coefficientMap J A I)
    (flat_and_quotients J A I).1

/-- Forget a module sheaf to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev underlying (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ Sheaf J (Type u) :=
  SheafOfModules.toSheaf (siteModuleRings O) ⋙ sheafCompose J (forget AddCommGrpCat)

/-- A sheaf map with a fixed section formula is unique. -/
private theorem sheaf_map_existsUnique_of_formula {X Y : Sheaf J (Type u)}
    (q : X ⟶ Y) (f : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U)
    (hq : ∀ U x, q.hom.app U x = f U x) :
    ∃! q' : X ⟶ Y, ∀ U x, q'.hom.app U x = f U x := by
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro m
  exact (hq' U m).trans (hq U m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-extension insertion is the unique underlying-sheaf map m ↦ 1 tensor m.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the section formula commutes with restrictions by the pure-tensor formula for
changeOfRingsMap and naturality of the sheafification unit. Components determine the map. -/
theorem insertion_existsUnique {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    ∃! q : (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M),
      ∀ (U : Cᵒᵖ) (m : M.val.obj U), q.hom.app U m = tensorSection φ M U 1 m := by
  let η := (scalarExtensionUnit_exists J φ).choose
  exact sheaf_map_existsUnique_of_formula
    ((underlying R).map (η.app M))
    (fun U m ↦ tensorSection φ M U 1 m)
    ((scalarExtensionUnit_exists J φ).choose_spec M)

/-- The actual scalar-extension insertion, including sheafification.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def insertion {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M) :=
  (insertion_existsUnique φ M).exists.choose

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

set_option genSizeOf false in
set_option genInjectivity false in
/-- Algebraic lifts of a topos inverse image, coherently in all coefficient rings.
The existing AlgebraicInverseImage specifies every ring operation and module action on
all generalized sections. Naturality specifies its action on ring maps. The constant
comparison is natural in every commutative ring, fixing the canonical constant-object
identification, including its coefficient maps.
Source: Stacks 00YV, 03D2, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure InverseImageData (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)) where
  rings : Sheaf J CommRingCat.{u} ⥤ Sheaf J' CommRingCat.{u}
  algebra : ∀ O : Sheaf J CommRingCat.{u},
    SheafOfModules.AlgebraicInverseImage L O (rings.obj O)
  ring_naturality : ∀ {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S),
    L.map ((sheafCompose J (forget CommRingCat)).map φ) ≫ (algebra S).ringUnderlying.hom =
      (algebra R).ringUnderlying.hom ≫
        (sheafCompose J' (forget CommRingCat)).map (rings.map φ)
  constants : constantSheaf J CommRingCat.{u} ⋙ rings ≅ constantSheaf J' CommRingCat.{u}


variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image maps to finite coefficients form the canonical projection cone.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply F.rings to projection naturality and use naturality of F.constants for
A/I^(n+2) → A/I^(n+1). These are exactly the displayed cone equations. -/
theorem pulledProjection_naturality (A : Type u) [CommRing A] (I : Ideal A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map f ≫
        (F.rings.map (projection J A I n.unop) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom) =
      (F.rings.map (projection J A I m.unop) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (m.unop + 1)))).hom) ≫
          (finiteSystem J' A I).map f := by
  have hstep (k : ℕ) :
      ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map
          (homOfLE (Nat.le_succ k)).op ≫
        (F.rings.map (projection J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) =
      (F.rings.map (projection J A I (k + 1)) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
        (finiteSystem J' A I).map (homOfLE (Nat.le_succ k)).op := by
    simp only [Functor.const_obj_map, finiteSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    change F.rings.map (projection J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.rings.map (projection J A I (k + 1)) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
          transition J' A I k
    have hnat := F.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))))
    change F.rings.map (transition J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom ≫
        transition J' A I k at hnat
    have hproj : projection J A I (k + 1) ≫ transition J A I k =
        projection J A I k := by
      unfold projection completed
      simpa only [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ k)).op
    calc
      _ = F.rings.map (projection J A I (k + 1) ≫ transition J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom := by rw [hproj]
      _ = _ := by rw [F.rings.map_comp, Category.assoc, hnat, Category.assoc]
  exact (NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I)))
    (G := finiteSystem J' A I)
    (fun k ↦ F.rings.map (projection J A I k) ≫
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) hstep).naturality f

attribute [local semireducible] completed

/-- The canonical map from the inverse image of the completed coefficient sheaf to the
completion on the second site, formed from its finite projections.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completedMap (A : Type u) [CommRing A] (I : Ideal A) :
    F.rings.obj (completed J A I) ⟶ completed J' A I :=
  limit.lift (finiteSystem J' A I)
    { pt := F.rings.obj (completed J A I)
      π :=
        { app := fun n ↦ F.rings.map (projection J A I n.unop) ≫
            (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom
          naturality := fun {m n} f ↦ pulledProjection_naturality F A I (m := m) (n := n) f } }

attribute [local irreducible] completed

/-- Module inverse image followed by the existing sheafified scalar extension.
Source: Stacks 03D2, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Mod R ⥤ Mod S :=
  (F.algebra R).modules ⋙ change c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Addition transport and underlying naturality make the algebraic module lift additive.
Abstracting the lift avoids repeatedly reducing the full inverse-image data record. -/
private theorem algebraModules_additive {R : Sheaf J CommRingCat.{u}}
    {RI : Sheaf J' CommRingCat.{u}}
    (AI : SheafOfModules.AlgebraicInverseImage L R RI) : AI.modules.Additive := by
  constructor
  intro M N f g
  ext U x
  let e := AI.moduleUnderlying
  let y := (e.hom.app M).hom.app U x
  have hy : (e.inv.app M).hom.app U y = x :=
    congrFun (congrArg (fun t ↦ t.hom.app U) (e.hom_inv_id_app M)) x
  have hn (k : M ⟶ N) :
      (e.inv.app N).hom.app U ((L.map ((underlying R).map k)).hom.app U y) =
        (AI.modules.map k).val.app U x := by
    have hh := congrFun
      (congrArg (fun t ↦ t.hom.app U) (e.inv.naturality k)) y
    change _ = (AI.modules.map k).val.app U
      ((e.inv.app M).hom.app U y) at hh
    exact hh.trans (congrArg ((AI.modules.map k).val.app U) hy)
  have h := AI.moduleAdd N ((underlying R).obj M)
    ((underlying R).map f) ((underlying R).map g) ((underlying R).map (f + g))
    (fun _ _ ↦ rfl) U y
  exact (hn (f + g)).symm.trans
    (h.trans (congrArg₂ (fun (a b : (AI.modules.obj N).val.obj U) ↦ a + b)
      (hn f) (hn g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This prescribed module pullback is additive.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the algebraic inverse-image lift preserves addition by its generalized-section
moduleAdd identity. The scalar-extension functor is additive, hence so is their composite. -/
theorem pull_additive {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : (pull F c).Additive := by
  have := algebraModules_additive (F.algebra R)
  change ((F.algebra R).modules ⋙ change c).Additive
  infer_instance

attribute [instance] pull_additive

/-- Insertion after inverse image: u^(-1)M → u^(-1)M tensor S, with coefficient action
fixed by c. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullInsertion {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (M : Mod R) :
    L.obj ((underlying R).obj M) ⟶ (underlying S).obj ((pull F c).obj M) :=
  (F.algebra R).moduleUnderlying.inv.app M ≫ insertion c ((F.algebra R).modules.obj M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universally specified derived pullback with computation on flat-term K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure DerivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶ (pull F c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded K-flat derived-pullback theorem supplies this universal derived pair.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply ringedTopoiDerivedPullback to the supplied geometric adjunction and algebraic
lift; pull has exactly its specified scalar-extension objects and maps. Flat-term K-flat
resolutions supply its resolving class. Transport the universal homotopy counit through
the quotient factorization to obtain the complex-level universal pair and computation. -/
theorem derivedPull_exists (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Nonempty (DerivedPull F c) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨T, ε, hu, _, _, hc, _⟩ :=
    SheafOfModules.ringedTopoiDerivedPullback L V adj (F.algebra R) c (pull F c) ho hm
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) := hu
  have : T.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
      (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
  obtain ⟨β, hβ, hcomp⟩ := cochain_derived_counit (pull F c) T ε
  exact ⟨{ functor := T
           comparison := β
           universal := ⟨hβ⟩
           computation := fun P hp hf ↦ hcomp P (hc P hp hf) }⟩

variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The live K-flat and monoidal-flat interface for a prescribed ringed pullback. -/
private theorem basechange_flat_kFlat
    {R : Sheaf J CommRingCat.{u}} {RI S : Sheaf J' CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (AI : SheafOfModules.AlgebraicInverseImage L R RI)
    (c : RI ⟶ S) (T : Mod R ⥤ Mod S) [T.Additive]
    (ho : ∀ M : Mod R, T.obj M = SheafOfModules.changeOfRings c (AI.modules.obj M))
    (hm : ∀ {M N : Mod R} (f : M ⟶ N), T.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom c (AI.modules.obj M) (AI.modules.map f) ≫
        eqToHom (ho N).symm)
    (P : Cx R) (hP : P.IsAcyclicTensorKFlat)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      ((T.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat (T.obj (P.X q)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  have hf' (q : ℤ) := (exactFunctor (Mod R) (Mod R)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X q)).symm (hf q)
  obtain ⟨hk, hflat⟩ := SheafOfModules.isKFlat_ringedToposPullback L V adj
    AI c T ho hm P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf'
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro q
  exact (exactFunctor (Mod S) (Mod S)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S (T.obj (P.X q))) (hflat q)

include V adj hL in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_flat_kFlat {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S) (P : Cx R)
    (hP : P.IsAcyclicTensorKFlat) (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      (((pull F c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((pull F c).obj (P.X q)) := by
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact basechange_flat_kFlat L V adj (F.algebra R) c (pull F c) ho hm P hP hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem change_flat_kFlat {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (P : Cx R) (hP : P.IsAcyclicTensorKFlat)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      (((change c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((change c).obj (P.X q)) := by
  have ho (M : Mod R) : (change c).obj M = SheafOfModules.changeOfRings c M := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (change c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c M f ≫
        eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨hk, hflat⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      c P (change c) ho hm
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, hflat⟩


/-- Choose the derived pullback with its universal comparison, not an arbitrary lift.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : DerivedPull F c :=
  Classical.choice (derivedPull_exists F V adj c)

attribute [local irreducible] derivedPull pull change

/-- The canonical constant-coefficient structural isomorphism.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def constantMap (A : Type u) [CommRing A] : F.rings.obj (constant J A) ⟶ constant J' A :=
  (F.constants.app (CommRingCat.of A)).hom

end CategoryTheory.ConstantCompletion

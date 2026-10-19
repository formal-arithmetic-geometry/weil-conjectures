/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearDerivedCalculus
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.SemilinearGeometryOps
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Ordinary derived semilinear sections

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, Lemma 4.10 and Proposition
  4.17;
Stacks Project, Tags 0941, 079P, 06YS, 06YY, 07A4, 07A6 and 08J7--08JB
(blueprint: lem-coef-semilinear-derived-sections).

The categories below are module sheaves on the actual vertical sequence site and their
ordinary unbounded derived categories. All comparisons have specified sources, targets
and equations; there are no free proposition-valued parameters.

## Main definitions and statements

- `Systems`, `DS`: strict semilinear systems and their ordinary derived category.
- `Data`, `Geometry`, `OpenSystems`: the coefficient, geometric and localized calculus.
- `TensorComparisonModel`, `InverseTensorPure`: representative and pure-tensor normalization.
- `semilinearDerivedSections`: existence of the complete ordinary-derived calculus.
- `evaluation_mate`: compatibility of specified adjunction transposes with evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- All operations of the ordinary-derived semilinear system statement, on its
actual categories and with their specified maps and equations.
Source: Zheng 4.1 and 4.10; Stacks 06YY, 07A4, 08J7--08JB
(blueprint: lem-coef-semilinear-derived-sections). -/
structure SemilinearDerivedSectionsData where
  /-- The actual abelian/derived system calculus. -/
  systems : Data.{c, v, r} J B τ
  /-- The specified cartesian internal-Hom reduction formula. -/
  homTransition : systems.HomReductionFormula J B τ
  /-- A morphism of topoi induces the actual geometric system operations. -/
  geometric : ∀ {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv],
    {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.TransitionFormula J B τ systems J' uInv uPush adjSet ∧
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet ∧
      G.ProjectionEvaluation J B τ systems J' uInv uPush adjSet}
  /-- Compatible coefficient-system maps have the stated scalar-extension calculus. -/
  coefficientExtension : ∀ (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n),
    ScalarSystems.{c, v, r} J B τ F σ α hα
  /-- Exact open-localization operations with the actual normalized level adjunctions. -/
  localization : ∀ U : C, OpenSystems.{c, v, r} J B τ U

/-- Ordinary derived semilinear sections and their coefficient-linear operations.
Source: Zheng, Construction 4.1, Lemma 4.10 and Proposition 4.17; Stacks 079P, 06YS, 06YY, 07A4,
07A6, 08J7--08JB (blueprint: lem-coef-semilinear-derived-sections).
Proof: the vertical sequence site identifies module sheaves with strict semilinear
systems. Kernels and sheafified cokernels are componentwise; Grothendieck abelianness
and K-injective resolutions apply to this small ringed site. Termwise exact evaluation
therefore descends to the ordinary localization, with componentwise cones proving
joint conservativity. Transpose the actual horizontal restrictions by the normalized
K-flat scalar-extension adjunctions to obtain the reductions; tensor reassociation
and the strict tower cocycle prove their composition formula.
Apply inverse image and direct image to the strict systems. Their ordinary adjunction
is componentwise. Resolve on the system site to derive direct image. Finite left
extension adjoints to evaluation, computed by coefficient extension below the given
index and zero above it, identify evaluation of derived direct image by Yoneda; no
preservation of K-injectives by evaluation is required. Choose the ordinary
component realizations with the identity on section carriers. On K-injective
targets the derived Hom equivalence is the localization of the ordinary one,
using the actual right-derived comparison isomorphism. This fixes the derived
adjunction before evaluation. The restriction coefficient comparison is the
identity on underlying sheaves; its scalar-adjunction transpose fixes coefficient
pullback. Transposing the coefficient
pullback comparison gives exactly coefficientMate and the displayed transition
formula. The unit and counit formulas follow from the same Hom correspondence.
For localization, take the levelwise direct-sum extension presheaves and sheafify;
their summand Hom correspondence gives the normalized adjunction. Exactness gives
the termwise derived pair. A compatible ring-system map gives the sectionwise ring
map systemMap, so the recorded change-of-rings universal pair on the sequence site
is its scalar extension. The restriction evaluation identity gives its level tensor
comparison by adjunction. K-flat resolutions and total tensor on the sequence site
likewise give tensorEvaluation. For geometric tensor pullback, first use the
inverse-image formula on generalized pure tensors. On each total summand use
exactly its inverse ordinary map; the signed differential gives the chain map.
Localize on K-flat representatives with flat terms on the system category itself. This fixes
tensorPullback without any inference from evaluations of derived morphisms.
Tensor-Hom adjunction and the finite left extensions
to evaluation give homEvaluation precisely when the first input is cartesian. Its
evaluation normalization forces its transition to be homReductionTranspose, by
adjunction and the inverse cartesian reduction. Finally transpose tensor pullback
followed by counit tensor identity: this is tensorProjection. The unit/counit and
tensor evaluation equations give ProjectionEvaluation. Naturality, exchange and
composition of these actual transformations are the ordinary mate words; their
evaluation compatibility is evaluation_mate below and their pasting laws are the
recorded mateEquiv_vcomp and mateEquiv_hcomp. No conservativity assertion is used
to infer equality of arbitrary derived morphisms. -/
theorem semilinearDerivedSections :
    Nonempty (SemilinearDerivedSectionsData.{c, v, r} J B τ) := by
  sorry

end WeilConjectures.SemilinearSections

namespace WeilConjectures.SemilinearSections
section CategoricalEvaluation

variable {X Y Z W x y z w : Type k}
  [Category.{k} X] [Category.{k} Y] [Category.{k} Z] [Category.{k} W]
  [Category.{k} x] [Category.{k} y] [Category.{k} z] [Category.{k} w]

/-- A pair of evaluation comparisons normalized by both adjunction identities.
This categorical helper is applied to the actual system and level categories above.
Source: Zheng 4.10; Mathlib Adjunction.Mates
(blueprint: lem-coef-semilinear-derived-sections). -/
structure AdjunctionEvaluation (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
    {l : x ⥤ y} {r : y ⥤ x} (level : l ⊣ r) where
  /-- Evaluation of the left adjoint. -/
  left : L ⋙ F ≅ E ⋙ l
  /-- Evaluation of the right adjoint. -/
  right : R ⋙ E ≅ F ⋙ r
  /-- Unit evaluation. -/
  unit : ∀ A : X,
    E.map (adj.unit.app A) ≫ right.hom.app (L.obj A) ≫
      r.map (left.hom.app A) = level.unit.app (E.obj A)
  /-- Counit evaluation. -/
  counit : ∀ B : Y,
    l.map (right.hom.app B) ≫ level.counit.app (F.obj B) =
      left.inv.app (R.obj B) ≫ F.map (adj.counit.app B)

/-- Evaluation commutes with the specified ordinary adjunction-mate word.
It applies also to the open adjunction and to adjunctions formed by composition,
so the existing mate-pasting identities include proper direct-image composition.
Source: Zheng 4.10; Stacks 07A4; Mathlib mateEquiv_vcomp and mateEquiv_hcomp
(blueprint: lem-coef-semilinear-derived-sections).
Proof: expand mateEquiv as unit, the given square, and counit. Substitute the two
unit/counit evaluation equations, and the square evaluation equation. Naturality
moves the four comparison isomorphisms through the three factors; their inverse
pairs cancel. The result is the level mate word. Applying the same calculation to
composable squares and then mateEquiv_vcomp or mateEquiv_hcomp proves the evaluation
and pasting assertions simultaneously. This uses equations of constructed words,
not detection of equality by evaluation. -/
theorem evaluation_mate
    {E₁ : X ⥤ x} {F₁ : Y ⥤ y} {E₂ : Z ⥤ z} {F₂ : W ⥤ w}
    {L₁ : X ⥤ Y} {R₁ : Y ⥤ X} {L₂ : Z ⥤ W} {R₂ : W ⥤ Z}
    {l₁ : x ⥤ y} {r₁ : y ⥤ x} {l₂ : z ⥤ w} {r₂ : w ⥤ z}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂)
    (A₁ : AdjunctionEvaluation E₁ F₁ adj₁ level₁)
    (A₂ : AdjunctionEvaluation E₂ F₂ adj₂ level₂)
    {G : X ⥤ Z} {H : Y ⥤ W} {g : x ⥤ z} {h : y ⥤ w}
    (γ : G ⋙ E₂ ≅ E₁ ⋙ g) (η : H ⋙ F₂ ≅ F₁ ⋙ h)
    (α : TwoSquare G L₁ L₂ H) (a : TwoSquare g l₁ l₂ h)
    (compatible : ∀ A : X,
      F₂.map (α.app A) ≫ η.hom.app (L₁.obj A) ≫ h.map (A₁.left.hom.app A) =
        A₂.left.hom.app (G.obj A) ≫ l₂.map (γ.hom.app A) ≫ a.app (E₁.obj A)) :
    ∀ B : Y,
      E₂.map ((mateEquiv adj₁ adj₂ α).app B) ≫ A₂.right.hom.app (H.obj B) ≫
          r₂.map (η.hom.app B) =
        γ.hom.app (R₁.obj B) ≫ g.map (A₁.right.hom.app B) ≫
          (mateEquiv level₁ level₂ a).app (F₁.obj B) := by
  intro B
  apply (level₂.homEquiv _ _).symm.injective
  change l₂.map _ ≫ level₂.counit.app _ = l₂.map _ ≫ level₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (A₂.left.hom.app (G.obj (R₁.obj B)))).1
  have hleft := A₂.left.hom.naturality ((mateEquiv adj₁ adj₂ α).app B)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft]
  have hcounit := level₂.counit.naturality (η.hom.app B)
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  rw [hcounit]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (A₂.counit (H.obj B))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp_assoc, mateEquiv_counit]
  rw [F₂.map_comp, Category.assoc]
  have hη := η.hom.naturality (adj₁.counit.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [hη]
  rw [mateEquiv_counit]
  have ha := a.naturality (A₁.right.hom.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ha
  rw [reassoc_of% ha]
  rw [← reassoc_of% (compatible (R₁.obj B))]
  rw [← h.map_comp, A₁.counit]
  rw [← h.map_comp, Iso.hom_inv_id_app_assoc]

end CategoricalEvaluation
end WeilConjectures.SemilinearSections

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.ConstantTowerDirectImageNormalization
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedSitePerfectProjectionFormula
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Direct-image reduction and the completion unit

Source: Stacks Project, proetale.tex, Tag 099N (3), (4), and sites-cohomology.tex,
Tags 0B56, 0944 and 0A07; strict-diagram refinement of fix-lem-exchanges, Step 5
(blueprint: lem-sf-cbc-direct-image-reduction-unit).

All reductions, augmentations, projection mates and limit comparisons are the
specified constructions of ConstantTowerDirectImageNormalization. The index n
means exponent n+1. Derived towers are localized strict diagrams.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction
open ConstantNormalization

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A)

/-- Completion is the total limit of the canonical strict quotient reduction.
Source: Stacks 099M, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def completion (T : Scheme.{u}) :
    DerivedCategory (Modules A T) ⥤ DerivedCategory (Modules A T) :=
  reduction I T ⋙ L A T

/-- The completion unit is the limit of tensoring with the quotient augmentation,
using the specified inverse of the constant-tower limit identification.
Source: Stacks 099M, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def unit (T : Scheme.{u}) : 𝟭 (DerivedCategory (Modules A T)) ⟶ completion I T :=
  (deltaLimit A T).inv ≫ Functor.whiskerRight (augmentation I T) (L A T)

/-- The natural transformation rho is L(h) followed by the inverse of the
underived-composite normalized direct-image/limit comparison, without evaluation.
Source: Stacks 0A07, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def comparison {U V : Scheme.{u}} (f : U ⟶ V) :
    push A f ⋙ completion I V ⟶ completion I U ⋙ push A f :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (projection I f) (L A V) ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (reduction I U) (limitPush A f).inv ≫
          (Functor.associator _ _ _).inv

/-- The canonical finite-quotient tensor/pullback comparison. Evaluating the
K-flat-normalized whole-tower tensor comparison gives scalar-extension balancing
with the constant sheaf A/I^(n+1). This defines its actual map, not an arbitrary iso.
Source: Stacks 07A4, 0B56
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def finiteTensorPull {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    (reduction I V ⋙ ev A V n) ⋙ pull A f ≅
      pull A f ⋙ (reduction I U ⋙ ev A U n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reduction I V) (evalG A f n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (reductionPull I f) (ev A U n) ≪≫
          Functor.associator _ _ _

/-- The finite-P_n projection morphism is the adjunction mate of tensor balancing,
hence the adjunct of pullback-tensor comparison followed by counit tensor identity.
Its source and target use the canonical evaluation models of derived tensor.
Source: Stacks 0B56, 0944
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def finiteProjection {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    push A f ⋙ (reduction I V ⋙ ev A V n) ⟶
      (reduction I U ⋙ ev A U n) ⋙ push A f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
      (constantRingIso A f))
    (proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
      (constantRingIso A f)) (finiteTensorPull I f n).hom

/-- Strict direct-image reduction, naturality and completion-unit normalization.
Source: Stacks 099N (3), (4), 0A07, 0B56 and 0944; agent refinement of
fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-direct-image-reduction-unit).

Proof:
1. Naturality of the diagram-site projection mate and the constant comparison chi
makes h natural. Clause (4) of constantTowerDirectImageNormalization gives the
strict augmentation square h i = Q(i) chi for arbitrary F.
2. Naturality of limitPush on i, clause (3) of the same normalization theorem,
and the definition of unit give L(h) eta = b P(eta). Composing with b inverse
gives comparison eta = P(eta), before any evaluation of tower morphisms.
3. Naturality of h and b gives naturality of comparison, with the stated formula.
4. For each positive exponent independently, quotientPerfect gives a bounded
finite-projective A-complex representing P_n. The exact constant-module functor
and its finite-power identifications carry the finite-free splitting identities
to sheaves (lem-sfb-constant-finite-free-presentation-extension). The perfect
projection formula (lem-sbc-ringed-site-perfect-projection-formula) therefore
makes finiteProjection invertible. The augmented diagram projection mate
(lem-weil-pbc-augmented-diagram-projection-mate) identifies evaluation of h with
this precise counit-tensor mate, under evalR.
5. Tower kernels, cokernels and cohomology are levelwise
(lem-weil-tower-category-levelwise-abelian). Evaluation thus detects whether each
cohomology map of h is invertible. The unbounded cohomology criterion
(lem-weil-pbc-unbounded-derived-iso-cohomology) makes h invertible for complete K.
Specialize Step 2 to K to obtain the final equation. Naturality is Step 1 restricted
to complete objects. No uniform bound on the representatives is used. -/
theorem directImageReductionUnit (d : CompleteCoefficientDatum A)
    (_hfinite : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1)))
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (∀ F : DerivedCategory (Modules A U),
      (unit d.ideal V).app ((push A f).obj F) ≫ (comparison d.ideal f).app F =
        (push A f).map ((unit d.ideal U).app F)) ∧
    (∀ (F F' : DerivedCategory (Modules A U)) (t : F ⟶ F'),
      (completion d.ideal V).map ((push A f).map t) ≫ (comparison d.ideal f).app F' =
        (comparison d.ideal f).app F ≫ (push A f).map ((completion d.ideal U).map t)) ∧
    (∀ (F F' : DerivedCategory (Modules A U)) (t : F ⟶ F'),
      (reduction d.ideal V).map ((push A f).map t) ≫ (projection d.ideal f).app F' =
        (projection d.ideal f).app F ≫ (R A f).map ((reduction d.ideal U).map t)) ∧
    (∀ K : DerivedCategory (Modules A U), IsIso ((unit d.ideal U).app K) →
      IsIso ((projection d.ideal f).app K) ∧
      (∀ n : ℕ,
        (ev A V n).map ((projection d.ideal f).app K) ≫
            (evalR A f n).app ((reduction d.ideal U).obj K) =
          (finiteProjection d.ideal f n).app K) ∧
      (∀ n : ℕ, IsIso ((finiteProjection d.ideal f n).app K)) ∧
      (unit d.ideal V).app ((push A f).obj K) ≫
          (L A V).map ((projection d.ideal f).app K) =
        (push A f).map ((unit d.ideal U).app K) ≫
          (limitPush A f).hom.app ((reduction d.ideal U).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction

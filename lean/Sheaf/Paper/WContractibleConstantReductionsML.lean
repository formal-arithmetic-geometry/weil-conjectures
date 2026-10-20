/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.FiniteTripleMittagLeffler
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Mathlib.CategoryTheory.CofilteredSystem
public import Sheaf.Paper.ConstantReductionsFiniteProjectiveModel

import Sheaf.Algebra.Homology.AdicShortComplexCohomologyML
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Constant reductions on a weakly contractible affine

Source: Stacks Project, Tag 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml).

## Main definitions

- `mlConstantDerivedObject`: constant realization of an algebraic derived object.
- `mlHypercohomologyTower`: the canonical quotient tower, with cohomology and sections.

## Main statements

- `wcontractible_constant_reductions_mittagLeffler`: image stabilization in every degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Constant module realization uses the existing sheafification construction.
Source: Stacks Tags 093J and 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
abbrev mlConstant (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] :=
  constantModuleHomFunctor (coefficientProEtaleModelTopology.{u, v} W) A

/-- The constant presheaf functor preserves zero morphisms sectionwise.
Source: Stacks Tag 093J (blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
instance mlConstantPresheafPreservesZero {D : Type w} [SmallCategory D]
    (A : Type w) [CommRing A] :
    (siteConstantModulePresheafGeneral (C := D) A).PreservesZeroMorphisms where
  map_zero := by intros; ext U x; rfl

/-- Constant module sheafification preserves zero morphisms.
Source: Stacks Tag 093J (blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
instance mlConstantPreservesZero {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) (A : Type w) [CommRing A] :
    (constantModuleHomFunctor T A).PreservesZeroMorphisms := by
  unfold constantModuleHomFunctor siteConstantModuleFunctorGeneral
  infer_instance

/-- Realize an algebraic complex as a constant complex on the equivalent small site.
Source: Stacks Tag 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
def mlConstantComplex (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :=
  ((mlConstant W A).mapHomologicalComplex (.up ℤ)).obj P

/-- The algebraic derived category uses the standard localization.
Source: Stacks Tag 05RU (blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
abbrev MLAlgebraDerived (A : Type w) [CommRing A] :=
  @DerivedCategory (ModuleCat.{w} A) _ _ (HasDerivedCategory.standard _)

/-- Perfectness in the standard algebraic derived category.
Source: Stacks Tags 07LU and 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
abbrev MLAlgebraPerfect {A : Type w} [CommRing A] (E : MLAlgebraDerived A) : Prop :=
  @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) E

/-- Realization of an algebraic derived object by its complex representative. Exact
constant module sheafification makes its isomorphism class independent of this choice.
Source: Stacks Tags 093J and 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
def mlConstantDerivedObject (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (E : MLAlgebraDerived A) :
    ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A) :=
  constantReductionsRealization (coefficientProEtaleModelTopology.{u, v} W) A E

/-- Degree-q cohomology of strict module-sheaf towers in the standard localization.
Source: Stacks Tags 05RU and 0940
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
abbrev mlTowerCohomology {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.TD R ⥤ (ℕᵒᵖ ⥤ ConstantCompletion.Mod R) :=
  constantReductionsTowerCohomology R q

/-- The actual strict derived quotient tower, followed by degree-q cohomology and
sections over the final object. For weakly contractible W, sections are exact, so
these are precisely the hypercohomology groups, with their actual transition maps.
Index n represents exponent n+1. The final forgetful functor retains the same images.
Source: Stacks Tags 09C5 and 0946
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
def mlHypercohomologyTower (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (J : Ideal A)
    (H : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A))
    (q : ℤ) : ℕᵒᵖ ⥤ Type (max v (u + 1)) :=
  (mlTowerCohomology
    (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A) q).obj
      ((ConstantCompletion.quotientPresentation (coefficientProEtaleModelTopology.{u, v} W) A J
        false).tower.obj H) ⋙
    SheafOfModules.evaluation _ (op (AsSmall.up.obj (⊤_ W.ProEt))) ⋙
      CategoryTheory.forget (ModuleCat _)

/-- The derived constant quotient tower admits finite comparisons with an algebraic
Mittag--Leffler tower. The comparison may depend on the finite triple of indices.
Source: Stacks Project, Tag 09C5.

Proof: choose local algebraic markings, normalize finite chains of quotient maps, and
apply complete perfect inverse-limit reconstruction. Artin--Rees gives stabilization of
the bounded finite-projective quotient complex. Reducing one level-t marking to levels m
and n gives the two comparison equations by tensor reassociation, so no compatible
infinite family of markings is required.
(blueprint: lem-sfb-wcontractible-constant-reductions-finite-comparison). -/
theorem wcontractible_constant_reductions_finite_comparison
    (W : Scheme.{u}) [IsAffine W]
    (_hW : ∀ (F G : Sheaf (ProEt.topology W) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (⊤_ W.ProEt))))
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (H : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A))
    (_hcomplete : ConstantCompletion.IsComplete
      (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J 0) H)
    (_hconstant : ∀ n : ℕ, ∃ E : MLAlgebraDerived (A ⧸ J ^ (n + 1)),
      (n = 0 → MLAlgebraPerfect E) ∧
      Nonempty
        ((ConstantCompletion.extend
            (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J n)).obj H ≅
          mlConstantDerivedObject W (A ⧸ J ^ (n + 1)) E)) (q : ℤ) :
    ∃ U : ℕᵒᵖ ⥤ Type (max v (u + 1)),
      U.IsMittagLeffler ∧
      CategoryTheory.Functor.FiniteTripleRangeComparison
        (mlHypercohomologyTower W A J H q) U := by
  obtain ⟨P, _, _, _, _, hfinite, hcomparison⟩ :=
    constant_reductions_finite_projective_model W _hW A J H _hcomplete _hconstant
  let B := AdicCompletion J A
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing J
  let F := AdicCohomology.sections (R := B)
    (coefficientProEtaleModelTopology.{u, v} W) (AsSmall.up.obj (⊤_ W.ProEt))
  have : F.PreservesHomology := AdicCohomology.sections_preservesHomology _ _
  have : Module.Finite B (P.sc q).X₃ := (hfinite _).2
  refine ⟨_, ?_, hcomparison q⟩
  exact AdicCohomology.map_isMittagLeffler _ F
    (AdicCohomology.isMittagLeffler (J.map (algebraMap A B)) (P.sc q))

/-- The hypercohomology groups of individually constant derived quotient reductions
satisfy Mittag--Leffler in every integer degree. The constant markings have no
compatibility requirement, and the quotient rings need not have finite underlying sets.
The coefficient-sized small model is equivalent to the original small pro-etale site;
the coefficient ring may lie in any universe max v (u + 1) containing its objects.

Source: Stacks Project, proetale.tex, Tag 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml).

Proof: apply `wcontractible_constant_reductions_finite_comparison` in degree q. Its
finite-projective model has stabilized quotient-cohomology images by the Artin--Rees
calculation, and exact constant-module sections preserve them. The finite-triple
transfer theorem then transports the two images using the same level-n bijection.
The comparison may vary with the triple, so no infinite compatible markings are needed. -/
theorem wcontractible_constant_reductions_mittagLeffler
    (W : Scheme.{u}) [IsAffine W]
    (_hW : ∀ (F G : Sheaf (ProEt.topology W) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (⊤_ W.ProEt))))
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (H : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A))
    (_hcomplete : ConstantCompletion.IsComplete
      (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J 0) H)
    (_hconstant : ∀ n : ℕ, ∃ E : MLAlgebraDerived (A ⧸ J ^ (n + 1)),
      (n = 0 → MLAlgebraPerfect E) ∧
      Nonempty
        ((ConstantCompletion.extend
            (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} W) A J n)).obj H ≅
          mlConstantDerivedObject W (A ⧸ J ^ (n + 1)) E)) :
    ∀ q : ℤ, (mlHypercohomologyTower W A J H q).IsMittagLeffler := by
  intro q
  obtain ⟨U, hU, hcomparison⟩ :=
    wcontractible_constant_reductions_finite_comparison W _hW A J H _hcomplete _hconstant q
  exact CategoryTheory.Functor.isMittagLeffler_of_finiteTripleRangeComparison hcomparison hU

end AlgebraicGeometry.Scheme

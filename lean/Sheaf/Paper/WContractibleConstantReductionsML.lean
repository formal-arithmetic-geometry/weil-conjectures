/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.AdicQuotientCohomologyML
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
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.AdicQuotientCohomologyML
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.RingTheory.NilpotentProjectiveComplexLift
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.RingTheory.RlimPerfectComplete
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Filtration
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero
import Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism
import Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal
import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

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
  (ConstantCompletion.Q _).obj (mlConstantComplex W A
    ((@DerivedCategory.Q (ModuleCat.{max v (u + 1)} A) _ _
      (HasDerivedCategory.standard _)).objPreimage E))

/-- Degree-q cohomology of strict module-sheaf towers in the standard localization.
Source: Stacks Tags 05RU and 0940
(blueprint: lem-sfb-wcontractible-constant-reductions-ml). -/
abbrev mlTowerCohomology {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.TD R ⥤ (ℕᵒᵖ ⥤ ConstantCompletion.Mod R) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

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
      CategoryTheory.Functor.FiniteTripleComparison
        (mlHypercohomologyTower W A J H q) U := by
  sorry

/-- The hypercohomology groups of individually constant derived quotient reductions
satisfy Mittag--Leffler in every integer degree. The constant markings have no
compatibility requirement, and the quotient rings need not have finite underlying sets.
The coefficient-sized small model is equivalent to the original small pro-etale site;
the coefficient ring may lie in any universe max v (u + 1) containing its objects.

Source: Stacks Project, proetale.tex, Tag 09C5
(blueprint: lem-sfb-wcontractible-constant-reductions-ml).

Proof plan:
1. The empty scheme has zero module sections, so the conclusion is immediate there.
   On a nonempty object constant sheafification detects a zero module: equality of
   constant sections holds on a cover, which has a nonempty member. Exact constant
   realization therefore reflects algebraic derived isomorphisms. K-flat resolutions
   compute successive reductions by (x tensor s) tensor t mapped to x tensor st,
   compatibly with every quotient unit.
2. For each E_n, reduce to A/J. Apply local algebraicity (09BE) to the inverse of
   its constant identification with perfect E_1. On one nonempty covering member this
   gives an algebraic isomorphism. Lift its bounded finite-projective model across
   the nilpotent ideal J/J^n using 09AR. Nilpotent Nakayama makes the lifted terms
   finite and zero outside the original finite range, proving E_n perfect.
3. Local algebraicity now supplies algebraic consecutive transition maps. Their
   reductions are isomorphisms by the detection in step 1. Choose one at each level;
   their composites form a normalized algebraic tower, without asserting equality
   with the original global sheaf transitions.
4. Complete A at J. By 05GG and 0316 the completion B is Noetherian and its quotients
   by (JB)^n are A/J^n, compatibly. Apply 09AW to reconstruct a bounded finite-projective
   B-complex P with these reductions. Bounded flatness computes every derived reduction.
5. Apply Artin--Rees to im(d^q) inside the finite module P^(q+1), obtaining c. If
   t >= n+c and dz lies in I^t, write dz=dy with y in I^(t-c)P^q. Then z-y is a true
   cycle with the same class modulo I^n. Thus images in H^q(P/I^n) stabilize at n+c.
6. Exact evaluation at weakly contractible W computes derived sections. Exactness of
   evaluated constant modules preserves the stabilized images of step 5, yielding
   stabilization for the constant model tower in every q.
7. For each triple t >= m >= n reduce a single level-t isomorphism to m and n.
   The tensor reassociation of step 1 identifies both quotient arrows, including
   repeated indices, with the constant-model arrows. The same level-n isomorphism
   transports both images, so equality holds without compatible infinite markings.

Dependencies by proof step (the node records their precise uses):
1. def-weil-pbc-proetale-site, def-weil-pbc-constant-sheaf,
   lem-weil-pbc-constant-module-section-properties,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pc-kflat-resolution,
   lem-pur-kflat-change-of-rings, lem-pur-derived-change-of-rings,
   lem-pc-sites-module-sheafification-interface, lem-pc-sites-sheafification-underlying-sets,
   lem-weil-pbc-site-sheafification-sections-local.
2. lem-sfb-perfect-constant-derived-map-local, lem-pur-derived-change-of-rings,
   lem-weil-pbc-nilpotent-projective-complex-lift, def-pc-perfect-ring-complex.
3. lem-sfb-perfect-constant-derived-map-local, lem-pur-derived-change-of-rings.
4. lem-weil-pbc-adic-completion-mod-ideal, lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-rlim-perfect-complete, def-pc-perfect-ring-complex, lem-pc-kflat-closure,
   lem-pur-derived-change-of-rings.
5. lem-weil-pbc-artin-rees.
6. lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits,
   lem-weil-pbc-constant-module-section-properties.
7. lem-pur-derived-change-of-rings. -/
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
  exact CategoryTheory.Functor.isMittagLeffler_of_finiteTripleComparison hcomparison hU

end AlgebraicGeometry.Scheme

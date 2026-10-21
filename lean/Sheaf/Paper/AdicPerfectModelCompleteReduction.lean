/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.TorsionLimitSheafCompleteness
import Sheaf.Paper.RestrictionLocalCompleteness
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

/-!
# Completeness and residue reduction of completed perfect models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication;
Stacks Tags 093J, 093M, 099Q, 06YQ and 0E8K
(blueprint: lem-sfb-adic-perfect-model-complete-reduction).

We use the equivalent coefficient-sized small model of the pro-etale site. The ring
and the module universe are independent of the scheme universe. Positive exponents
are indexed by n : ℕ, meaning n+1. In particular the residue field is A/I^(0+1).
All helpers below only name the actual complexes and maps in the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.AdicPerfectModel

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {A : Type w} [CommRing A] (I : Ideal A)

/-- The actual termwise constant complex, using the recorded exact realization.
Source: Stacks 093J (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
abbrev constantComplex (R : Type w) [CommRing R] :=
  (commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)

/-- The complex B tensor_A P, before localization.
Source: Bhatt--Scholze 6.6.11 (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
abbrev model (P : CochainComplex (ModuleCat.{w} A) ℤ) :=
  ((ConstantCompletion.change (ConstantCompletion.coefficientMap J A I)).mapHomologicalComplex
    (.up ℤ)).obj ((constantComplex J A).obj P)

/-- The ordinary algebraic residue complex k tensor_A P, with its k-action retained.
Source: Stacks 093M (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def algebraicResidue (P : CochainComplex (ModuleCat.{w} A) ℤ) :
    CochainComplex (ModuleCat.{w} (A ⧸ I ^ (0 + 1))) ℤ :=
  letI := (ModuleCat.extendRestrictScalarsAdj
    (Ideal.Quotient.mk (I ^ (0 + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex
    (.up ℤ)).obj P

/-- The constant sheaf of the ordinary residue complex.
Source: Stacks 093J (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
abbrev constantResidue (P : CochainComplex (ModuleCat.{w} A) ℤ) :=
  (constantComplex J (A ⧸ I ^ (0 + 1))).obj (algebraicResidue I P)

variable {J}

/-- Restrict actual complexes and chain maps to the localized site.
Source: Stacks 03DJ (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def overComplex (R : Sheaf J CommRingCat.{w}) (U : C) :
    ConstantCompletion.Cx R ⥤ ConstantCompletion.Cx (R.over U) :=
  letI := ringedOverFunctor_additive R U
  (SheafOfModules.overFunctor (siteModuleRings R) U).mapHomologicalComplex
    (.up ℤ)

/-- Cohomology in the standard derived localization used throughout the coefficient API.
Source: Stacks 05RU (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
abbrev cohomology (R : Sheaf J CommRingCat.{w}) (q : ℤ) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard (ConstantCompletion.Mod R)) q

variable (J)

/-- Constant module sections, through the actual additive sheafification unit.
Source: Stacks 093J (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def constantSection (R : Type w) [CommRing R] (N : ModuleCat.{w} R) (U : Cᵒᵖ) (x : N) :
    ((commutativeSiteConstantModuleFunctor J R).obj N).val.obj U :=
  (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj N).presheaf).app U x

/-- The normalization fixing the canonical residue comparison on local tensor generators.
The image of (c tensor (b tensor p)) is c times bar(b) times the constant section 1 tensor p.
Source: Stacks 093M (blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def IsResidueComparison (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (f : ((ConstantCompletion.change (ConstantCompletion.projection J A I 0)).mapHomologicalComplex
      (.up ℤ)).obj (model J I P) ⟶ constantResidue J I P) : Prop :=
  ∀ (q : ℤ) (U : Cᵒᵖ) (b : (ConstantCompletion.completed J A I).obj.obj U)
    (c : (ConstantCompletion.finite J A I 0).obj.obj U) (p : P.X q),
    (f.f q).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.projection J A I 0) _ U c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _ U b
          (constantSection J A (P.X q) U p))) =
      (c * (ConstantCompletion.projection J A I 0).hom.app U b) •
        constantSection J (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).X q) U
          ((1 : A ⧸ I ^ (0 + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (0 + 1))] p)

/-- The same canonical tensor formula on a slice, with the restricted coefficient sheaf.
Source: Stacks 03DJ, 093M and 0E8K
(blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def IsSliceResidueComparison (P : CochainComplex (ModuleCat.{w} A) ℤ) (U : C)
    (f : ((ConstantCompletion.change
      ((J.overPullback CommRingCat U).map
        (ConstantCompletion.projection J A I 0))).mapHomologicalComplex
         (.up ℤ)).obj
          ((overComplex (ConstantCompletion.completed J A I) U).obj (model J I P)) ⟶
        (overComplex (ConstantCompletion.finite J A I 0) U).obj (constantResidue J I P)) :
    Prop :=
  ∀ (q : ℤ) (W : (Over U)ᵒᵖ)
    (b : (ConstantCompletion.completed J A I).obj.obj (op W.unop.left))
    (c : (ConstantCompletion.finite J A I 0).obj.obj (op W.unop.left)) (p : P.X q),
    (f.f q).val.app W
      (ConstantCompletion.tensorSection
        ((J.overPullback CommRingCat U).map (ConstantCompletion.projection J A I 0)) _ W c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _
          (op W.unop.left) b (constantSection J A (P.X q) (op W.unop.left) p))) =
      (c * (ConstantCompletion.projection J A I 0).hom.app (op W.unop.left) b) •
        constantSection J (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).X q) (op W.unop.left)
          ((1 : A ⧸ I ^ (0 + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (0 + 1))] p)

variable {J}

/-- The complete assertion on a site or a slice, retaining the canonical chain comparison.
This uses the existing local internal-Hom completeness predicate and universal derived counit.
Source: Bhatt--Scholze 6.6.11; Stacks 093J, 093M, 099Q and 06YY
(blueprint: lem-sfb-adic-perfect-model-complete-reduction). -/
def HasCompleteResidueCalculation
    {B k : Sheaf J CommRingCat.{w}} (π : B ⟶ k)
    (M : ConstantCompletion.Cx B) (V : ConstantCompletion.Cx k)
    (H : ℤ → ConstantCompletion.Mod k) (a b : ℤ)
    (c : ((ConstantCompletion.change π).mapHomologicalComplex (.up ℤ)).obj M ≅ V) : Prop :=
  ConstantCompletion.IsComplete π ((ConstantCompletion.Q B).obj M) ∧
    IsIso ((ConstantCompletion.extendComparison π).app M ≫
      (ConstantCompletion.Q k).map c.hom) ∧
    (∀ q : ℤ, Nonempty
      ((cohomology k q).obj ((ConstantCompletion.extend π).obj ((ConstantCompletion.Q B).obj M)) ≅
        H q)) ∧
    ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((cohomology B q).obj ((ConstantCompletion.Q B).obj M)) ∧
      IsZero ((cohomology k q).obj
        ((ConstantCompletion.extend π).obj ((ConstantCompletion.Q B).obj M)))

end AlgebraicGeometry.Scheme.AdicPerfectModel

namespace AlgebraicGeometry.Scheme

open AdicPerfectModel

/-- Completed bounded finite-projective models are locally derived complete and their
canonical derived residue comparison is an isomorphism, on the site and every slice.
Source: Bhatt--Scholze 6.6.11, reverse implication; Stacks 093J, 093M, 099Q, 06YQ, 0E8K
(blueprint: lem-sfb-adic-perfect-model-complete-reduction).

Proof, following the seven DAG steps:
1. Split each finite-projective P^i off a finite free module. Constant sheaves preserve
   the splitting, so B tensor P^i is the image of the same idempotent on B^r. Sectionwise
   limits identify this with lim_n of the constant sheaves P^i/I^n P^i, including rank zero.
2. Noetherianity makes I finitely generated. Torsion-limit completeness applies to these
   inverse limits and their bounded complex. Restriction of scalars preserves and reflects
   local derived completeness for the extended ideal, giving completeness over B.
3. The constant-completion quotient theorem identifies B/IB with the constant residue field,
   through the first projection. It assumes no finite underlying residue set or regularity.
4. Each term is a retract of a finite free B-module, hence flat. Bounded-above flat complexes
   are K-flat, so the universal derived-change-of-rings counit computes reduction ordinarily.
5. The displayed tensor-generator formula is balanced, natural in the differential, and
   invertible on finite free modules and their retracts. It gives the canonical chain
   isomorphism; its composite with the universal counit is the asserted derived isomorphism.
6. Exactness of constant realization identifies cycles, boundaries and cohomology. The
   algebraic residue terms are finite-dimensional vector spaces, hence so is their
   cohomology. Both complexes have zero terms, hence zero cohomology, outside [a,b].
7. Localization identifies the slice with the pro-etale site of the covering object.
   Restriction is exact, commutes with tensor and preserves K-flat complexes and limits.
   Restrict the same chain comparison and apply the preceding argument on the slice.
   This works for every object, so in particular every covering slice, and for a>b.

The kernel of the first projection is IB by the Noetherian constant-completion quotient
identification. Thus HasCompleteResidueCalculation uses exactly local derived IB-completeness.
No completeness or localness assumption on A, or perfectness of its quotients, is used. -/
theorem adicPerfectModel_complete_reduction
    (T : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.IsMaximal)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (a b : ℤ)
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (_hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) :
    ∃ c : ((ConstantCompletion.change
        (ConstantCompletion.projection
          (coefficientProEtaleModelTopology.{u, v} T) A I 0)).mapHomologicalComplex
          (.up ℤ)).obj
            (model (coefficientProEtaleModelTopology.{u, v} T) I P) ≅
              constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P,
      IsResidueComparison (coefficientProEtaleModelTopology.{u, v} T) I P c.hom ∧
      (∀ q : ℤ, Module.Finite (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).homology q)) ∧
      HasCompleteResidueCalculation
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0)
        (model (coefficientProEtaleModelTopology.{u, v} T) I P)
        (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P)
        (fun q ↦ (commutativeSiteConstantModuleFunctor
          (coefficientProEtaleModelTopology.{u, v} T) (A ⧸ I ^ (0 + 1))).obj
            ((algebraicResidue I P).homology q)) a b c ∧
      ∀ U : coefficientProEtaleSiteModel.{u, v} T,
        ∃ d : ((ConstantCompletion.change
            (((coefficientProEtaleModelTopology.{u, v} T).overPullback CommRingCat U).map
              (ConstantCompletion.projection
                (coefficientProEtaleModelTopology.{u, v} T) A I 0))).mapHomologicalComplex
                  (.up ℤ)).obj
          ((overComplex (ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} T) A I) U).obj
              (model (coefficientProEtaleModelTopology.{u, v} T) I P)) ≅
          (overComplex (ConstantCompletion.finite
            (coefficientProEtaleModelTopology.{u, v} T) A I 0) U).obj
              (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P),
        IsSliceResidueComparison (coefficientProEtaleModelTopology.{u, v} T) I P U d.hom ∧
        HasCompleteResidueCalculation
          (((coefficientProEtaleModelTopology.{u, v} T).overPullback CommRingCat U).map
            (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0))
          ((overComplex (ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} T) A I) U).obj
              (model (coefficientProEtaleModelTopology.{u, v} T) I P))
          ((overComplex (ConstantCompletion.finite
            (coefficientProEtaleModelTopology.{u, v} T) A I 0) U).obj
              (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P))
          (fun q ↦ (SheafOfModules.overFunctor
            (siteModuleRings (ConstantCompletion.finite
              (coefficientProEtaleModelTopology.{u, v} T) A I 0)) U).obj
                ((commutativeSiteConstantModuleFunctor
                  (coefficientProEtaleModelTopology.{u, v} T) (A ⧸ I ^ (0 + 1))).obj
                    ((algebraicResidue I P).homology q))) a b d := by
  sorry

end AlgebraicGeometry.Scheme

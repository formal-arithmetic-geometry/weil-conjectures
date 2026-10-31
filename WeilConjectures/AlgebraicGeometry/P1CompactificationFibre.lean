/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction

/-!
# Excision in the projective-line compactification

Source: blueprint, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; Stacks Tags 09XP and 03F3 (blueprint: lem-pur-p1-compactification-fibre).
The map is fixed by restriction on supported sections, not by an arbitrary isomorphism.
The chart used here is `[1:t]`, so its origin is the section named `infinity` by
ProjectiveLine's other chart convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Etale.P1CompactificationFibre

variable (S : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

/-- The affine chart `[1:t]`. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev j := ProjectiveLine.infinityChart S

/-- The affine origin. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev z := AffineSpace.zeroSection PUnit.{u + 1} S

/-- The closed image `[1:0]` of the origin. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev zbar := ProjectiveLine.infinity S

/-- The origin remains closed in the compactification. Source: blueprint Step 2.
Proof: it is a section of the separated projective-line structure map, hence a closed
immersion. Its factorization through `[1:t]` is the definition of `infinity`.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem zbar_isClosedImmersion : IsClosedImmersion (zbar S) := by
  apply IsClosedImmersion.of_section_of_isSeparated (ProjectiveLine S ↘ S) (zbar S)
  exact ProjectiveLine.infinity_over (S := S)

attribute [instance] zbar_isClosedImmersion

/-- The specified proper compactification of the affine line.
Source: blueprint Step 2 (blueprint: lem-pur-p1-compactification-fibre). -/
def compactification : Compactification (𝔸(PUnit.{u + 1}; S) ↘ S) where
  Z := ProjectiveLine S
  g := ProjectiveLine S ↘ S
  i := j S
  comm := (ProjectiveLine.infinityChart_over (S := S)).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The coefficient category. Source: Stacks 09XP, module-valued supported sections
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev C := ModuleCat.{u + 1} A

/-- The uniquely characterized restriction isomorphism on sections with support.
Source: Stacks 09XP and 03F3; blueprint Step 2.
Proof: the complement W of `[1:0]` and the chart X cover P, with intersection X minus
its origin. Restrict a supported section to X. Conversely glue a section on X vanishing
on X minus the origin with zero on W. The sheaf axiom gives a unique glued section.
These constructions are inverse, natural and A-linear. The kernel inclusion is monic,
so the displayed compatibility uniquely determines the natural isomorphism.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem existsUnique_supportedRestriction :
    ∃! r : globalSectionsWithSupport (C A) (zbar S) ≅
        openImmersionRestriction (C A) (j S) ⋙ globalSectionsWithSupport (C A) (z S),
      ∀ G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A),
        r.hom.app G ≫
            (Sheaf.ΓSupportι _ (C A) (op (Scheme.Etale.mk (z S).openComplement.ι))).app
              ((openImmersionRestriction (C A) (j S)).obj G) =
          (Sheaf.ΓSupportι _ (C A)
              (op (Scheme.Etale.mk (zbar S).openComplement.ι))).app G ≫
            globalSectionsUpperStarMap (C A) (j S) G ≫
            (Sheaf.Γ _ (C A)).map
              ((upperStarIsoOpenImmersionRestriction (C A) (j S)).hom.app G) := by
  sorry

/-- Restriction on supported sections, selected by its unique kernel-inclusion equation.
Source: Stacks 09XP and 03F3 (blueprint: lem-pur-p1-compactification-fibre). -/
def supportedRestriction := (existsUnique_supportedRestriction S A).exists.choose

/-- Restriction is a left adjoint as well as a right adjoint.
Source: Stacks 03F3; the open adjoint triple
(blueprint: lem-pur-p1-compactification-fibre). -/
instance restriction_isLeftAdjoint :
    (openImmersionRestriction (C A) (j S)).IsLeftAdjoint :=
  (openImmersionRestrictionLowerStarAdjunction (C A) (j S)).isLeftAdjoint

/-- Derived restriction, with the open unit identifying the restriction of `j_! F` with F.
Source: Stacks 03F3, injective computation (blueprint: lem-pur-p1-compactification-fibre). -/
def derivedRestriction (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    (rightDerivedSectionsWithSupport (C A) (zbar S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek (C A) (j S)).obj F)) ⟶
      (rightDerivedSectionsWithSupport (C A) (z S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) :=
  (Functor.rightDerivedPullback (openImmersionRestriction (C A) (j S))
      (supportedRestriction S A).hom).app _ ≫
    (rightDerivedSectionsWithSupport (C A) (z S)).map
      (((openImmersionRestriction (C A) (j S)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          (asIso ((openImmersionLowerShriekAdjunction (C A) (j S)).unit.app F)).inv)

/-- Excision: derived restriction is invertible.
Source: Stacks 03F3 and 09XP; blueprint Step 2.
Proof: resolve `j_! F` by a bounded-below injective complex I. Restriction is exact and
preserves injectives, because its left adjoint extension by zero is exact. The open unit
identifies the restriction of `j_! F` with F. The unique supported-section isomorphism
above applied termwise to I is an isomorphism of complexes. It computes the displayed
right-derived comparison. Thus the comparison is invertible, independently of the
resolution by uniqueness of right derived functors.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem derivedRestriction_isIso
    (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    IsIso (derivedRestriction S A F) := by
  have : (openImmersionRestriction (C A) (j S)).PreservesKInjectiveComplexes :=
    (openImmersionLowerShriekAdjunction (C A) (j S)).preservesKInjectiveComplexes
  have := Functor.isIso_rightDerivedPullback_app
    (openImmersionRestriction (C A) (j S)) (supportedRestriction S A).hom
    ((DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek (C A) (j S)).obj F))
  unfold derivedRestriction
  infer_instance

/-- Canonical excision, in the direction from affine support to projective support.
Source: blueprint Step 2 (blueprint: lem-pur-p1-compactification-fibre). -/
def excision (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :=
  letI := derivedRestriction_isIso S A F
  (asIso (derivedRestriction S A F)).symm

/-- Forget support on the projective line, derived from the actual kernel inclusion.
Source: Stacks 09XP (blueprint: lem-pur-p1-compactification-fibre). -/
def forgetSupport : rightDerivedSectionsWithSupport (C A) (zbar S) ⟶
    (Sheaf.Γ (ProjectiveLine S).smallEtaleTopology (C A)).rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatTrans
    (Sheaf.ΓSupportι _ (C A) (op (Scheme.Etale.mk (zbar S).openComplement.ι)))

/-- The identification of derived global sections with the derived proper direct image,
after global sections at the base. For an algebraically closed field base, these latter
global sections are the equivalence from module sheaves on the point to modules.
Source: blueprint Step 2; Stacks 09XP
(blueprint: lem-pur-p1-compactification-fibre). -/
def properDirectImageComparison :
    (lowerStar (C A) (ProjectiveLine S ↘ S)).rightDerivedFunctor ⋙
        rightDerivedGlobalSections (C A) S ≅
      rightDerivedGlobalSections (C A) (ProjectiveLine S) :=
  rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (C A) (ProjectiveLine S ↘ S)

/-- The global-sections target is the compactly supported direct image for the
specified compactification, followed by global sections on the base.
Source: blueprint Step 2, definition of compact support
(blueprint: lem-pur-p1-compactification-fibre). -/
def compactSupportComparison
    (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    (rightDerivedGlobalSections (C A) (ProjectiveLine S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek (C A) (j S)).obj F)) ≅
      (rightDerivedGlobalSections (C A) S).obj
        ((rightDerivedLowerShriekOfCompactification (C A) (compactification S)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  (properDirectImageComparison S A).symm.app _ ≪≫
    (rightDerivedGlobalSections (C A) S).mapIso
      ((lowerStar (C A) (ProjectiveLine S ↘ S)).rightDerivedFunctor.mapIso
        (((openImmersionLowerShriek (C A) (j S)).mapDerivedCategorySingleFunctor 0).app F).symm)

/-- The compactification forget-supports morphism on cohomology.
Source: blueprint Step 2. It is excision followed by the kernel inclusion on P.
(blueprint: lem-pur-p1-compactification-fibre). -/
def u (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) (m : ℤ) :=
  (DerivedCategory.homologyFunctor (C A) m).map
    ((excision S A F).hom ≫ (forgetSupport S A).app _)

/-- The finite coefficient ring is killed by the exponent of the roots-of-unity sheaf.
Source: blueprint Step 2, finite coefficient setup.
Proof: ell has absolute value less than one in E, hence belongs to its maximal ideal.
The uniformizer generates that ideal, so ell^n lies in its nth power, which is the
quotient ideal. Its image in the quotient is therefore zero.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem coefficient_annihilated (ell : ℕ) [Fact ell.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (π : Padic.coefficientExtensionIntegers ell E)
    (_hπ : Ideal.span ({π} : Set _) = Padic.coefficientExtensionMaximalIdeal ell E)
    (n : ℕ) : ((ell ^ n : ℕ) : Padic.coefficientExtensionIntegers ell E ⧸
      Ideal.span ({π} : Set _) ^ n) = 0 := by
  have hm := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec.2.1
  have hell : (ell : Padic.coefficientExtensionIntegers ell E) ∈
      Padic.coefficientExtensionMaximalIdeal ell E := by
    apply (hm _).mpr
    change spectralNorm ℚ_[ell] E (ell : E) < 1
    rw [← map_natCast (algebraMap ℚ_[ell] E), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hpow := Ideal.pow_mem_pow hell n
  rw [← _hπ] at hpow
  have hzero := (Ideal.Quotient.eq_zero_iff_mem).mpr hpow
  simpa using hzero

/-- The actual finite Tate line on the affine fibre.
Source: blueprint Step 2 and Stacks 03PK
(blueprint: lem-pur-p1-compactification-fibre). -/
def finiteOriginSheaf (Ω : Type u) [Field Ω] (ell : ℕ) [Fact ell.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (π : Padic.coefficientExtensionIntegers ell E)
    (hπ : Ideal.span ({π} : Set _) = Padic.coefficientExtensionMaximalIdeal ell E) (n : ℕ) :=
  Scheme.finiteEtaleTateLine (𝔸(PUnit.{u + 1}; Spec (.of Ω))) (ell ^ n)
    (Padic.coefficientExtensionIntegers ell E ⧸ Ideal.span ({π} : Set _) ^ n)
    (coefficient_annihilated ell E π hπ n)

/-- Excision for the geometric fibre with the stated finite Tate coefficients.
Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md, Step 2;
Stacks 09XP and 03F3.
Proof: use the two-open cover P = X ∪ (P minus the closed origin). Restriction on the
kernels defining supported sections has inverse gluing with zero on the second open.
Resolve j_! F by injectives; exact open restriction preserves injectives and its open
unit identifies the restricted resolution with a resolution of F. Termwise restriction
is an isomorphism, hence so is its derived map. Its inverse is `excision`, and composing
with `forgetSupport` and taking homology is the definition `u`. Projective space is
proper; global sections of q_* agree with those on P. Since Ω is algebraically closed,
module sheaves on Spec Ω identify with modules and this identifies Rq_*j_!F with the
displayed global cohomology target. No invertibility or Chern formula for u is asserted.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem finite_excision (k₀ : Type u) [Field k₀] [Finite k₀]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (AlgebraicClosure k₀) Ω]
    (ell : ℕ) [Fact ell.Prime] (_hchar : (ell : Ω) ≠ 0)
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (π : Padic.coefficientExtensionIntegers ell E)
    (hπ : Ideal.span ({π} : Set _) = Padic.coefficientExtensionMaximalIdeal ell E)
    (n : ℕ) (_hn : 1 ≤ n) :
    Nonempty
      ((rightDerivedSectionsWithSupport
          (C (Padic.coefficientExtensionIntegers ell E ⧸ Ideal.span ({π} : Set _) ^ n))
          (z (Spec (.of Ω)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj (finiteOriginSheaf Ω ell E π hπ n)) ≅
        (rightDerivedSectionsWithSupport
          (C (Padic.coefficientExtensionIntegers ell E ⧸ Ideal.span ({π} : Set _) ^ n))
          (zbar (Spec (.of Ω)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((openImmersionLowerShriek
              (C (Padic.coefficientExtensionIntegers ell E ⧸ Ideal.span ({π} : Set _) ^ n))
              (j (Spec (.of Ω)))).obj (finiteOriginSheaf Ω ell E π hπ n)))) := by
  exact ⟨excision (Spec (.of Ω)) _ (finiteOriginSheaf Ω ell E π hπ n)⟩

end AlgebraicGeometry.Etale.P1CompactificationFibre

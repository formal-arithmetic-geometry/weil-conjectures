/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.Paper.AdicSmoothDualizingFinitePowers
import Sheaf.Paper.FiniteTateLocalRootTensorsExt

/-! # Finite comparisons for the adic smooth dualizing model

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.md
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing

open AlgebraicGeometry.Scheme

attribute [local irreducible] PurCompactSupport.image
  sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar

/-- The positive completed coefficient line already used by the signed twists.
Source: the corollary proof, completed coefficient object and its Tate power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev line (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistPower T
    (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension T)
    (purTwistIntegralModule T P.coefficients.l P.extension) d

/-- Pure completed-coefficient root tensors in that line, including its zero power.
Source: the corollary proof, the projection-normalized integral Tate line
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def generator (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted
      P.coefficients.l P.extension T).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W) →
      (line P T d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction T P.coefficients.l P.extension W).toSMul a
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x 0))
  | d + 2, x => SheafOfModules.siteSheafTensorTmul
      (line P T (d + 1)) (purTwistIntegralModule T P.coefficients.l P.extension) W
      (generator P T W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x (Fin.last (d + 1))))

/-- The finite projection of a completed Tate power is fixed on every local root
and completed scalar, rather than chosen as an unnormalized line isomorphism.
Source: corollary proof, reduction to the normalized finite coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: project completed scalars to the finite quotient. The integral root tensor
is defined over the discrete constants; its quotient is purTwistFiniteOne.
The tensor universal property gives the first-power map and its tensor powers.
At power zero use the coefficient projection. These generators generate locally,
so the displayed equations determine the morphism uniquely, including on the empty site. -/
theorem existsUnique_lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! p : line P T d ⟶
        (scalarReductionRestriction P.coefficients.l P.extension T n).obj
          (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)),
      ∀ (W : T.ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted
          P.coefficients.l P.extension T).obj.obj W)
        (x : Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W),
        p.val.app W (generator P T W a d x) =
          @SMul.smul ((integralCoefficientSheaf
              P.coefficients.l P.extension T n).obj.obj W)
            ((finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W)
            (
              (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W
            ).isModule.toSMul
            ((completedIntegralCommRingProjectionUnrestricted
              P.coefficients.l P.extension T n).hom.app W a)
            (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 d x) := by
  sorry

/-- The fixed positive finite level, with the original global conventions unchanged.
Source: corollary proof, reductions modulo every positive power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }

/-- The projection selected by its unique root-tensor equations.
Source: corollary proof, integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_lineProjection P T n d).exists.choose

attribute [local irreducible] etalePowerComparison

set_option backward.isDefEq.respectTransparency false in
/-- The unique finite site comparison fixed by the root-limit projections.
Source: corollary proof, finite normalization; finite Tate site descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: finite Tate site descent gives the comparison for the annihilator ell^(n+1).
The displayed projection formula is its defining normalization. Local root lifts
and pure tensor generation make two such comparisons equal. -/
theorem existsUnique_rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (_aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    ∃! b : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).obj
        (finiteEtaleTateTwist T (levelSetting P n).diagonalExponent
          (levelSetting P n).Coefficient (levelSetting P n).diagonalExponent_annihilates d) ≅
        finiteTateProSheaf P.coefficients.l P.extension n T d,
      IsFiniteTateSiteComparison P.coefficients.l P.extension n T n
        (levelSetting P n).diagonalExponent_annihilates d b := by
  have hpow : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa [levelSetting, PurityFiniteSetting.diagonalExponent] using
      (levelSetting P n).diagonalExponent_isUnit _aT
  have hl : IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
    apply (isUnit_pow_iff (Nat.ne_of_gt (Nat.zero_lt_succ n))).mp
    simpa [Nat.succ_eq_add_one] using hpow
  obtain ⟨b, hb, _⟩ := finite_tate_site_descent P.coefficients.l P.extension n
  refine ⟨b T hl n (levelSetting P n).diagonalExponent_annihilates d,
    hb T hl n (levelSetting P n).diagonalExponent_annihilates d, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply finiteTate_local_root_tensors_hom_ext P.coefficients.l P.extension n T hl n
    (levelSetting P n).diagonalExponent_annihilates d
  intro U W v a z x hx
  exact (hb' U W v a z x hx).trans
    ((hb T hl n (levelSetting P n).diagonalExponent_annihilates d U W v a z x hx).symm)

/-- The finite comparison selected from its unique root-projection characterization.
Source: corollary proof, finite coefficient comparisons
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :=
  (existsUnique_rootComparison P T aT n d).exists.choose

/-- A realization comparison fixes each scalar-unit section of the original sheaf.
Source: the corollary's fixed-to-intrinsic finite coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsScalarUnitRealization (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : proEtaleRingModules T (proEtaleConstantRing T A))
    (e : (sfIntrinsicModuleEquivalence T A).functor.obj M ≅ N) : Prop :=
  ∀ (W : T.ProEtᵒᵖ) (y : M.obj.obj W),
    HEq (e.hom.val.app W (sfIntrinsicRealizationUnit T A M W y)) y

/-- The finite fixed-scalar realization is fixed on every scalar-unit section.
Source: corollary proof, canonical finite coefficient presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: restriction to the constant scalar action is inverse to the canonical
finite coefficient realization. The realization unit sends a section to its
scalar-unit generator. Extend the identity on these sections by local scalar
linearity and sheafification. The two inverse composites are identities on those
generators, which also proves uniqueness. -/
theorem existsUnique_finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d) ≅
        finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ),
      IsScalarUnitRealization T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        (finiteTateProSheaf P.coefficients.l P.extension n T d)
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)) e := by
  sorry

/-- The preceding canonical realization, with no generator or orientation choice.
Source: corollary proof, finite comparison
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_finiteRealization P T n d).exists.choose

attribute [local irreducible] finiteRealization

/-- Exact functors carry shifted single complexes to the shifted single image.
The data is the standard shift comparison followed by the single-complex comparison.
Source: the corollary's exact coefficient and site transports
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def exactSingleShiftIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (M : C) (j : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M))⟦j⟧ :=
  (F.mapDerivedCategory.commShiftIso j).app _ ≪≫
    (shiftFunctor _ j).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)

attribute [local irreducible] exactSingleShiftIso

/-- The exact single-complex comparison in the literal intrinsic-derived coordinates.
This exposes its endpoints without repeatedly unfolding the derived equivalence.
Source: the corollary's exact coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def intrinsicExactSingleShiftIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) (j : ℤ) :
    (sfIntrinsicDerivedEquivalence T A).functor.obj
        (((DerivedCategory.singleFunctor _ 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((sfIntrinsicModuleEquivalence T A).functor.obj M))⟦j⟧ :=
  exactSingleShiftIso (sfIntrinsicModuleEquivalence T A).functor M j

attribute [local irreducible] intrinsicExactSingleShiftIso

/-- The site part of the finite-power comparison, with its normalized root target.
This is the same three factors as in the original finitePowerComparison.
Source: the corollary's finite normalized Tate presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteSitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (levelSetting P n).diagonalTwist T d ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d))⟦2 * (d : ℤ)⟧ :=
  (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).mapDerivedCategory.mapIso
    (etalePowerComparison (levelSetting P n) T
      ((levelSetting P n).diagonalExponent_isUnit aT) d) ≪≫
    exactSingleShiftIso (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T) _ (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (rootComparison P T aT n d))

attribute [local irreducible] finiteSitePowerComparison

/-- Canonical comparison from the finite purity orientation's ordered shifted tensor
model to the specified intrinsic finite Tate power placed in degree -2d.
Source: corollary proof, normalized finite purity at each reduction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)))⟦2 * (d : ℤ)⟧ :=
  (sfIntrinsicDerivedEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.mapIso
    (finiteSitePowerComparison P T aT n d) ≪≫
    intrinsicExactSingleShiftIso T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) _
      (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (finiteRealization P T n d))

end AdicSmoothDualizing
end WeilConjectures

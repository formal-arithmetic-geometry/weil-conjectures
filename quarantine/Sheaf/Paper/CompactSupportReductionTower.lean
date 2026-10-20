/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction

/-!
# Coherent compact-support reduction towers

Source: Weil blueprint, `sk-def-sf-operations`, proof of
`lem-weil-compact-support-representative-independence`, first sentence;
Stacks Project, Tags 0940, 0941 and 06YY; Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-weil-compact-support-reduction-tower-functor).

The target is the derived category of strict towers of modules over the completed
coefficient sheaf. Evaluation comparisons are natural isomorphisms of functors.
Every pair of positive levels is constrained by the actual quotient map; index n
means exponent n+1. The proper image is derived separately after open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive finite coefficient levels are finite, using the recorded theorem.
Source: blueprint coefficient extension, clause 4
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
instance compactSupportLevelFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The canonical quotient for any pair of positive coefficient levels.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelQuotient (m n : ℕ) (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The same quotient after constant sheafification on the small pro-etale site.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelSheafQuotient (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E W m ⟶ integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (compactSupportLevelQuotient l E m n h).ulift)

private theorem compactSupportLevelSheafQuotient_self (W : Scheme.{u}) (n : ℕ) :
    compactSupportLevelSheafQuotient l E W n n le_rfl = 𝟙 _ := by
  unfold compactSupportLevelSheafQuotient
  have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
    Ideal.Quotient.factor_eq
  rw [hq]
  exact (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id _

private theorem compactSupportLevelSheafQuotient_step
    (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) ≫
        compactSupportLevelSheafQuotient l E W m n h =
      compactSupportLevelSheafQuotient l E W (m + 1) n (h.trans (Nat.le_succ m)) := by
  unfold compactSupportLevelSheafQuotient
  rw [← Functor.map_comp]
  congr 1
  ext x
  change (compactSupportLevelQuotient l E m n h)
      ((compactSupportLevelQuotient l E (m + 1) m (Nat.le_succ m)) x.down) =
    (compactSupportLevelQuotient l E (m + 1) n (h.trans (Nat.le_succ m))) x.down
  exact Ideal.Quotient.factor_comp_apply _ _ x.down

/-- Limit projections commute with all coefficient quotients, including m=n.
Source: Stacks Tag 03CO; blueprint proof, steps 1--2
(blueprint: lem-weil-compact-support-reduction-tower-functor).
Proof: for adjacent levels this is the cone compatibility of the completed sheaf.
The quotient factor sends the class of a to the class of a, so successive factors
compose to the direct factor, and the equal-level factor is the identity. Apply
constant sheafification and induct on m-n to obtain compatibility for every pair. -/
theorem compactSupportProjection_comp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    completedIntegralCommRingProjectionUnrestricted l E W m ≫
        compactSupportLevelSheafQuotient l E W m n h =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
  induction m, h using Nat.le_induction with
  | base => simp only [compactSupportLevelSheafQuotient_self, Category.comp_id]
  | succ m h ih =>
    rw [← compactSupportLevelSheafQuotient_step l E W m n h, ← Category.assoc]
    have hs : completedIntegralCommRingProjectionUnrestricted l E W (m + 1) ≫
        compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) =
        completedIntegralCommRingProjectionUnrestricted l E W m := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply (forget₂ CommRingCat RingCat).map_injective
      ext x
      have hw := congrArg (fun v ↦ (v.hom.app U).hom x)
        (limit.w (integralCoefficientSheafSystem l E W)
          (homOfLE (Nat.le_succ m)).op)
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      convert hw using 1 <;> rfl
    rw [hs]
    exact ih

/-- The canonical composition of exact restrictions along a limit projection and
its quotient, induced by the identity on underlying sections.
Source: Stacks Tag 03DA; blueprint proof, steps 4 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictionComp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction l E W m ≅
      scalarReductionDerivedRestriction l E W n :=
  pbcDerivedRestrictComp
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)

/-- The quotient-induced derived reduction map. It is the transpose of the
reduction unit under the normalized derived tensor/restriction adjunction.
Thus this is id tensor q on K-flat representatives, rather than an arbitrary map.
Source: Stacks Tags 03CZ and 06YY; blueprint proof, steps 2 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportReductionMap (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W m).obj K ⟶
      ((proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory).obj
        ((scalarReductionDerivedExtension l E W n).obj K) :=
  (((derivedScalarExtensionRestrictionAdjunction l E W m).choose).homEquiv _ _).symm
    (((derivedScalarExtensionRestrictionAdjunction l E W n).choose).unit.app K ≫
      (compactSupportRestrictionComp l E W m n h).inv.app
        ((scalarReductionDerivedExtension l E W n).obj K))

/-- The specified finite-level composite, including its action on derived morphisms.
Source: Bhatt--Scholze, Definition 6.7.6; blueprint proof, step 4
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedLevel {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  scalarReductionDerivedExtension l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      scalarReductionDerivedRestriction l E Y n

/-- The required transition: quotient-induced reduction, compact support at the
larger level, the specified coefficient comparison, and composition of restrictions.
Source: blueprint proof, step 6; Bhatt--Scholze, Lemma 6.7.7
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedTransition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (compactSupportRestrictedLevel l E c m).obj K ⟶
      (compactSupportRestrictedLevel l E c n).obj K :=
  (scalarReductionDerivedRestriction l E Y m).map
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          (compactSupportReductionMap l E X m n h K) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
    (compactSupportRestrictionComp l E Y m n h).hom.app
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The canonical constant integral section of the completed coefficient sheaf.
It is obtained from the constant-to-completion map, whose projections are the actual
constant quotient sections. Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportConstantScalar (W : Scheme.{u}) (U : W.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
  ((integralConstantToCompletion l E W).hom.app U)
    (((toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app U)
          (ULift.up a))

/-- Normalization of a linear structure by the actual constant-section action.
Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def IsCompactSupportScalarAction (W : Scheme.{u})
    [Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W)] : Prop :=
  ∀ (M N : scalarReductionSource l E W) (v : M ⟶ N)
    (a : Padic.coefficientExtensionIntegers l E) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
    (a • v).val.app U x = compactSupportConstantScalar l E W U a • v.val.app U x

/-- There is a coherent exact integral-linear compact-support reduction tower functor.
Its natural evaluation comparisons identify every transition with the canonical
quotient/direct-image comparison, including adjacent and equal levels.
Source: blueprint `lem-weil-compact-support-representative-independence`, first
proof sentence; Stacks Tags 0940, 0941 and 06YY; Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-weil-compact-support-reduction-tower-functor).
Proof:
1. Form the ringed sequence site with quotient restriction maps. Its module sheaves
are semilinear coefficient systems, and it admits simultaneous K-injective resolutions
by lem-coef-semilinear-derived-sections, lem-weil-pbc-diagram-site-realization and
prop-pur-kinjective-resolutions-exist.
2. Derived pullback along the completed-to-system coefficient morphism gives exact
simultaneous reduction, computed by P tensor A_n on a flat-term K-flat resolution
(lem-weil-pbc-ringed-topoi-derived-pullback and lem-pc-kflat-resolution).
The strict chain maps id tensor q compose for all pairs of coefficient levels.
3. Apply exact open extension at every level, then the separately right-derived
proper direct image of the entire system. The geometric clauses of
lem-coef-semilinear-derived-sections identify its evaluations with Rp_* j_!,
including on all derived morphisms. They apply to arbitrary semilinear sections.
4. Restrict every level along B_Y to A_n. The projection compatibility makes the
transitions B_Y-linear. Exact restriction descends to the derived strict-tower
category by lem-weil-pbc-exact-functor-derived-factorization.
5. Each factor is triangulated; use lem-pc-right-derived-functor-triangulated and
lem-weil-pbc-triangulated-functor-composite to obtain the composite shift structure.
6. Evaluation of the coherent system gives precisely the displayed transition:
apply compact support to the quotient-induced map and then its canonical scalar
comparison. The proper comparison is normalized on K-injective replacements by
lem-weil-proetale-direct-image-restriction-of-scalars, without assuming that
restriction preserves K-injectives; the open comparison is identity on underlying
abelian sheaves (lem-sf-compact-support-restriction-of-scalars).
7. Quotient composition holds on K-flat complexes before localization; the
coefficient comparison cocycle carries it to every pair m>=n and is natural in K.
8. Compatible constant sections define the two normalized linear structures.
All four factors preserve these scalars on complexes and their resolution roofs,
so their composite is R-linear. The derived tower action is induced levelwise,
not a scalar action chosen after evaluation. -/
theorem exists_compactSupportReductionTower
    (K₀ : Type u) [Field K₀] (X Y : Scheme.{u})
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hl : IsUnit (l : K₀)) (c : Compactification f) :
    ∃ (sX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X))
      (sY : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)),
      (fun [linearX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X)]
        [linearY : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)] ↦
        IsCompactSupportScalarAction l E X ∧ IsCompactSupportScalarAction l E Y ∧
        ∃ T : DerivedCategory (scalarReductionSource l E X) ⥤
            DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)),
          T.Linear (Padic.coefficientExtensionIntegers l E) ∧
          ∃ (_shift : T.CommShift ℤ), T.IsTriangulated ∧
            ∃ e : ∀ n : ℕ,
                T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
                  compactSupportRestrictedLevel l E c n,
              ∀ (m n : ℕ) (h : n ≤ m) (K : DerivedCategory (scalarReductionSource l E X)),
                (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
                    m n h).app (T.obj K) ≫ (e n).hom.app K =
                  (e m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K)
        (linearX := sX) (linearY := sY) := by
  sorry

end WeilConjectures

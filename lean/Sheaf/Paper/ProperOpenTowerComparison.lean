/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral

/-!
# Open-adjunction normalization of proper/open comparison on strict towers

Source: Stacks Project, Tags 0F7B, 0F7F and 0941; the strict diagram enhancement and
normalization are the explicit agent assertion in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).

All operations are the published constant-coefficient strict-tower operations. Positive
level `n+1` is indexed by `n : ℕ`. The restriction arrow is constructed using the
cartesian square mate, the clopen lift, and the normalized direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (A : Type (u + 1)) [CommRing A]

/-- Restrict open extension along the open part of the fibre product. The inverse
open unit removes `G_b J_b`, after factoring `k = b s`.
Source: Stacks 09AE and the clopen factorization of 0F7B
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictedExtension {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    J A k ⋙ G A (pullback.fst p i) ≅ J A (squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h)).symm (G A (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J A (squareLift k r p i h))
    (@asIso _ _ _ _ (jAdj A (pullback.fst p i)).unit
      (jAdj_unit_isIso A (pullback.fst p i))).symm ≪≫
  Functor.rightUnitor _

/-- The actual open-restriction arrow: the cartesian inverse/direct-image mate,
restricted extension, the clopen open-to-direct-image map, and direct-image composition.
Source: Stacks 04J0, 07A7, 09AE and 0F7B, applied on the strict diagram site
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k)
    (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (properOpenRestrictedExtension A k r p i h).hom
    (R A (pullback.snd p i)) ≫
  Functor.whiskerRight (openToR A (squareLift k r p i h)) (R A (pullback.snd p i)) ≫
  (rComp A (squareLift k r p i h) (pullback.snd p i)).hom ≫
  (eqToIso (congrArg (R A) (pullback.lift_snd k r h))).hom

/-- The open adjunct of the inverse restriction isomorphism, as a transformation on
the entire derived strict-tower category. No evaluation or arbitrary choice is used.
Source: Stacks 03DI and 07A7, blueprint open-adjunction normalization
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenOpenAdjunct {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r) :
    R A r ⋙ J A i ⟶ J A k ⋙ R A p :=
  (((jAdj A i).whiskerRight (Derived A U)).homEquiv _ _).symm lam.inv

/-- In a cartesian square the restriction comparison is the square mate followed
by the inverse open unit, with the associators made explicit.
Source: Stacks 07A7 and the cartesian normalization in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenCartesianRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k) (exchange A k r p i h) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (@asIso _ _ _ _ (jAdj A k).unit (jAdj_unit_isIso A k)).inv (R A r) ≫
  (Functor.leftUnitor _).hom

/-- Specialize the existing origin witness and scalar restriction to `A/I^(n+1)`.
This is just the dependent pair of the bounded-below finite-coefficient object, its
retained etale origin, and the specified scalar-restriction isomorphism.
Source: Stacks 099R and the displayed origin hypothesis in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenQuotientOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ) : Type _ :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  Σ F : FiniteCoefficientDerivedCategoryPlus U (A ⧸ I ^ (n + 1)),
    Σ _origin : EtaleOriginWitness U (A ⧸ I ^ (n + 1)) F,
      (finiteRestriction A U (A ⧸ I ^ (n + 1)) (Ideal.Quotient.mk _)).mapDerivedCategory.obj
        F.obj ≅ (ev A U n).obj N

/-- Use that very quotient origin in the existing finite evaluation comparisons.
Source: Stacks 099R and the blueprint's finite evaluation clause
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenScalarOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ)
    (w : properOpenQuotientOrigin A I U N n) :
    ScalarEtaleOrigin A U ((ev A U n).obj N) :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  { Λ := A ⧸ I ^ (n + 1)
    topology := inferInstance
    discrete := inferInstance
    φ := Ideal.Quotient.mk _
    F := w.1
    origin := w.2.1
    iso := w.2.2 }

/-- The unique canonical restriction isomorphism and its open adjunct, with the finite
evaluation normalization. The equation with the open unit is the typed form of
`λ G_i Γ = 1` under `G_i J_i ≅ 1`. The equality with `gamma` identifies actual natural
transformations before evaluation, including noncartesian squares.

Source: Stacks 0F7B and 0F7F with 0941; the strict-tower enhancement and its open
normalization are agent assertions, as explicitly recorded in the DAG source
(blueprint: lem-sp-proper-open-tower-comparison).

Proof, following the five DAG steps:
1. Use the published strict constant-coefficient operations with B=A and n indexing
   positive level n+1. Weakly-etale localization and localizedModuleExactIndependent
   identify moduleJ with the prescribed sheafified extension presheaf: maps to the
   open are unique when they exist, so its direct sum is the stated module or zero.
   This preserves the open units and gives the same exact tower and derived adjunctions.
   Noetherian schemes make the open immersions quasi-compact. The strict-tower calculus
   supplies the clopen lift s into V times_Z W, with b s=k and q s=r.
2. Split every test object over the clopen image of s and its complement. Sheaf gluing
   identifies modules, transitions and differentials with pairs. Both J_s and s_* are
   F mapped to (F,0); openToR is identity on the first factor and zero on the other.
   Thus it is invertible and the direct-image unit is the clopen projection pi.
   The unit-normalized open compositor gives properOpenRestrictedExtension.
3. On the ringed diagram site choose a K-injective resolution. Restriction G_b
   preserves K-injectives because it is right adjoint to exact J_b. Localization of
   the ringed-site morphism identifies both restricted direct images with q_*G_b
   of that same resolution, by identity on sections. This is precisely exchange.
   Compose with step 2 and the normalized direct-image compositor to obtain the
   displayed properOpenRestrictionMap, an isomorphism. For a cartesian square the
   clopen lift is an isomorphism and this is the square mate followed by the open unit.
4. Compute the open transpose of the existing proper mate gamma. The square-mate
   unit equation cancels the p adjunction unit; the restriction of beta is the open
   identity. Naturality moves the r counit past the restriction comparison. What
   remains is R_q J_s epsilon_r composed with R_q pi_s G_q R_r and eta_q R_r.
   Since pi_s=eta_s under J_s=R_s, the composite-unit formula and the r triangle
   identity make this the identity of R_r. The open Hom bijection therefore identifies
   gamma with properOpenOpenAdjunct, as transformations on derived strict towers.
5. Apply gamma_isIso and gamma_evaluation to the specified quotient origins, using
   finiteGamma from properOpenInterchangeCoherence and the canonical finiteSource
   and finiteTarget comparisons. Each origin has its own lower bound; the strict
   transitions belong to N and no transitions between etale origins are required.
   Substitute step 4 before evaluating; no faithfulness of evaluation is invoked.
   Uniqueness of lambda follows because its hom is the specified restriction map. -/
theorem properOpenTowerComparison [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ∃! lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r,
      lam.hom = properOpenRestrictionMap A k r p i h ∧
      (IsPullback k r p i → lam.hom = properOpenCartesianRestrictionMap A k r p i h) ∧
      properOpenOpenAdjunct A k r p i lam = gamma A k r p i h ∧
      (∀ M : Derived A U,
        (jAdj A i).unit.app ((R A r).obj M) ≫
            (G A i).map ((properOpenOpenAdjunct A k r p i lam).app M) ≫ lam.hom.app M =
          𝟙 ((R A r).obj M)) ∧
      ∀ (N : Derived A U) (w : ∀ n : ℕ, properOpenQuotientOrigin A I U N n),
        IsIso ((properOpenOpenAdjunct A k r p i lam).app N) ∧
        ∀ n : ℕ,
          (finiteSource A r i N n (properOpenScalarOrigin A I U N n (w n))).hom ≫
              (ev A Z n).map ((properOpenOpenAdjunct A k r p i lam).app N) =
            (HD A Z (properOpenScalarOrigin A I U N n (w n)).Λ
                (properOpenScalarOrigin A I U N n (w n)).φ).map
                ((finiteGamma (properOpenScalarOrigin A I U N n (w n)).Λ k r p i h).hom.app
                  (properOpenScalarOrigin A I U N n (w n)).origin.L) ≫
              (finiteTarget A k p N n (properOpenScalarOrigin A I U N n (w n))).hom := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower

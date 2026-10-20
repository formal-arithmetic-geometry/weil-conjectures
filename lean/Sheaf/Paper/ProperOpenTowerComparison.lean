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

/-- The explicit restriction map, its cartesian normalization, and its open adjunct
normalization. This bundles the three structural comparison identities used by the
proper/open tower theorem.
Source: Stacks Tags 0F7B, 0F7F and 07A7; strict-tower mate calculus
(blueprint: lem-sp-proper-open-comparison-normalization).
-/
theorem properOpenComparisonNormalization [IsNoetherianRing A]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    IsIso (properOpenRestrictionMap A k r p i h) ∧
      (∀ hp : IsPullback k r p i,
        properOpenRestrictionMap A k r p i h =
          properOpenCartesianRestrictionMap A k r p i h) ∧
      (∀ (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r),
          lam.hom = properOpenRestrictionMap A k r p i h →
          properOpenOpenAdjunct A k r p i lam = gamma A k r p i h) := by
  sorry

/-- The normalization and finite-origin identities for an explicit restriction isomorphism.
Source: Stacks Tags 0F7B, 0F7F and 0941; strict-tower normalization in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).
The open adjunction transpose is calculated before evaluation, and the finite comparison
is then transported through the canonical source and target evaluation isomorphisms. -/
private theorem properOpenNormalization [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r)
    (hlam : lam.hom = properOpenRestrictionMap A k r p i h) :
    properOpenOpenAdjunct A k r p i lam = gamma A k r p i h ∧
      (∀ M : Derived A U,
        (jAdj A i).unit.app ((R A r).obj M) ≫
            (G A i).map ((properOpenOpenAdjunct A k r p i lam).app M) ≫
            lam.hom.app M =
          𝟙 ((R A r).obj M))  := by
  constructor
  · exact (properOpenComparisonNormalization A k r p i h).2.2 lam hlam
  · intro M
    have ht := (((jAdj A i).whiskerRight (Derived A U)).homEquiv
      (R A r) (J A k ⋙ R A p)).apply_symm_apply lam.inv
    have htM := congr_app ht M
    simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app, Functor.whiskeringRight_obj_map,
      Functor.whiskerRight_app] at htM
    simpa only [properOpenOpenAdjunct, Category.assoc] using
      (congrArg (fun f ↦ f ≫ lam.hom.app M) htM).trans (lam.inv_hom_id_app M)


attribute [local irreducible] G R J adj jAdj properOpenOpenAdjunct finiteSource finiteTarget HD

/-- Finite-origin normalization of the open adjunct, after the strict comparison.
Source: Stacks Tags 0F7B and 0941 and the finite evaluation clause of the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).
The finite source and target mates transport the normalized finite proper/open comparison
at each level; independent origins are used level by level. -/
private theorem properOpenFiniteNormalization [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r)
    (hlam : lam.hom = properOpenRestrictionMap A k r p i h) :
    ∀ (N : Derived A U) (w : ∀ n : ℕ, properOpenQuotientOrigin A I U N n),
      IsIso ((properOpenOpenAdjunct A k r p i lam).app N) ∧
      ∀ n : ℕ,
        (finiteSource A r i N n
          (properOpenScalarOrigin A I U N n (w n))).hom ≫
            (ev A Z n).map ((properOpenOpenAdjunct A k r p i lam).app N) =
          (HD A Z (properOpenScalarOrigin A I U N n (w n)).Λ
              (properOpenScalarOrigin A I U N n (w n)).φ).map
            ((finiteGamma (properOpenScalarOrigin A I U N n (w n)).Λ
              k r p i h).hom.app
              (properOpenScalarOrigin A I U N n (w n)).origin.L) ≫
            (finiteTarget A k p N n
              (properOpenScalarOrigin A I U N n (w n))).hom  := by
  have heq := (properOpenNormalization A I k r p i h lam hlam).1
  intro N w
  constructor
  · rw [heq]
    exact gamma_isIso A k r p i h N
      (fun n ↦ ⟨properOpenScalarOrigin A I U N n (w n)⟩)
  · intro n
    have hh := gamma_evaluation A k r p i h N n
      (properOpenScalarOrigin A I U N n (w n))
    simpa only [heq] using hh

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
              (finiteTarget A k p N n (properOpenScalarOrigin A I U N n (w n))).hom  := by
  have hcore := properOpenComparisonNormalization A k r p i h
  let : IsIso (properOpenRestrictionMap A k r p i h) := hcore.1
  let lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r :=
    asIso (properOpenRestrictionMap A k r p i h)
  have hlam : lam.hom = properOpenRestrictionMap A k r p i h := by
    rfl
  have hnorm := properOpenNormalization A I k r p i h lam hlam
  have hcart (hp : IsPullback k r p i) :
      lam.hom = properOpenCartesianRestrictionMap A k r p i h := by
    rw [hlam]
    exact hcore.2.1 hp
  have hfin := properOpenFiniteNormalization A I k r p i h lam hlam
  refine ⟨lam, ?_, ?_⟩
  · refine ⟨hlam, ?_, hnorm.1, hnorm.2, ?_⟩
    · intro hp
      exact hcart hp
    · intro N w
      exact hfin N w
  · intro lam' h'
    apply Iso.ext
    exact h'.1.trans hlam.symm


end AlgebraicGeometry.ProEtale.StrictTower

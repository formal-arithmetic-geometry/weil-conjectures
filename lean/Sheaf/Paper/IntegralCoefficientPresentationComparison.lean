/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Projection-normalized integral coefficient presentation comparison

Source: Bhatt--Scholze, Section 6.5, convention before Definition 6.5.1,
Lemma 4.2.12 and Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison).

The existing constants-to-functions comparison is reused. The quotient isomorphisms e_n
and the completed comparison e_T are the unique ones with the node's normalizations:
the statement asserts their existence and uniqueness and then quantifies over any family
so normalized. It does not import the parent stratified-perfect module (which cites this
node in its proof), so that module can import this one.
The extra compatibility predicate records finite derived reductions, their genuine
adjunction units, all quotient transitions, and the two arrows of the product Roos diagram.
No constructibility or completeness membership is asserted. Index n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralCoefficientPresentation

-- The published free-universe sheaf instance would leave a universe unassigned here;
-- the fixed coefficient-universe instance of the imported modules is used instead.
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

/-- The restricted derived finite reduction for a specified quotient projection.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
abbrev reduction {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (π : R ⟶ S) := pbcDerivedExtend π ⋙ pbcDerivedRestrict π

/-- The canonical restricted map from a larger quotient to a smaller quotient.
It is the adjoint of the smaller quotient unit, using the normalized scalar-restriction
composition. On K-flat models it sends b tensor x to q(b) tensor x.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def transition {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (π : R ⟶ S) (q : S ⟶ B) (π' : R ⟶ B) (h : π ≫ q = π')
    (K : DerivedCategory (pbcModules T R)) :
    (reduction π).obj K ⟶ (reduction π').obj K :=
  (pbcDerivedRestrict π).map (pbcReductionTransition π q π' h K) ≫
    (pbcDerivedRestrictComp π q π' h).hom.app ((pbcDerivedExtend π').obj K)

/-- Derive an identity-on-sections comparison of the two composite restrictions.
Source: Stacks 03DA and 015F
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def derivedSquare {T : Scheme.{u}}
    {R S Rn Sn : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ≅ S) (b : Rn ≅ Sn) (π : R ⟶ Rn) (ρ : S ⟶ Sn)
    (r : pbcRestrict b.hom ⋙ pbcRestrict π ≅ pbcRestrict ρ ⋙ pbcRestrict e.hom) :
    pbcDerivedRestrict b.hom ⋙ pbcDerivedRestrict π ≅
      pbcDerivedRestrict ρ ⋙ pbcDerivedRestrict e.hom :=
  (Functor.mapDerivedCategoryCompIso (pbcRestrict b.hom) (pbcRestrict π)).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
      Functor.mapDerivedCategoryCompIso (pbcRestrict ρ) (pbcRestrict e.hom)

/-- The finite comparison after restriction to the completed coefficient ring.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def restrictedComparison {T : Scheme.{u}}
    {R S Rn Sn : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ≅ S) (b : Rn ≅ Sn) (π : R ⟶ Rn) (ρ : S ⟶ Sn)
    (r : pbcRestrict b.hom ⋙ pbcRestrict π ≅ pbcRestrict ρ ⋙ pbcRestrict e.hom)
    (α : pbcDerivedRestrict e.hom ⋙ pbcDerivedExtend π ≅
      pbcDerivedExtend ρ ⋙ pbcDerivedRestrict b.hom)
    (K : DerivedCategory (pbcModules T S)) :
    (reduction π).obj ((pbcDerivedRestrict e.hom).obj K) ≅
      (pbcDerivedRestrict e.hom).obj ((reduction ρ).obj K) :=
  (pbcDerivedRestrict π).mapIso (α.app K) ≪≫
    (derivedSquare e b π ρ r).app ((pbcDerivedExtend ρ).obj K)

/-- Compatibility of the two product Roos arrows, with the product comparison fixed
by every projection. Product existence is supplied separately, not assumed of a complex.
Source: Bhatt--Scholze, Propositions 3.1.10--3.1.11; Stacks 08TC
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def RoosCompatible {C : Type v} [Category.{w} C] [Preadditive C]
    {D : Type v} [Category.{w} D] [Preadditive D] (F : C ⥤ D)
    (K : C) (P : ℕ → D) (Q : ℕ → C)
    (cP : ∀ n, F.obj K ⟶ P n) (cQ : ∀ n, K ⟶ Q n)
    (tP : ∀ n, P (n + 1) ⟶ P n) (tQ : ∀ n, Q (n + 1) ⟶ Q n)
    (β : ∀ n, P n ≅ F.obj (Q n)) [HasProduct P] [HasProduct Q] : Prop :=
  ∃ z : F.obj (∏ᶜ Q) ≅ ∏ᶜ P,
    (∀ n, z.hom ≫ Pi.π P n = F.map (Pi.π Q n) ≫ (β n).inv) ∧
    F.map (Pi.lift cQ) ≫ z.hom = Pi.lift cP ∧
    F.map (towerTransitionEndomorphism tQ) ≫ z.hom =
      z.hom ≫ towerTransitionEndomorphism tP

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The commutative finite coefficient comparison ē_n = e_n ∘ κ_n⁻¹ for a family q of
quotient isomorphisms; the theorem applies it to the uniquely normalized family.
Source: Bhatt--Scholze, Section 6.5, Lemma 4.2.12
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def level (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (n : ℕ) : (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      integralCoefficientCommRingSheaf l E T n :=
  (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso (q n).toCommRingCatIso

/-- The actual detailed finite coefficient diagram, retaining commutativity.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def detailedSystem : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ integralCoefficientCommRingSheaf l E T n) (fun n ↦
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))

/-- The derived compatibility clauses, expressed using the published scalar adjunctions.
The section formula on r prevents substitution of an arbitrary restriction comparison.
The unit equation then fixes the derived tensor comparison. The transition equation is
for every quotient arrow, including the identity. RoosCompatible uses the actual 1-s.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY and 08TC
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def DerivedCompatible
    (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E T)
    (hρ : ∀ (b a : ℕ) (hab : a ≤ b),
      completedIntegralCommRingProjectionUnrestricted l E T b ≫
          (detailedSystem l E T).map (homOfLE hab).op =
        completedIntegralCommRingProjectionUnrestricted l E T a) : Prop :=
  ∃ r : ∀ n, pbcRestrict (level l E T q n).hom ⋙
        pbcRestrict (pbcAdicProjection T (pbcIntegralDatum l E) n) ≅
      pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E T n) ⋙
        pbcRestrict e.hom,
    (∀ (n : ℕ) (M : pbcModules T (integralCoefficientCommRingSheaf l E T n))
      (U : T.ProEtᵒᵖ) (x : M.val.obj U), ((r n).hom.app M).val.app U x = x) ∧
    ∃ α : ∀ n, pbcDerivedRestrict e.hom ⋙
          pbcDerivedExtend (pbcAdicProjection T (pbcIntegralDatum l E) n) ≅
        pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T n) ⋙
          pbcDerivedRestrict (level l E T q n).hom,
      (∀ (K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T))) (n : ℕ),
        (pbcDerivedScalarAdjunction
            (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
              ((pbcDerivedRestrict e.hom).obj K) ≫
          (restrictedComparison e (level l E T q n)
            (pbcAdicProjection T (pbcIntegralDatum l E) n)
            (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) (α n) K).hom =
          (pbcDerivedRestrict e.hom).map
            ((pbcDerivedScalarAdjunction
              (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K)) ∧
      (∀ (K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T)))
          (b a : ℕ) (hab : a ≤ b),
        transition (pbcAdicProjection T (pbcIntegralDatum l E) b)
            (pbcAdicQuotient T (pbcIntegralDatum l E) b a hab)
            (pbcAdicProjection T (pbcIntegralDatum l E) a)
            (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab)
            ((pbcDerivedRestrict e.hom).obj K) ≫
          (restrictedComparison e (level l E T q a)
            (pbcAdicProjection T (pbcIntegralDatum l E) a)
            (completedIntegralCommRingProjectionUnrestricted l E T a) (r a) (α a) K).hom =
        (restrictedComparison e (level l E T q b)
            (pbcAdicProjection T (pbcIntegralDatum l E) b)
            (completedIntegralCommRingProjectionUnrestricted l E T b) (r b) (α b) K).hom ≫
          (pbcDerivedRestrict e.hom).map
            (transition (completedIntegralCommRingProjectionUnrestricted l E T b)
              ((detailedSystem l E T).map (homOfLE hab).op)
              (completedIntegralCommRingProjectionUnrestricted l E T a) (hρ b a hab) K)) ∧
      (∀ K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T)),
        ∃ (hP : HasProduct (fun n ↦
              (reduction (pbcAdicProjection T (pbcIntegralDatum l E) n)).obj
                ((pbcDerivedRestrict e.hom).obj K)))
          (hQ : HasProduct (fun n ↦
              (reduction (completedIntegralCommRingProjectionUnrestricted l E T n)).obj K)),
          @RoosCompatible _ _ _ _ _ _ (pbcDerivedRestrict e.hom) K
            (fun n ↦ (reduction (pbcAdicProjection T (pbcIntegralDatum l E) n)).obj
              ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦
              (reduction (completedIntegralCommRingProjectionUnrestricted l E T n)).obj K)
            (fun n ↦ (pbcDerivedScalarAdjunction
              (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
                ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦ (pbcDerivedScalarAdjunction
              (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K)
            (fun n ↦ transition (pbcAdicProjection T (pbcIntegralDatum l E) (n + 1))
              (pbcAdicQuotient T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))
              (pbcAdicProjection T (pbcIntegralDatum l E) n)
              (pbcAdicProjection_comp T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))
              ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦ transition (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
              ((detailedSystem l E T).map (homOfLE (Nat.le_succ n)).op)
              (completedIntegralCommRingProjectionUnrestricted l E T n)
              (hρ (n + 1) n (Nat.le_succ n)) K)
            (fun n ↦ restrictedComparison e (level l E T q n)
              (pbcAdicProjection T (pbcIntegralDatum l E) n)
              (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) (α n) K) hP hQ)

/-- Projection-normalized comparison of the two completed integral coefficient presentations.
Source: Bhatt--Scholze, Section 6.5, convention before Definition 6.5.1,
Lemma 4.2.12 and Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison).
The family q and the completed comparison e are quantified under their normalizations,
whose existence and uniqueness are the first and the ∃! conjuncts; so the remaining
clauses are about e_n and e_T themselves.

Proof: (1) ULift.down carries the lifted uniformizer ideal and its powers onto the
original ones. Descend it to the quotient and lift the target. Quotient surjectivity
proves uniqueness from the representative formula. The same formula proves every
transition square, including equal indices. (2) The integers-DVR theorem and finite
residue field show that all positive quotients are finite (the two coefficient
arithmetic nodes). (3) By finite-constant-sections, functions to a finite discrete ring
are the constant sheaf; they factor continuously and uniquely through connected
components. The induced comparison is the sheafification of constants-to-functions,
and its normalization proves compatibility with all quotient maps.
(4) Apply the finite comparisons coordinatewise to compatible families. The inverse
is coordinatewise inverse; the projections prove existence and uniqueness of the
completed comparison. (5) Ring-isomorphism tensor transport gives inverse exact
scalar restrictions, leaving underlying additive sheaves unchanged. (6) The exact
functor derived theorem descends these inverses and identifies cohomology; hence
both derived equivalences preserve and reflect every cohomology bound.
(7) Resolve by a flat-term K-flat complex. On tensors the finite comparison sends
x tensor a to x tensor b_n(a); the projection square gives balancedness. Its inverse
uses b_n inverse. The derived-change-of-rings universal counits descend it and give
resolution independence. (8) The normalized coefficient-adjunction unit is x tensor 1;
the comparison fixes it since b_n(1)=1. This identifies exactly the augmented reduction
tower maps, including the inverse resolution quasi-isomorphism in c_n.
(9) For every b>=a both transition composites send x tensor z to x tensor b_a(q(z));
this also respects the balancing normalization for iterated reductions.
(10) Countable-products-exact and derived-limit-existence clause 2 supply the products
for arbitrary unbounded complexes. (11) The equivalence preserves products. Their
projections uniquely fix the product comparison. The unit equality identifies the
first Roos arrow; additivity and the transition equality identify each component
pr_n minus pr_(n+1) followed by t_n of the second arrow. Apply the inverse equivalence
for the reverse identification. No distinguished triangle or membership claim is used. -/
theorem comparison :
    (∀ n : ℕ, ∃! q : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ x : PbcIntegralRing l E,
        q (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down)) ∧
    (∀ (n : ℕ),
      (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom =
        AdicCoefficients.constantComparison T
          (PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))) ∧
    (∀ (i j : ℕᵒᵖ) (f : i ⟶ j),
      (adicLisseRingSystem T (pbcIntegralDatum l E).ideal).map f ≫
          (pbcLevelConstantComparison T (pbcIntegralDatum l E) j.unop).hom =
        (pbcLevelConstantComparison T (pbcIntegralDatum l E) i.unop).hom ≫
          (pbcAdicRings T (pbcIntegralDatum l E)).map f) ∧
    ∃ hρ : ∀ (b a : ℕ) (hab : a ≤ b),
        completedIntegralCommRingProjectionUnrestricted l E T b ≫
            (detailedSystem l E T).map (homOfLE hab).op =
          completedIntegralCommRingProjectionUnrestricted l E T a,
    ∀ q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      (∀ (n : ℕ) (x : PbcIntegralRing l E),
        q n (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down)) →
    (∀ (b a : ℕ) (hab : a ≤ b),
      (q a).toRingHom.comp
          (reductionQuotientMap (pbcIntegralDatum l E).ideal b a hab) =
        ((ULift.ringEquiv : ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (a + 1)) ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))).comp
              (ULift.ringEquiv : ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (b + 1)) ≃+* _).toRingHom)).comp
          (q b).toRingHom) ∧
    (∀ (i j : ℕᵒᵖ) (f : i ⟶ j),
      (pbcAdicRings T (pbcIntegralDatum l E)).map f ≫ (level l E T q j.unop).hom =
        (level l E T q i.unop).hom ≫ (detailedSystem l E T).map f) ∧
    (∃! e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom) ∧
    ∀ e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      (∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom) →
    (pbcRestrict e.hom).IsEquivalence ∧
    (pbcRestrict e.inv).IsEquivalence ∧
    PreservesFiniteLimits (pbcRestrict e.hom) ∧
    PreservesFiniteColimits (pbcRestrict e.hom) ∧
    PreservesFiniteLimits (pbcRestrict e.inv) ∧
    PreservesFiniteColimits (pbcRestrict e.inv) ∧
    Nonempty (pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _) ∧
    Nonempty (pbcRestrict e.inv ⋙ pbcRestrict e.hom ≅ 𝟭 _) ∧
    (pbcDerivedRestrict e.hom).IsEquivalence ∧
    (pbcDerivedRestrict e.inv).IsEquivalence ∧
    Nonempty (pbcDerivedRestrict e.hom ⋙ pbcDerivedRestrict e.inv ≅ 𝟭 _) ∧
    Nonempty (pbcDerivedRestrict e.inv ⋙ pbcDerivedRestrict e.hom ≅ 𝟭 _) ∧
    (∀ (K : DerivedCategory
        (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T))) (m : ℤ),
      (DerivedCategory.IsLE ((pbcDerivedRestrict e.hom).obj K) m ↔
        DerivedCategory.IsLE K m) ∧
      (DerivedCategory.IsGE ((pbcDerivedRestrict e.hom).obj K) m ↔
        DerivedCategory.IsGE K m)) ∧
    (∀ (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m : ℤ),
      (DerivedCategory.IsLE ((pbcDerivedRestrict e.inv).obj K) m ↔
        DerivedCategory.IsLE K m) ∧
      (DerivedCategory.IsGE ((pbcDerivedRestrict e.inv).obj K) m ↔
        DerivedCategory.IsGE K m)) ∧
    DerivedCompatible l E T q e hρ := by
  sorry

end WeilConjectures.IntegralCoefficientPresentation

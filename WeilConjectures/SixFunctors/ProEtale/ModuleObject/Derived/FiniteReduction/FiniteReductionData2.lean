/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized

/-! # Canonical finite coefficient reduction data

Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md`, proof steps 1-2 (finite quotient reduction
and the specified comparison maps); setting of `sk-def-sf-setting`
(blueprint: def-sf-pf-finite-reduction-data).

The map and functors below are the canonical quotient reduction from
`A_{E,n+1}` to `A_{E,m+1}`. The six-functor comparison maps are the flatness-free
analogues of the published condensed coefficient-change maps of
`ChangeOfCoefficients`/`ChangeOfCoefficientsMate` (which assume flat scalar extension):
the Pull comparison is the scalar mate of `derivedComapLeftDerivedUpperStarIso`, the Push
comparison is the base-change mate of its inverse (as in `derivedPushHom_eq_mateEquiv`),
the compact-support comparison pastes Push with `derivedOpenImmersionShriekIso`, and the
tensor comparison is the tensorator of the left-derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor CategoryTheory.MonoidalCategory CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]

/-! The following maps are the flatness-free coefficient-change mates. -/

/-- The specified pull comparison has the original restriction square as its scalar mate.
Source: the canonical Pull clause of `def-sf-pf-finite-reduction-data`.
Proof: apply the mate equivalence to its inverse in the definition of `derivedPullHomFree`.
(blueprint: def-sf-pf-finite-reduction-data) -/
theorem mateEquiv_derivedPullHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    mateEquiv
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (ringMap ell E h) Y))
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (ringMap ell E h) X))
        (TwoSquare.mk _ _ _ _ (derivedPullHomFree ell E h g)) =
      TwoSquare.mk _ _ _ _ (derivedComapLeftDerivedUpperStarIso (ringMap ell E h) g).hom := by
  unfold derivedPullHomFree
  exact (mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (ringMap ell E h) Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (ringMap ell E h) X))).apply_symm_apply _

/-- The Pull mate is invertible, for every morphism `g` and on all unbounded objects.
Source: Stacks 0D6D (sites-cohomology, lemma-derived-pullback-composition), with Stacks 0G7E
and 07A4; recorded in node `def-sf-pf-finite-reduction-data`
(blueprint: def-sf-pf-finite-reduction-data).

Proof (postponed): (1) the change of coefficients `ρ` and the pullback `g` form a commuting
square of ringed topoi, the coefficient rings being pulled back from the point; (2) represent
an object by a K-flat complex `P` of flat terms; by Stacks 0G7E `g^*P` is again such, so
both sides are computed on `P` as `g^*P ⊗ Λ_m` and `g^*(P ⊗ Λ_m)`; (3) the mate of the restriction
square is the underived tensor comparison of `g^*` (Stacks 07A4) on these representatives,
which is an isomorphism; equivalently both composites are `L(ρ ∘ g)^*` (Stacks 0D6D). -/
theorem isIso_derivedPullHomFree {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) : IsIso (derivedPullHomFree ell E h g) := by
  let a := ringMap ell E h
  obtain ⟨b, hb, _⟩ :=
    DiagonalCoefficients.scalar_pullback_mate_inverse_normalized a g
  have he : derivedPullHomFree ell E h g =
      DiagonalCoefficients.scalarPullbackComparison a g := by
    unfold derivedPullHomFree DiagonalCoefficients.scalarPullbackComparison
      Adjunction.pushHomOfComapIso
    congr 2
    ext K
    simp only [a, derivedComapLeftDerivedUpperStarIso,
      DiagonalCoefficients.scalarRestrictionPullbackIso,
      leftDerivedUpperStarIsoMapDerivedCategory, derivedComapUpperStarIso,
      Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
  rw [he, ← hb]
  with_unfolding_all exact b.isIso_inv

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteReduction

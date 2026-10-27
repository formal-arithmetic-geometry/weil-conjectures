/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.Paper.RealizationCompletedPull
public import Sheaf.Paper.RealizationLocalizedPush
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.Paper.RealizationCoefficientSquare
import Sheaf.Paper.RealizationOrdinaryPullScalarUnit
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Restriction normalizations for the actual continuous scalar comparisons

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; Stacks, Tags 0D6D, 0D6E, 07A6.
(blueprint: lem-weil-pbc-realization-restriction-normalizations)

The auxiliary definitions only insert the canonical adjunction identification between
universal and termwise ordinary pullback. Both restriction comparisons are the published
ring-sheaf comparisons for the actual completed and continuous coefficient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures


variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {k : Type u} [Field k]
variable {T U : RealizationPullScheme l k} {f : T.scheme ⟶ U.scheme}
  {sT : RealizationScalarFunctorData l E T.scheme}
  {sU : RealizationScalarFunctorData l E U.scheme}

/-- The actual completed coefficient isomorphism, retaining its specified structure map.
Source: BS 6.8.2, 6.8.15 (blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionCoefficient
    (a : RealizationCompletedPullArrow T U f sT sU) :=
  @asIso _ _ _ _ (completedCoefficientMap f (pbcIntegralDatum l E)) a.coefficient_isIso

/-- Identify universal ordinary pullback with exact termwise pullback by the canonical
left-adjoint uniqueness isomorphism for their common actual direct image.
Source: Stacks 07A6 (blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionOrdinaryPull
    (a : RealizationCompletedPullArrow T U f sT sU) :
    pbcActualDerivedPull f (pbcIntegralDatum l E) ≅
      proEtaleRingDerivedPullback f _ _ (realizationRestrictionCoefficient a) :=
  (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).leftAdjointUniq
    (proEtaleRingDerivedAdjunction f _ _ (realizationRestrictionCoefficient a))

/-- The published coefficient-restriction pull comparison b, in the universal ordinary
pullback coordinates of the completed-pull node. The coefficient square is the actual one.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionPull
    (a : RealizationCompletedPullArrow T U f sT sU) :=
  proEtaleRingRestrictionDerivedPullback f
      (pbcAdicCompletion U.scheme (pbcIntegralDatum l E)) (rationalCoefficientSheaf l U.scheme E)
      (pbcAdicCompletion T.scheme (pbcIntegralDatum l E)) (rationalCoefficientSheaf l T.scheme E)
      (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
      (realizationRestrictionCoefficient a) a.rationalCoefficient a.coefficient_square.symm ≪≫
    Functor.isoWhiskerLeft (pbcDerivedRestrict (realizationPullScalarMap l E sU))
      (realizationRestrictionOrdinaryPull a).symm

/-- The published direct-image restriction comparison d for exactly the same coefficient
square as b. Source: Stacks 0D6E
(blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionPush
    (a : RealizationCompletedPullArrow T U f sT sU) :=
  proEtaleRingRestrictionDerivedDirectImage f
    (pbcAdicCompletion U.scheme (pbcIntegralDatum l E)) (rationalCoefficientSheaf l U.scheme E)
    (pbcAdicCompletion T.scheme (pbcIntegralDatum l E)) (rationalCoefficientSheaf l T.scheme E)
    (realizationPullScalarMap l E sU) (realizationPullScalarMap l E sT)
    (realizationRestrictionCoefficient a) a.rationalCoefficient a.coefficient_square.symm

/-- The ordinary scalar comparison alpha^o is the specified completed comparison after
F of the actual completion unit gamma, without replacing either map by an arbitrary iso.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionAlpha
    (a : RealizationCompletedPullArrow T U f sT sU)
    (N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) :=
  (pbcDerivedExtend (realizationPullScalarMap l E sT)).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app N.obj) ≫
    a.alpha.hom.app N

/-- Transport the already specified beta only along equalities of its actual coefficient
isomorphisms. Its scalar-extension unit normalization is unchanged.
Source: BS 6.8.15 (blueprint: lem-weil-pbc-realization-restriction-normalizations). -/
def realizationRestrictionBeta
    (a : RealizationCompletedPullArrow T U f sT sU)
    (p : RealizationLocalizedPushData l E f sT sU)
    (hA : p.integralPullback = realizationRestrictionCoefficient a)
    (hE : p.rationalPullback = a.rationalCoefficient) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
        proEtaleRingDerivedDirectImage f _ _ (realizationRestrictionCoefficient a) ⋙
          pbcDerivedExtend (realizationPullScalarMap l E sU) ⟶
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (realizationPullScalarMap l E sT) ⋙
          proEtaleRingDerivedDirectImage f _ _ a.rationalCoefficient :=
  by
    unfold realizationPullScalarMap
    exact hA ▸ hE ▸ p.beta

/-- The actual scalar pull, push and ambient counit comparisons have simultaneous
restriction normalizations. The push datum is supplied with the same coefficient maps;
beta is its specified scalar-adjunction transpose, not an arbitrary isomorphism.
Source: BS Lemma 6.8.2 and Remark 6.8.15; Stacks Tags 0D6D, 0D6E and 07A6.
(blueprint: lem-weil-pbc-realization-restriction-normalizations)

Proof:
1. Realization-completed-pull identifies c_h with precomposition on integral continuous
functions and c_E with its localization. Realization-coefficient-square gives the square
for these same normalized scalar maps. Ring-sheaf-change-adjunction supplies b and d;
left-adjoint uniqueness inserts the canonical ordinary-pullback coordinate comparison.
2. By the completed-pull normalization, alpha^comp after F(gamma) equals the ordinary
inverse-image/localization comparison. Continuous-coefficients-immersion-restriction
identifies E with the sheaf localization of A. Realization-scalar-functor identifies j
with the derived tensor unit m |-> 1 tensor m. Apply localization-inverse-image-coherence,
including its unbounded derived unit equation and identified-coefficient clause, and
cancel b. This proves the first equation for every integral N.
3. Use realization-localized-push with the same uniquely normalized coefficient maps.
Its beta is the scalar-adjunction inverse transpose of Q(j) followed by d inverse.
The unit formula for that adjunction is j followed by r(beta); this proves the second
equation. Equal coefficient isomorphisms transport the existing push datum and its beta.
4. In the Hom equation of ring-sheaf-change-adjunction set M=Q^E Z, N=Z and t=epsilon^E_Z.
Its E-adjunct is the identity, so the A-adjunct of b inverse followed by r(epsilon^E_Z)
is d_Z. The inverse A-adjunction sends d_Z to P(d_Z) followed by epsilon at r_T Z.
This proves the last equation for every ambient unbounded Z, without an integral
constructibility condition on r_T Z. All equations use the same b and d of step 1. -/
theorem realization_restriction_normalizations
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] [f.IsOver (Spec (.of k))]
    (a : RealizationCompletedPullArrow T U f sT sU) :
    ∃ p : RealizationLocalizedPushData l E f sT sU,
      ∃ hA : p.integralPullback = realizationRestrictionCoefficient a,
        ∃ hE : p.rationalPullback = a.rationalCoefficient,
          (∀ N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
            (pbcDerivedScalarAdjunction (realizationPullScalarMap l E sT)).unit.app
                ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj N.obj) ≫
              (pbcDerivedRestrict (realizationPullScalarMap l E sT)).map
                (realizationRestrictionAlpha a N) =
            (pbcActualDerivedPull f (pbcIntegralDatum l E)).map
                ((pbcDerivedScalarAdjunction (realizationPullScalarMap l E sU)).unit.app N.obj) ≫
              (realizationRestrictionPull a).inv.app
                ((pbcDerivedExtend (realizationPullScalarMap l E sU)).obj N.obj)) ∧
          (∀ M : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E),
            (pbcDerivedScalarAdjunction (realizationPullScalarMap l E sU)).unit.app
                ((proEtaleRingDerivedDirectImage f _ _
                  (realizationRestrictionCoefficient a)).obj M.obj) ≫
              (pbcDerivedRestrict (realizationPullScalarMap l E sU)).map
                ((realizationRestrictionBeta a p hA hE).app M) =
            (proEtaleRingDerivedDirectImage f _ _ (realizationRestrictionCoefficient a)).map
                ((pbcDerivedScalarAdjunction (realizationPullScalarMap l E sT)).unit.app M.obj) ≫
              (realizationRestrictionPush a).inv.app
                ((pbcDerivedExtend (realizationPullScalarMap l E sT)).obj M.obj)) ∧
          (∀ Z : DerivedCategory (proEtaleRingModules T.scheme (rationalCoefficientSheaf l
              T.scheme E)),
            (realizationRestrictionPull a).inv.app
                ((proEtaleRingDerivedDirectImage f _ _ a.rationalCoefficient).obj Z) ≫
              (pbcDerivedRestrict (realizationPullScalarMap l E sT)).map
                ((proEtaleRingDerivedAdjunction f _ _ a.rationalCoefficient).counit.app Z) =
            (pbcActualDerivedPull f (pbcIntegralDatum l E)).map
                ((realizationRestrictionPush a).hom.app Z) ≫
              (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).counit.app
                ((pbcDerivedRestrict (realizationPullScalarMap l E sT)).obj Z)) := by
  classical
  obtain ⟨p⟩ := realization_localized_push l E f sT sU k
  have hA : p.integralPullback = realizationRestrictionCoefficient a := by
    apply Iso.ext
    exact p.integralPullback_normalization
  have hE : p.rationalPullback = a.rationalCoefficient := by
    apply Iso.ext
    apply ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
    apply Sheaf.hom_ext
    ext V z
    apply rationalCoefficientValue_ext l E T.scheme _
    intro x
    exact (rationalCoefficientDirectImage_value l E f _
      p.rationalPullback_normalization V.unop z x).trans
      (rationalCoefficientDirectImage_value l E f _ a.rational_normalization
        V.unop z x).symm
  refine ⟨p, hA, hE, ?_, ?_, ?_⟩
  · intro N
    dsimp only [realizationRestrictionAlpha]
    rw [a.alpha_normalization]
    exact realizationOrdinaryPull_scalarUnit a N.obj
  · intro M
    have hn := p.beta_normalization M
    cases p
    cases hA
    cases hE
    dsimp only [realizationRestrictionBeta, realizationRestrictionPush]
    delta realizationPullScalarMap realizationRestrictionCoefficient
    rw [Adjunction.homEquiv_unit] at hn
    dsimp only [RealizationScalarFunctorData.scalarMap,
      Functor.comp_obj, Functor.id_obj, id_eq] at hn
    exact hn
  · intro Z
    unfold pbcDerivedRestrict
    let cA := realizationRestrictionCoefficient a
    let cE := a.rationalCoefficient
    let aU := realizationPullScalarMap l E sU
    let aT := realizationPullScalarMap l E sT
    let rT := (proEtaleRingRestrictScalars aT).mapDerivedCategory
    let rU := (proEtaleRingRestrictScalars aU).mapDerivedCategory
    let e := realizationRestrictionOrdinaryPull a
    let b := proEtaleRingRestrictionDerivedPullback f
      (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l U.scheme E)
      (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l T.scheme E) aU aT cA cE a.coefficient_square.symm
    let adj := proEtaleRingDerivedAdjunction f _ _ cA
    let adjE := proEtaleRingDerivedAdjunction f _ _ cE
    have hn := (proEtaleRingSheafChangeAdjunction f
      (pbcAdicCompletion U.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l U.scheme E)
      (pbcAdicCompletion T.scheme (pbcIntegralDatum l E))
      (rationalCoefficientSheaf l T.scheme E) aU aT cA cE
      a.coefficient_square.symm).2.2 _ Z (adjE.counit.app Z)
    have he : b.inv.app ((proEtaleRingDerivedDirectImage f _ _ cE).obj Z) ≫
        rT.map (adjE.counit.app Z) =
      (proEtaleRingDerivedPullback f _ _ cA).map ((realizationRestrictionPush a).hom.app Z) ≫
        adj.counit.app (rT.obj Z) := by
      have ht : adjE.homEquiv _ _ (adjE.counit.app Z) = 𝟙 _ :=
        adjE.right_triangle_components Z
      change adj.homEquiv _ _ (b.inv.app _ ≫
        rT.map (adjE.counit.app Z)) =
          rU.map (adjE.homEquiv _ _ (adjE.counit.app Z)) ≫
            (realizationRestrictionPush a).hom.app Z at hn
      rw [ht, rU.map_id, Category.id_comp] at hn
      have h := congrArg (adj.homEquiv _ _).symm hn
      simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
        Functor.comp_obj, Functor.id_obj] using h
    dsimp only [realizationRestrictionPull, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv]
    rw [Category.assoc]
    change e.hom.app _ ≫ (b.inv.app _ ≫ _) = _
    rw [he, ← Category.assoc]
    rw [← e.hom.naturality]
    rw [Category.assoc]
    exact congrArg (_ ≫ ·)
      ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).leftAdjointUniq_hom_app_counit
        adj (rT.obj Z))

end WeilConjectures

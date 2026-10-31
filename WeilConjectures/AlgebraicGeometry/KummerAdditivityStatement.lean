/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-!
# Statement of finite Kummer additivity

Source: blueprint `sec-smooth-purity/sk-prop-an/lem-pur-kummer-additivity.md`,
node `lem-pur-kummer-additivity`, order 3233; Stacks Tags 03P8, 03PL and 099W
(blueprint: lem-pur-kummer-additivity).

The classes are the published constructions of `WeilConjectures.AlgebraicGeometry.KummerAdditivity`:
`Etale.kummerFirstChern` is the unique derived arrow `A_T → A_T^et(1)[2]` realizing
`H²(φ_T)(δ¹_T(α_T(M)))`, and `ProEtale.kummerFirstChern` is its image under the
étale-to-pro-étale comparison, in the finite-root presentation `ν_T^*A_T^et(1)` of
the pro-étale Tate line (lem-amb-finite-tate-site-descent). They are not redefined
here. `OrdinaryFiniteTwistTransport` records the canonical pullback comparison by
its root-inclusion and pure-tensor normalizations, so the displayed comparisons are
the canonical ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

private theorem kummerFirstChern_eq_ordinary (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (M : T.Pic) :
    Etale.kummerFirstChern A N hA T hT M =
      Etale.ordinaryFiniteFirstChern A N hA T hT M := by
  apply (Etale.ordinaryFiniteClass_bijective_arbitraryBase A T
    (Scheme.finiteEtaleTateLine T N A hA) 2).injective
  rw [Etale.ordinaryFiniteFirstChern_class]
  unfold Etale.kummerFirstChern Etale.kummerFirstChernAbelian
  exact (Equiv.ofBijective (Etale.ordinaryFiniteClass A T
    (Scheme.finiteEtaleTateLine T N A hA) 2)
    (Etale.kummerFirstChernRealization_bijective A T _)).apply_symm_apply _

private theorem etale_kummer_pullback (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hA : (n : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A n hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤))) (M : Y.Pic) :
    (Etale.ordinaryFinitePullback A f).map (Etale.kummerFirstChern A n hA Y hY M) ≫
        (Etale.ordinaryFiniteShiftedLinePullback A n hA t f hY).hom =
      (Etale.ordinaryFiniteUnitPullback A f).hom ≫
        Etale.kummerFirstChern A n hA X hX (Scheme.Pic.map f M) := by
  rw [kummerFirstChern_eq_ordinary, kummerFirstChern_eq_ordinary]
  have hh := Etale.ordinaryFiniteFirstChern_pullback A n hA t f hY hX M
  simpa only [Etale.ordinaryFiniteLinePullbackMap, Etale.ordinaryFiniteArrowPullback,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id] using
    congrArg (fun z ↦ (Etale.ordinaryFiniteUnitPullback A f).hom ≫ z) hh

/--
Kummer additivity and functoriality at a finite coefficient stage `A = A_{E,n}`,
for an annihilating exponent `N ≥ 1`, `m = ℓ^N`, on a separated finite-type
`k`-scheme `T`: the étale class `c^et_{1,A}` and the pro-étale class `c_{1,A}` are
additive in the line bundle, and commute with pullback along every morphism
`f : T' → T` of separated finite-type `k`-schemes under the canonical constant,
twist and shift comparisons (in particular for a base-change projection).

Source: blueprint `lem-pur-kummer-additivity` (node order 3233); Stacks Tags 03P8,
03PL, 05TE, 010Q, 040E, 03FD and 099W (blueprint: lem-pur-kummer-additivity).

Proof (the Lean proof identifies `Etale.kummerFirstChern` with
`Etale.ordinaryFiniteFirstChern` through the bijective realization
`ordinaryFiniteClass_bijective_arbitraryBase` (def-sp-ordinary-finite-first-chern,
lem-sp-ordinary-finite-class-arbitrary-base), whose proved additivity and pullback
equations carry Steps 1-4; the pro-étale clauses follow by the comparison functor and
its naturality, Step 5):
1. By thm-sc-hilbert-90, `α_T` from line bundles up to isomorphism to `H¹(T_et, G_m)`
   is a group isomorphism with tensor product as source law, so
   `α_T(M ⊗ P) = α_T(M) + α_T(P)`. Since `ℓ ≠ p`, `m` is invertible on `T`;
   lem-amb-kummer-any-base gives the exact Kummer sequence, and its connecting map
   `δ¹_T` is a homomorphism by clause (2) of
   lem-weil-pbc-pullback-cohomology-long-exact-ladder (identity scheme map).
2. Cohomology is additive (def-weil-pbc-sites-and-cohomology), so `H²(φ_T)` is a
   homomorphism; applying both homomorphisms to Step 1 gives additivity of
   `c^et_{1,A}`. No module structure on `G_m` is used.
3. For `f : T' → T`, let `b : f⁻¹G_{m,T} → G_{m,T'}` and its restriction
   `a : f⁻¹μ_{m,T} → μ_{m,T'}` (an isomorphism by lem-asd-etale-finite-twist-pullback).
   `(a, b, b)` maps the inverse-image Kummer sequence (exact by ladder clause (1)) to
   the Kummer sequence on `T'` (exact by lem-amb-kummer-any-base). Ladder clause (3),
   lem-sc-p1-right-derived-triangle-connecting and clause (1) of
   lem-weil-pbc-horseshoe-delta-functor (or lem-weil-pbc-right-derived-universal-delta-functor)
   give `P_μ δ¹_T = δ¹_{T'} P_G`, with `P_G = H¹(b) f^*`, `P_μ = H²(a) f^*`.
4. The tensor comparison `d` of lem-asd-etale-finite-twist-pullback satisfies
   `d ∘ f⁻¹φ_T = φ_{T'} ∘ a` (both send `z` to `a(z) ⊗ 1`). With `P_A = H²(d) f^*`,
   lem-weil-pbc-cohomology-pullback-functorial (3) gives `P_A H²(φ_T) = H²(φ_{T'}) P_μ`,
   and lem-sp-picard-cohomology-arbitrary-pullback gives `P_G α_T(M) = α_{T'}(f^*M)`;
   together with Step 3, `P_A c^et_{1,A}(M) = c^et_{1,A}(f^*M)`.
5. The module and abelian cohomologies agree and commute with pullback
   (lem-weil-pbc-module-sheaves-enough-injectives,
   lem-pe-left-module-derived-evaluation-forget);
   lem-cbc-abelian-etale-proetale-cohomology-comparison moves the class to
   `H²(T_proet, ν_T⁻¹A_T^et(1))`, lem-amb-finite-tate-site-descent identifies the
   coefficient with `A_T(1)` compatibly with pullback, and lem-pur-supported-hom for
   the identity closed immersion (empty complement) identifies it with the arrow
   `A_T → A_T(1)[2]`. These are group isomorphisms, so Step 2 gives additivity of
   arrows; lem-pur-supported-hom-pullback for the identity immersion and Step 4 give
   `f^*c_{1,A}(M) = c_{1,A}(f^*M)`.
6. For a Cartesian square take `f` to be the projection `T ×_S S' → T`: the pulled
   back line bundle is its base change, so no base-change theorem is needed.
-/
theorem kummer_additivity_statement (P : PurityFiniteSetting.{u}) (N : ℕ)
    (hN : 1 ≤ N)
    (hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (∀ M Q : T.Pic,
      Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
          (P.kummerPower_isUnit a N) (M * Q) =
        Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M +
          Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) Q) ∧
    (∀ M Q : T.Pic,
      ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
          (P.kummerPower_isUnit a N) (M * Q) =
        ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M +
          ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) Q) ∧
    (∀ (T' : Scheme.{u}) (a' : T' ⟶ Spec (.of P.field.k))
        (_hs : IsSeparated a') (_hft : LocallyOfFiniteType a')
        (_hqc : QuasiCompact a') (f : T' ⟶ T),
      ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient
          (P.coefficients.l ^ N) hA) (M : T.Pic),
      (Etale.ordinaryFinitePullback P.Coefficient f).map
          (Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M) ≫
        (Etale.ordinaryFiniteShiftedLinePullback P.Coefficient
          (P.coefficients.l ^ N) hA t f (P.kummerPower_isUnit a N)).hom =
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f).hom ≫
        Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T'
          (P.kummerPower_isUnit a' N) (Scheme.Pic.map f M)) ∧
    (∀ (T' : Scheme.{u}) (a' : T' ⟶ Spec (.of P.field.k))
        (_hs : IsSeparated a') (_hft : LocallyOfFiniteType a')
        (_hqc : QuasiCompact a') (f : T' ⟶ T),
      ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient
          (P.coefficients.l ^ N) hA) (M : T.Pic),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.map
          (ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M) ≫
        (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
          (Etale.ordinaryFiniteShiftedLinePullback P.Coefficient
            (P.coefficients.l ^ N) hA t f (P.kummerPower_isUnit a N))).hom =
      (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
        (Etale.ordinaryFiniteUnitPullback P.Coefficient f)).hom ≫
        ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T'
          (P.kummerPower_isUnit a' N) (Scheme.Pic.map f M)) := by
  have _hN := hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M Q
    rw [kummerFirstChern_eq_ordinary, kummerFirstChern_eq_ordinary,
      kummerFirstChern_eq_ordinary]
    exact Etale.ordinaryFiniteFirstChern_mul P.Coefficient (P.coefficients.l ^ N)
      hA T (P.kummerPower_isUnit a N) M Q
  · intro M Q
    let C := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
    have h := Etale.ordinaryFiniteFirstChern_mul P.Coefficient (P.coefficients.l ^ N)
      hA T (P.kummerPower_isUnit a N) M Q
    have h' : C.map (Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
        (P.kummerPower_isUnit a N) (M * Q)) =
        C.map (Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
          (P.kummerPower_isUnit a N) M) +
          C.map (Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) Q) := by
      rw [kummerFirstChern_eq_ordinary, kummerFirstChern_eq_ordinary,
        kummerFirstChern_eq_ordinary]
      simpa only [Functor.map_add] using congrArg C.map h
    simpa [C, ProEtale.kummerFirstChern] using h'
  · intro T' a' hs hft hqc f t M
    exact etale_kummer_pullback P.Coefficient (P.coefficients.l ^ N) hA t f
      (P.kummerPower_isUnit a N) (P.kummerPower_isUnit a' N) M
  · intro T' a' hs hft hqc f t M
    let A := P.Coefficient
    let c := Etale.kummerFirstChern A (P.coefficients.l ^ N) hA T
      (P.kummerPower_isUnit a N) M
    let e := ProEtale.kummerComparisonPullback A f
    let C := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory
    have he := e.hom.naturality c
    have hh := etale_kummer_pullback A (P.coefficients.l ^ N) hA t f
      (P.kummerPower_isUnit a N) (P.kummerPower_isUnit a' N) M
    simp only [Functor.comp_map] at he
    simp only [ProEtale.kummerFirstChern, ProEtale.kummerCoefficientPullback,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, hh, Functor.map_comp]

end WeilConjectures.PurityFiniteSetting

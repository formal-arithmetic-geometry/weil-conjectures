/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsExchange
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
public import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleOpenClosedRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericStratumMate
public import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericImmersionProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.AlgebraicClosure
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing

/-!
# Restriction to a geometric generic fibre

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-verdier-biduality/sk-lem-pd-generic-restriction/_section.md
(blueprint: sk-lem-pd-generic-restriction).

This statement packages the canonical geometric-generic comparisons for direct image,
closed exceptional inverse image, and internal Hom.  In the affine-line case it also
records the Tate-line twist of the dualizing complex and the evaluation-normalized
double-dual comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.longLine false
universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme
open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- Restriction to a geometric generic fibre: for a smooth integral curve `B/k`, the
canonical comparisons `g_X^*Rh_*L ≃ Rh_{η̄,*}g_T^*L`, `g_Z^*i^!M ≃ i_{η̄}^!g_X^*M` and
`g_X^*RHom(K,M) ≃ RHom(g_X^*K, g_X^*M)` are isomorphisms, the last compatible with
evaluation; when `B = A^1_k`, locally on `X`, `g_X^*ω_X ≃ ω_{X_η̄}(1)[2]` and the
internal-Hom comparisons identify `g_X^*δ_K` with `δ_{g_X^*K}` (`affineLineDualityClause`).

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-verdier-biduality/sk-lem-pd-generic-restriction/_section.md,
Lemma sk-lem-pd-generic-restriction, entire statement; standing conventions of sk-def-ops;
Stacks Tag 0F10 (blueprint: sk-lem-pd-generic-restriction).

The formal statement is on the ordinary small étale site with finite coefficients; the
finite pro-étale categories of the node are identified with it by
`sk-prop-ctf-finite-comparison`.  The carrier `[Field k]` is the Lean rendering of the
`sk-def-ops` base field (finite or algebraically closed of characteristic `p ≠ ell`).

Proof (node steps):
1. Finite comparison: by lem-sf-module-object-ordinary-coefficient-equivalence,
   sk-thm-pe-constructible-comparison and sk-cor-pe-finite-tor-comparison choose bounded
   constructible étale origins of `L, K, M` (that of `K` of finite Tor amplitude); the
   pullback and direct-image comparisons are those of sk-prop-ctf-finite-comparison and
   sk-thm-pe-direct-image-comparison, also on the fibre over `η̄`.
2. Exceptional adjunction: transport the étale right adjoint of
   thm-amb-etale-exceptional-adjoint (compactifications by sk-thm-nagata-compactification)
   through the equivalence `ν^*` onto the localizing closure; det-sp-unique-right-adjoint
   identifies it, counits included, with the adjoint of sk-thm-existence(3), and
   det-def-sf-operations restricts it to the exceptional functor of sk-def-ops.
3. Direct image: det-pd-generic-direct-image applied to the étale origin of `L` (étale
   stages, bounded-below limit exchange, inseparable invariance) gives the first iso.
4. Closed support: det-pd-generic-closed-hom(1) applied to `i` and `M` (localization
   triangle `i_*i^!M → M → Rj_*j^*M`) gives the second iso.
5. Internal Hom: det-pd-generic-closed-hom(2) (dévissage to `t_!P`) for finite-Tor `K`;
   lem-sfb-finite-site-internal-hom-comparison, lem-sfb-ringed-derived-monoidal-comparisons
   and lem-sfb-module-object-ringed-site-derived-comparison identify it with the
   evaluation transpose, giving the third iso and the evaluation equation.
6. Twist (`B = A^1_k`): det-pd-generic-dualizing-twist (algebraically closed `k`) or
   lem-weil-geometric-generic-duality (finite `k`) on each affine open, with
   lem-asd-etale-finite-twist-pullback, gives `θ : g_U^*ω_U ≃ ω_{U_η̄} ⊗ A(1)[2]`.
7. Double dual: by sk-lem-pd-preservation `D_U K` and `ω_U` are bounded constructible, so
   step 5 applies twice; with `θ` and the evaluation-normalized cancellation maps `t, s`
   of lem-sf-invertible-factor-hom-cancellation this gives `β`, and uncurrying with the
   symmetry/hexagon identities shows `β ∘ g^*δ_K = δ_{g^*K}`. -/
theorem restrictionToGeometricGenericFibre
    {k : Type u} [Field k] {B : Scheme.{u}} [IsIntegral B]
    (aB : B ⟶ Spec (CommRingCat.of k)) [IsCurve aB] [Smooth aB]
    (Ω : Type u) [Field Ω] [Algebra B.functionField Ω]
    [IsAlgClosure B.functionField Ω]
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (hchar : ringChar k ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    {T X : Scheme.{u}} (t : T ⟶ B) (x : X ⟶ B)
    [LocallyOfFiniteType t] [QuasiCompact t]
    [LocallyOfFiniteType x] [QuasiCompact x]
    (h : T ⟶ X) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (hB : h ≫ x = t)
    {Tη Xη : Scheme.{u}} (gX : Xη ⟶ X)
    (pX : Xη ⟶ Spec (CommRingCat.of Ω))
    (sqX : IsPullback gX pX x
      (Spec.map (CommRingCat.ofHom (algebraMap B.functionField Ω)) ≫
        B.fromSpecStalk (genericPoint B)))
    (gT : Tη ⟶ T) (hη : Tη ⟶ Xη)
    (sq : IsPullback gT hη h gX)
    (L : DerivedCategoryModule A T)
    (hL : DerivedCategory.isBoundedConstructible A T L)
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Zη : Scheme.{u}} (gZ : Zη ⟶ Z) (iη : Zη ⟶ Xη)
    (sqZ : IsPullback gZ iη i gX) [HasCompactification iη] [QuasiCompact iη]
    (M : DerivedCategoryModule A X)
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X M)
    (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app L) ∧
      IsIso ((rightDerivedUpperShriekBaseChangeMap A sqZ).app M) ∧
      IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K M) ∧
      (letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) gX
       (L((gX)^*[ModuleCat.{u + 1} A])).obj K ◁
           derivedHomUpperStarComparison (ModuleCat.{u + 1} A) gX K M ≫
           (ihom.ev ((L((gX)^*[ModuleCat.{u + 1} A])).obj K)).app
             ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) =
         Functor.LaxMonoidal.μ (L((gX)^*[ModuleCat.{u + 1} A])) K
           ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ≫
           (L((gX)^*[ModuleCat.{u + 1} A])).map
             ((ihom.ev K).app M)) ∧
      ∀ (hline : B = AffineSpace (ULift (Fin 1)) (Spec (.of k)))
        [hsep : IsSeparated ((hline ▸ x) ≫
          (AffineSpace (ULift (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)))]
        [hlft : LocallyOfFiniteType ((hline ▸ x) ≫
          (AffineSpace (ULift (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)))]
        [hqc : QuasiCompact ((hline ▸ x) ≫
          (AffineSpace (ULift (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)))],
        affineLineDualityClause k ell n hn hchar A hA (hline ▸ x) := by
  sorry

end AlgebraicGeometry.Etale

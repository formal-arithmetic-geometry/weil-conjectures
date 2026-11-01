/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.FiniteTorsionProperFiniteness
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.SixFunctors.RationalIntegralGenerators
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Ordinary condensed proper finiteness over a Noetherian base

Source: Bhatt--Scholze, Theorem 6.7.1 and Lemma 6.7.2, Proposition 6.8.14 and
Remark 6.8.15; Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9
(blueprint: lem-fd-noetherian-proper-finiteness).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStarFromPoint Mod.extendScalars

private theorem nppf_integral_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E Z))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Z K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E 1
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
    have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    simpa only [Padic.coefficientExtensionIdeal, pow_one, hg] using hm
  let : Field A := Ideal.Quotient.field _
  let : Finite A := Padic.finite_coefficientExtensionRing l E 1 le_rfl
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E 1
  let : CharP A l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr
    (coefficientExtensionRing_one_natCast_self l E)
  have hsource := IntegralModelsStacks.internal_integral_criterion_forward l E Z K hK
  have hfinite := constantModelBoundedConstructible_derivedPushforward_of_isProper_finite_field
    l A p ((AdicCompletion.derivedReduction l E Z 0).obj K) hsource.2.1
  obtain ⟨hχ, hpush⟩ := internal_integral_direct_image_limits l E p
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (AdicCompletion.derivedReduction l E Y 0).obj
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ≅
      (moduleObjectDerivedPushforward (DerivedNakayama.quotientRing l E 1) p).obj
        ((AdicCompletion.derivedReduction l E Z 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  let := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing l E 1) Y).2.1
  exact IntegralModelsStacks.internal_integral_criterion_reverse l E Y _ hcomplete
    ((constantModelBoundedConstructible _ Y).prop_of_iso e.symm hfinite)

private theorem nppf_transport
    {R S : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj S.X] (a : R ≅ S)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (hs : ∀ K, boundedConstructible (condensedRingObj S.X Z) K →
      boundedConstructible (condensedRingObj S.X Y)
        ((moduleObjectDerivedPushforward S.X p).obj K))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R.X Z)))
    (hK : boundedConstructible (condensedRingObj R.X Z) K) :
    boundedConstructible (condensedRingObj R.X Y)
      ((moduleObjectDerivedPushforward R.X p).obj K) := by
  have ht := NormedCoefficientRealization.transport_property a
  obtain ⟨_, _, _, _, _, _, _, hZ, _⟩ := ht.1 Z
  obtain ⟨_, _, _, _, _, _, _, hY, _⟩ := ht.1 Y
  obtain ⟨γ, _⟩ := ht.2 Z Y p
  apply (hY _).mp
  exact (boundedConstructible _).prop_of_iso (γ.symm.app K) (hs _ ((hZ K).mpr hK))

private theorem nppf_integer_ring
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E Z))
    (hK : boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) Z) K) :
    boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) Y)
      ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) := by
  have hc (T : Scheme.{u}) [IsNoetherian T] :
      boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) T) =
        constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T := by
    funext M
    exact propext (and_congr Iff.rfl
      (forall_congr' fun q ↦ integerModel_comparison l E T _))
  rw [hc Z] at hK
  rw [hc Y]
  exact nppf_integral_model l E p K hK

private theorem nppf_integral
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
    [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) Y)
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E) p).obj K) := by
  let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  obtain ⟨e⟩ := integralCoefficientIso.{u} l E
  exact nppf_transport (e.symm ≪≫ integerLatticeIso l (ULift.{u} E)) p
    (nppf_integer_ring l (ULift.{u} E) p) K hK

private theorem nppf_integral_continuous
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) Z)))
    (hK : boundedConstructible (condensedRingObj (integralCoeff l E) Z) K) :
    boundedConstructible (condensedRingObj (integralCoeff l E) Y)
      ((moduleObjectDerivedPushforward (integralCoeff l E) p).obj K) := by
  let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  exact nppf_transport (integerNormedIso l E) p
    (nppf_integer_ring l (ULift.{u} E) p) K hK

private theorem nppf_continuous
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj K) := by
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model l E Z ⟨K, hK⟩
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralScalarMap l E) T)) :=
    integralScalarExtension_exact l E
  have hb := boundedConstructible_leftDerivedExtendScalars_obj
    (condensedRingObj (integralCoeff l E) Y)
    (condensedRingObj (Profinite.continuousMapRingObj E) Y)
    (coefficientMap (integralScalarMap l E) Y) _
    (nppf_integral_continuous l E p M.obj M.property)
  exact (boundedConstructible _).prop_of_iso
    (@asIso _ _ _ _ _ (integralScalarPushHom_isIso l E p M) ≪≫
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).mapIso e) hb

private theorem nppf_algCl
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
      ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) p).obj K) := by
  let P := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
  have heq := (adicConstructibilityPredicateComparison l Y
    (Profinite.padicAlgClRingObj l) .algebraicClosure).2
  obtain ⟨hiso, htri, hret⟩ := (constantModelBoundedConstructible_field_triangulated l Y).2
  let : P.IsClosedUnderIsomorphisms := by dsimp [P]; rw [heq]; exact hiso
  let : P.IsTriangulated := by dsimp [P]; rw [heq]; exact htri
  let : P.IsStableUnderRetracts := by dsimp [P]; rw [heq]; exact hret
  let G := (lowerStar (Profinite.padicAlgClRingObj l) p).rightDerivedFunctor
  let Q := P.inverseImage G
  let : Q.IsStableUnderRetracts := ⟨fun r h ↦ P.prop_of_retract (r.map G) h⟩
  have : Q.IsTriangulated := inferInstance
  have hgen : (WeilConjectures.SixFunctors.qlbarRationalIntegralGenerator l Z) ≤ Q := by
    rintro L ⟨F, M, hM, ⟨e⟩⟩
    let := PadicAlgCl.normedFieldOfAlgebra l F.1
    let : NormedAlgebra ℚ_[l] F.1 := ⟨fun c x ↦ by
      change ‖algebraMap F.1 (PadicAlgCl l) (c • x)‖ ≤
        ‖c‖ * ‖algebraMap F.1 (PadicAlgCl l) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
    let a := padicIntegersRingObjToContinuousMapRingObj l F
    let b := Profinite.padicSubfieldRingObjToPadicAlgCl l F
    let A := Mod.extendScalars (coefficientMap a Z)
    let B := Mod.extendScalars (coefficientMap b Z)
    have : PreservesFiniteLimits A := integralScalarExtension_exact l F.1 Z
    let N := A.leftDerivedFunctor.obj M
    have hN : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj F.1) Z)
        N := boundedConstructible_derivedExtendScalars_obj Z l F ⟨M, hM⟩
    have hPN := nppf_continuous l F.1 p N hN
    obtain ⟨q, hq⟩ := hN.1.1
    let : N.IsGE q := hq
    have hB := boundedConstructible_leftDerivedExtendScalars_obj
      (condensedRingObj (Profinite.continuousMapRingObj F.1) Y)
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
      (coefficientMap b Y) _ hPN
    let ecomp : Mod.extendScalars (coefficientMap a Z ≫ coefficientMap b Z) ≅ A ⋙ B :=
      Mod.extendScalarsComp _ _
    let : PreservesFiniteLimits (Mod.extendScalars
        (coefficientMap a Z ≫ coefficientMap b Z)) :=
      preservesFiniteLimits_of_natIso ecomp.symm
    let : PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a ≫ b) Z)) :=
      preservesFiniteLimits_of_natIso
        (Mod.extendScalarsIsoOfEq (coefficientMap_comp a b Z)).symm
    let ec : (Mod.extendScalars (coefficientMap (a ≫ b) Z)).leftDerivedFunctor ≅
        A.leftDerivedFunctor ⋙ B.leftDerivedFunctor :=
      Functor.leftDerivedFunctorNatIso _
        (Mod.extendScalarsIsoOfEq (coefficientMap_comp a b Z)) ≪≫
      Functor.leftDerivedFunctorNatIso _ (Mod.extendScalarsComp _ _) ≪≫
      A.leftDerivedFunctorCompIso B
    let eL : L ≅ B.leftDerivedFunctor.obj N := e ≪≫ ec.app M
    exact P.prop_of_iso (@asIso _ _ _ _ _
      (isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE l p F N q) ≪≫
      G.mapIso eL.symm) hB
  exact ((ObjectProperty.triangEnvelope_le_iff
    (WeilConjectures.SixFunctors.qlbarRationalIntegralGenerator l Z)).mpr hgen) K
      ((WeilConjectures.SixFunctors.rationalIntegralGenerators l Z ⟨⊥, inferInstance⟩).2 K hK)

/-- Proper pushforward preserves the ordinary bounded constructible category for the three
condensed coefficient rings in the finite-extension and algebraic-closure family. The derived
pushforward is the total derived functor on module objects, and the conclusion imposes no
common field of definition, finite-dimensional base, or geometric base-change hypothesis.

Proof, following the six steps of this node:
1. For integral coefficients, the adic constructibility predicate comparison identifies the
cohomological predicate with the finite constant local model predicate on both Noetherian
schemes. The forward integral criterion gives derived completeness and bounded
constructibility of the first residue reduction. The integral direct-image-limits theorem,
with j = h and quotient index zero (exponent one), gives completeness of the direct image
and its coefficient-change isomorphism. Finite torsion proper finiteness gives bounded
constructibility of the direct image of the residue reduction. The reverse integral
criterion and predicate comparison give the integral conclusion, for every finite E.
The integer-lattice and normed unit-ball presentations of the integral coefficient (with
ULift) are related to this ring by coefficient-ring isomorphisms (the integral-coefficient
comparisons of the noetherian proper constructible cohomology module), and transport along
such isomorphisms preserves bounded constructibility and commutes with derived direct image
by the normed coefficient realization.
2. The integral-to-rational scalar extension preserves finite limits by continuous integral
scalar exactness. Extension from a finite subfield to the specified algebraic closure does
so by qlbar-flat. The exact scalar-extension theorem therefore gives preservation of
bounded constructibility for both scalar extensions.
3. Properness implies quasi-compactness by finite type and quasi-separatedness by
separatedness. The continuous integral push comparison identifies the pushforward of an
integral generator extended to E with the scalar extension of its integral pushforward.
Steps 1 and 2 make this bounded constructible. Every bounded constructible E-complex
has an integral model by continuousConstructible_integral_model, so this proves the
finite-extension case directly.
4. The coefficient map respects composition. Underived scalar-extension associativity
and the comparison between the left derived functor of a composite of exact functors
and the composite of their left derived functors identify extension along
O_F -> F -> Qlbar with the two successive derived extensions.
5. For a Qlbar integral generator, step 2 makes its intermediate F-extension bounded
constructible, hence lower bounded. The bounded finite-stage Qlbar push comparison for
the proper map h applies. Step 4 identifies the input; steps 3 and 2 make its image
bounded constructible.
6. The algebraic-closure part of rational-integral-generators reduces that case to generators.
The total right derived pushforward is triangulated, additive and preserves retract
diagrams. On Noetherian Y the predicate comparison identifies the target cohomological
category with the finite constant model category, which is thick by the coefficient-heart
triangulated theorem. Thus the class of inputs with bounded constructible image is closed
under isomorphisms, finite sums, shifts, cones and retracts. Steps 3 and 5 put all generators
in that class, proving the algebraic-closure case and completing all three cases.
These are the arguments of Bhatt--Scholze 6.7.1, 6.7.2 and 6.8.14, with
Hemo--Richarz--Scholbach 7.7 and 7.9 for the finite-subextension coefficient.
(blueprint: lem-fd-noetherian-proper-finiteness).
-/
theorem proper_pushforward_mem_boundedConstructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (Profinite.padicIntegersRingObj ℓ E) ∨
      Λ = Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (Profinite.padicSubfieldCondensedRing ℓ E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (h : Z ⟶ Y) [IsProper h] :
    ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj Λ.X Z)),
      boundedConstructible (condensedRingObj Λ.X Z) K →
        boundedConstructible (condensedRingObj Λ.X Y)
          ((moduleObjectDerivedPushforward Λ.X h).obj K) := by
  rcases hΛ with rfl | rfl | rfl
  · exact nppf_integral ℓ E h
  · let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E := ⟨fun c x ↦ by
      change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
        ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
    exact nppf_continuous ℓ E h
  · exact nppf_algCl ℓ h

end AlgebraicGeometry.ProEtale.CondensedRing

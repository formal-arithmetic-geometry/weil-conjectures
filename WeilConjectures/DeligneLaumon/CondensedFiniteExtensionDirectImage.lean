/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel

import all WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSerreIndConstructible
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Ambient condensed finite-extension direct-image finiteness

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15,
last paragraph; Definition 6.8.8, Proposition 6.8.11(3), Lemma 6.7.2 and
Theorem 6.7.1 (blueprint: lem-per-condensed-finite-extension-direct-image).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option synthInstance.maxSize 4096

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

/-- The uniformizer generates the maximal ideal of the continuous integer DVR. -/
private theorem residueIdeal_maximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hg] using hm

/-- The prime has norm less than one and therefore vanishes in the first residue field. -/
private theorem residue_killed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : Padic.coefficientExtensionRing l E 1) ^ 1 = 0 := by
  rw [pow_one]
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change _ ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
  simpa only [pow_one, hg] using hlm

section FiniteTypeIntegral

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] (hℓ : IsUnit (ℓ : k))
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

private instance ambient_source_noetherian : IsNoetherian X.left :=
  isNoetherian_of_locallyOfFiniteType X.hom
private instance ambient_target_noetherian : IsNoetherian Y.left :=
  isNoetherian_of_locallyOfFiniteType Y.hom

include ℓ k hℓ


set_option linter.unusedSectionVars false in
/-- Finite-coefficient finiteness over any field with the coefficient prime invertible. -/
private theorem ambient_finite_etale (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : Etale.DerivedCategoryModule A X.left)
    (hK : Etale.DerivedCategory.isBoundedConstructible A X.left K) :
    Etale.DerivedCategory.isBoundedConstructible A Y.left
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K) := by
  have hA : Etale.IsSmoothBaseChangeCoefficients (ℓ ^ n) A (Spec (.of k)) := by
    refine ⟨pow_pos (Fact.out : ℓ.Prime).pos n, inferInstance, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hn
    · simpa only [map_natCast, map_pow, Nat.cast_pow] using
        (hℓ.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k A (ℓ ^ n) hA X.hom Y.hom f.left (Over.w f) K hK


/-- Transfer finite etale finiteness through the bounded-below pro-etale comparison. -/
private theorem ambient_finite_fixed (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A X.left K) :
    FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y.left
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor.obj
        K) := by
  let B := ULift.{u + 1} A
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin X.left B K
    (fun q ↦ (FiniteDiscreteOrdinary.ordinary_constructible_iff A X.left _).mp (hK.2 q)) a b (by
      intro q hq
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
      · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  have hnB : (ℓ : B) ^ n = 0 := ULift.ext _ _ hn
  have hFJ := ambient_finite_etale ℓ hℓ f B n hnB J hJ
  obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
  have : J.IsGE aJ := (DerivedCategory.isGE_iff J aJ).2 fun q hq ↦ hvJ q (Or.inl hq)
  have := ProEtale.unboundedDirectImageComparison_boundedBelow B f.left J aJ
  let νY := ProEtale.comparisonUpperStar (ModuleCat B) Y.left
  let F := Etale.lowerStar (ModuleCat B) f.left
  let G := ProEtale.lowerStar (ModuleCat B) f.left
  let e : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
      G.rightDerivedFunctor.obj K :=
    asIso (ProEtale.unboundedDirectImageComparisonMap B f.left J) ≪≫
      G.rightDerivedFunctor.mapIso eJ
  obtain ⟨c, d, _, hv⟩ := hFJ.2
  have hge : (F.rightDerivedFunctor.obj J).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have hle : (F.rightDerivedFunctor.obj J).IsLE d :=
    (DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hv q (Or.inr hq)
  have := νY.isGE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) c
  have := νY.isLE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) d
  refine ⟨⟨⟨c, DerivedCategory.TStructure.t.isGE_of_iso e c⟩,
    ⟨d, DerivedCategory.TStructure.t.isLE_of_iso e d⟩⟩, ?_⟩
  intro q
  apply (FiniteDiscreteOrdinary.ordinary_constructible_iff A Y.left _).mpr
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
  exact ProEtale.isConstructible_of_iso
    ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e)
    (ProEtale.isConstructible_comparisonUpperStar_obj _)

/-- Transfer finite-coefficient finiteness through the internal-module encoding. -/
private theorem ambient_finite_internal (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X.left))
    (hK : constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X.left K) :
    constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) Y.left
      (R((f.left)_*⟦FiniteDiscreteOrdinary.coefficient A⟧).obj K) := by
  classical
  let eX := (FiniteDiscreteOrdinary.encoding_exists A X.left).some
  let eY := (FiniteDiscreteOrdinary.encoding_exists A Y.left).some
  let e := (FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A f.left eY eX).app K
  have hsource := (FiniteDiscreteOrdinary.encoding_constructibility A X.left eX).2 K
  have himage := ambient_finite_fixed ℓ hℓ f A n hn _ (hsource.mp hK)
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y.left
      (eY.fixedDerived.functor.obj
        (R((f.left)_*⟦FiniteDiscreteOrdinary.coefficient A⟧).obj K)) := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm himage.1, ?_⟩
    intro q
    exact (FiniteDiscreteOrdinary.constructible_iso A Y.left
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)).mp (himage.2 q)
  exact (FiniteDiscreteOrdinary.encoding_constructibility A Y.left eY).2 _ |>.mpr hb

/-- Completeness and constructibility of the first residue detect integral finiteness. -/
private theorem ambient_finite_integralModel
    (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (f : X ⟶ Y)
    (K : DerivedCategory (ProEtale.AdicCompletion.Modules ℓ E X.left))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) X.left K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) Y.left
      (R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let A := Padic.coefficientExtensionRing ℓ E 1
  let : (Padic.coefficientExtensionIdeal ℓ E 1).IsMaximal := residueIdeal_maximal ℓ E
  let : Field A := Ideal.Quotient.field _
  let : Finite A := Padic.finite_coefficientExtensionRing ℓ E 1 le_rfl
  let : DiscreteTopology A := ProEtale.DerivedNakayama.quotientDiscrete ℓ E 1
  have hsource := IntegralModelsStacks.internal_integral_criterion_forward ℓ E X.left K hK
  have hkilled : (ℓ : A) ^ 1 = 0 := residue_killed ℓ E
  have hfiniteBC := ambient_finite_internal ℓ hℓ f A 1 hkilled
    ((ProEtale.AdicCompletion.derivedReduction ℓ E X.left 0).obj K) hsource.2.1
  have hlimits := ProEtale.internal_integral_direct_image_limits ℓ E f.left
  have hχ := hlimits.choose
  have hpush := hlimits.choose_spec
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (ProEtale.AdicCompletion.derivedReduction ℓ E Y.left 0).obj
      (R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj K) ≅
      R((f.left)_*⟦ProEtale.DerivedNakayama.quotientRing ℓ E 1⟧).obj
        ((ProEtale.AdicCompletion.derivedReduction ℓ E X.left 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  have hc := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing ℓ E 1) Y.left).2.1
  let := hc
  exact IntegralModelsStacks.internal_integral_criterion_reverse ℓ E Y.left _ hcomplete
    ((ProEtale.constantModelBoundedConstructible _ Y.left).prop_of_iso e.symm hfiniteBC)

/-- Transport boundedness and constructibility through the exact coefficient equivalence. -/
private theorem ambient_finite_integral_of_iso
    (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (ProEtale.DerivedNakayama.integerRing ℓ E))
    (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left)
      (R((f.left)_*⟦Λ⟧).obj K) := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F (X : Scheme.{u}) : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (ProEtale.DerivedNakayama.integerRing ℓ E) X) :=
    Mod.comap (coefficientMap φ X)
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  have hFK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) X.left ((F X.left).mapDerivedCategory.obj K) := by
    constructor
    · exact (F X.left).bounded_mapDerivedCategory_obj hK.1
    intro q
    apply (integerModel_comparison ℓ E X.left _).mp
    exact _root_.constructible_of_iso
      (((F X.left).mapDerivedCategoryHomologyFunctorIso q).app K)
      (_root_.constructible_comap (coefficientMap φ X.left) (hK.2 q))
  have hP := ambient_finite_integralModel ℓ hℓ E f _ hFK
  let hi : (F Y.left).mapDerivedCategory.obj (R((f.left)_*⟦Λ⟧).obj K) ≅
      R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj
        ((F X.left).mapDerivedCategory.obj K) := (derivedComapLowerStarIso φ f.left).app K
  refine ⟨(F Y.left).bounded_of_bounded_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.bounded).prop_of_iso hi.symm hP.1), ?_⟩
  intro q
  have hH := (integerModel_comparison ℓ E Y.left _).mpr (hP.2 q)
  have hF : IsConstructibleModuleObject
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing ℓ E) Y.left)
      ((F Y.left).obj ((DerivedCategory.homologyFunctor _ q).obj (R((f.left)_*⟦Λ⟧).obj K))) :=
    _root_.constructible_of_iso
      (((DerivedCategory.homologyFunctor _ q).mapIso hi).symm ≪≫
        ((F Y.left).mapDerivedCategoryHomologyFunctorIso q).symm.app _) hH
  let ψ := coefficientMap φ Y.left
  exact _root_.constructible_of_iso
    (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app _)
    (_root_.constructible_comap (inv ψ) hF)


end FiniteTypeIntegral


/-- For a finite `E/ℚ_ℓ` and a separated finite-type morphism over a field where `ℓ` is
invertible, the total ambient module-object direct image preserves bounded constructibility.
The bounded constructibility predicate is the finite constant local-model predicate of
`sk-def-sfb-constructible`, and the direct image is the total derived functor computed on
K-injectives. Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.7.2
(blueprint: lem-per-condensed-finite-extension-direct-image).

Proof plan:
1. A field is Noetherian. By `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-kun-dimension-finite-type`, both schemes are Noetherian of finite dimension.
   The closed-subset minimality and compact-open results
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` and
   `lem-sfb-noetherian-space-compact-subsets` imply that `f` is qcqs. The inverse of
   `ℓ` in `k` maps to its inverse in every stalk.
2. `lem-weil-pbc-continuous-coefficient-realizations` identifies the pulled-back
   continuous coefficients with their section rings. The exact equivalence of
   `lem-sfb-internal-module-operations-transport` identifies direct images and preserves
   K-injectives: Hom from an acyclic complex is transported through its exact inverse.
   A basis identifies a finite-dimensional constant model with a finite free model.
3. Use `lem-sfb-adic-constructibility-predicate-comparison` and
   `lem-weil-pbc-continuous-constructible-integral-model` to choose an actual bounded
   constructible integral lattice `M` over `A = 𝒪_E`, whose scalar extension is `K`.
   For a uniformizer `π`, put `B = A/π`. The forward direction
   `lem-sfb-internal-integral-criterion-forward` makes `M` complete and its first
   derived reduction bounded constructible.
4. Set `H = Rf_* M` in the ordinary ambient integral category. By
   `lem-sfb-integral-quotient-resolution-normalization`, the complexes
   `[A --π^n→ A]` resolve the quotients compatibly with transitions and augmentation.
   The comparison `lem-sfb-strict-completion-restriction-comparison` and the Koszul
   reflector `lem-weil-pbc-ringed-koszul-completion-reflector` identify their completion
   unit with local derived completeness. Apply
   `lem-weil-pbc-ringed-pushforward-completion` to the principal ideal `(π)` to deduce
   completeness of `H`, without assuming boundedness of `H`.
5. `lem-sfb-integral-quotient-direct-image-comparison` identifies the first reduction
   of `H` with the direct image of the first reduction of `M`. Use
   `lem-sf-module-object-ordinary-coefficient-equivalence` and
   `lem-sf-finite-discrete-encoding-constructibility` to apply
   `lem-sf-finite-proetale-pushforward-constructible` with the finite coefficient ring
   `B`. This gives bounded constructibility of that first reduction over any such `k`.
6. Apply `lem-sfb-internal-integral-criterion-reverse` on `Y`, using completeness and
   the first reduction, to conclude that `H` is bounded constructible over `A`.
7. By `lem-weil-pbc-continuous-integral-scalar-exact`, actual extension from `A` to
   `E` is exact. It preserves the cohomological bounds and, by
   `lem-sfb-internal-scalar-pullback-normalization`, the constant models on strata.
   The scalar extension of a finitely presented `A`-module is a finite-dimensional
   `E`-space, so the scalar extension of `H` has the required constant models.
8. `lem-sfb-localized-direct-image-comparison` applies to the qcqs map and bounded
   lattice `M`. It identifies the scalar extension of `H` with the actual ambient
   direct image of `K`. Transfer bounded constructibility across this isomorphism.
-/
theorem finiteExtension_directImage_preserves_constantModelBoundedConstructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hℓ : IsUnit (ℓ : k))
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hK : constantModelBoundedConstructible
      (Profinite.continuousMapRingObj E) X K) :
    constantModelBoundedConstructible
      (Profinite.continuousMapRingObj E) Y
      ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) f).obj K) := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let V : Over (Spec (.of k)) := Over.mk aX
  let W : Over (Spec (.of k)) := Over.mk aY
  let g : V ⟶ W := Over.homMk f hf
  have : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType aX)
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact aX)
  have : IsSeparated V.hom := inferInstanceAs (IsSeparated aX)
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType aY)
  have : QuasiCompact W.hom := inferInstanceAs (QuasiCompact aY)
  have : IsSeparated W.hom := inferInstanceAs (IsSeparated aY)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType aX
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have hX := (adicConstructibilityPredicateComparison ℓ X
    (Profinite.continuousMapRingObj E.1) (.continuous E.1)).2
  have hY := (adicConstructibilityPredicateComparison ℓ Y
    (Profinite.continuousMapRingObj E.1) (.continuous E.1)).2
  have hK' : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X) K := by
    rw [hX]
    exact hK
  have hint : ∀ M : integralConstructible ℓ E.1 X,
      boundedConstructible (condensedRingObj (integralCoeff ℓ E.1) Y)
        (R((f)_*⟦integralCoeff ℓ E.1⟧).obj M.obj) := by
    intro M
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
    exact ambient_finite_integral_of_iso ℓ hℓ (ULift.{u} E.1) _
      (integerNormedIso ℓ E.1) g M.obj M.property
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E.1) X)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E.1) X)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E.1) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E.1) Y)) := inferInstance
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E.1 X ⟨K, hK'⟩
  have := integralScalarPushHom_isIso ℓ E.1 f M
  let φ := coefficientMap (integralScalarMap ℓ E.1) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((f)_*⟦integralCoeff ℓ E.1⟧).obj M.obj) ≅
      R((f)_*⟦Profinite.continuousMapRingObj E.1⟧).obj K :=
    asIso ((derivedPushHom (integralScalarMap ℓ E.1) f).app M.obj) ≪≫
      (R((f)_*⟦Profinite.continuousMapRingObj E.1⟧)).mapIso e
  have hs := boundedConstructible_leftDerivedExtendScalars_obj _ _ φ _ (hint M)
  rw [← hY]
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e' hs.1,
    fun q ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e') (hs.2 q)⟩

end AlgebraicGeometry.ProEtale.CondensedRing

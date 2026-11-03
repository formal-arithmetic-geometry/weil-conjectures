/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleHeart
import WeilConjectures.AlgebraicGeometry.StrictCoefficientTensor.StrictCoefficientTensorDescent
import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.StratifiedTorIntervalDevissage
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionLevelConstructible
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerAdjunct
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison

/-!
# Normalized reduction towers in the integral-heart setting

Source: blueprint latest, part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/
sec-coefficients/sk-prop-sp-integral-towers/`sk-prop-sp-integral-towers-reduction.md`
and its proof, Construction, Normalization, and Constructibility
(blueprint: det-sp-reduction-tower-normalized).

The source of `red` is the ordinary unbounded derived category of modules over the
pulled-back condensed valuation ring. Its comparison with the existing strict
construction is through the exact internal/section-module equivalence. Construction
and normalization have no geometric hypotheses. Constructibility uses precisely the
separated finite-type field setting of `sk-lem-int-integral-heart`. The current
Q42 statement and its proof apply over every field with `l` invertible; the former
finite-or-algebraically-closed restriction is not part of this setting.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- The general instances have an unconstrained coefficient-size parameter.
-- Use the existing fixed-size pro-etale instances for this declaration only.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in

private theorem heartCoefficientIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ e : integralHeartCoefficientRingObj l E ≅ spIntegralCondensed l E,
      IsMonHom e.hom := by
  let : Small.{0} E := Module.Finite.small (Padic l) E
  let F := Shrink.{0} E
  let : FiniteDimensional (Padic l) F :=
    (Shrink.algEquiv (Padic l) E).symm.toLinearEquiv.finiteDimensional
  let := spectralNorm.normedField (Padic l) F
  let := spectralNorm.normedField (Padic l) E
  let e : F ≃ₐ[Padic l] E := Shrink.algEquiv (Padic l) E
  have hn (x : F) : spectralNorm (Padic l) F x =
      spectralNorm (Padic l) E (e x) := by
    simp only [spectralNorm, minpoly.algEquiv_eq]
  have hm (x : F) : x ∈ Padic.coefficientExtensionIntegers l F ↔
      e x ∈ Padic.coefficientExtensionIntegers l E := by
    have hF := (Padic.extension_integers_dvr l F
      (Padic.coefficientExtensionAbsoluteValue l F)
      (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec.1 x
    have hE := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec.1 (e x)
    have hh : Padic.coefficientExtensionAbsoluteValue l F x =
        Padic.coefficientExtensionAbsoluteValue l E (e x) := hn x
    exact hF.trans ((congrArg (fun t : ℝ ↦ t ≤ 1) hh).to_iff.trans hE.symm)
  let t : Padic.coefficientExtensionIntegers l F ≃+*
      Padic.coefficientExtensionIntegers l E :=
    { toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, (hm _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    change spectralNorm (Padic l) E (e x.val - e y.val) =
      spectralNorm (Padic l) F (x.val - y.val)
    rw [← map_sub, hn]
  have hti : Continuous t.symm := (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  let q : Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers l F) ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) :=
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.toRingHom.compLeftContinuous _ ht.continuous).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.symm.toRingHom.compLeftContinuous _ hti).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.symm_apply_apply (x.down z)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.apply_symm_apply (x.down z) }
  let G := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have hq : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  exact ⟨G.mapIso q, hq⟩

private theorem tor_of_heart_strata
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) [IsNoetherian T]
    (C : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (S : T.FiniteLocallyClosedStratification) (a b : ℤ)
    (hS : ∀ j : Fin S.n, DerivedCategory.torAmplitudeIn _ a b
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (S.immersion j)).obj C))) :
    DerivedCategory.torAmplitudeIn _ a b ((DerivedCategory.singleFunctor _ 0).obj C) := by
  intro N
  let K := (DerivedCategory.singleFunctor _ 0).obj C
  let L := K ⊗ (DerivedCategory.singleFunctor _ 0).obj N
  have hv (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    apply coefficientModuleZero Λ S
    intro j
    let F := CondensedRing.upperStar Λ (S.immersion j)
    have ht : DerivedCategory.torAmplitudeIn _ a b (F.mapDerivedCategory.obj K) :=
      (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
        ((F.mapDerivedCategorySingleFunctor 0).app C).symm (hS j)
    have h := concentration_of_pullback_tor F (pullbackTensorIso Λ (S.immersion j))
      a b K ht N
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (F.mapDerivedCategory.obj L)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ a).mp h.1 q hq
      · exact (DerivedCategory.isLE_iff _ b).mp h.2 q hq
    exact hz.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app L)
  exact ⟨(DerivedCategory.isGE_iff L a).mpr (fun q hq ↦ hv q (.inl hq)),
    (DerivedCategory.isLE_iff L b).mpr (fun q hq ↦ hv q (.inr hq))⟩

private theorem finiteTor_of_heart_stratum_bounds
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) [IsNoetherian T]
    (hstrata : ∀ C : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T), IsConstantModelConstructible Λ T C →
      ∃ S : T.FiniteLocallyClosedStratification, ∀ j : Fin S.n,
        DerivedCategory.torAmplitudeIn _ (-1) 0
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Λ (S.immersion j)).obj C)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (hM : constantModelBoundedConstructible Λ T M) :
    DerivedCategory.finiteTorAmplitude _ M := by
  let Q := DerivedCategory.finiteTorAmplitude
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
  let : Q.IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ T).2.2.2.2.2.2.2.1
  let P := ObjectProperty.isoClosure (IsConstantModelConstructible Λ T)
  have hsingle (C : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) (hC : P C) : Q ((DerivedCategory.singleFunctor _ 0).obj C) := by
    obtain ⟨C', hC', ⟨e⟩⟩ := hC
    obtain ⟨S, hS⟩ := hstrata C' hC'
    refine Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm ?_
    exact ⟨-1, 0, tor_of_heart_strata Λ T C' S (-1) 0 hS⟩
  exact DerivedCategory.prop_of_bounded Q P hsingle M hM.1
    (fun q ↦ ⟨_, hM.2 q, ⟨Iso.refl _⟩⟩)

private theorem finiteTor_of_integral_heart
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hell : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integralHeartCoefficientRingObj l E) T)))
    (hM : constantModelBoundedConstructible (integralHeartCoefficientRingObj l E) T M) :
    DerivedCategory.finiteTorAmplitude _ M := by
  let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of k))
  apply finiteTor_of_heart_stratum_bounds (integralHeartCoefficientRingObj l E) T ?_ M hM
  intro C hC
  obtain ⟨S, _, hS⟩ :=
    (integralConstructibleHeart k l hell E T).2.2.2.2.2.2.2.2.2.2.2 C hC
  exact ⟨S, fun j ↦ (hS j).2.1⟩

private theorem reduction_preserves_tor_interval
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (spIntegralCondensed l E) T)))
    (a b : ℤ) (hab : a ≤ b)
    (htor : DerivedCategory.torAmplitudeIn _ a b M) (n : ℕ) :
    let F := spIntegralModuleEquivalence l E T
    let _ : F.functor.Additive := Functor.additive_of_preserves_binary_products _
    Scheme.HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((spDerivedCoefficientEvaluation l E T D n).obj
        (red.obj (F.functor.mapDerivedCategory.obj M))) a b := by
  let R := condensedRingObj (spIntegralCondensed l E) T
  let F := spIntegralModuleEquivalence l E T
  have : F.functor.Additive :=
    InternalAbelianSheafModule.comparison_additive (Scheme.ProEt.topology T) R
  have : F.inverse.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨P, hge, hle, hP, ⟨eP⟩⟩ :=
    (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat.{u + 1, u + 1, u + 2} a b
      M).mp htor
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflat, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology T) R
  let Q := (F.functor.mapHomologicalComplex (.up ℤ)).obj P
  have hQ : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) (Q.X i) := by
    intro i
    exact (hflat (P.X i)).mp (hP i).2
  have : CochainComplex.IsStrictlyLE Q b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ _ b).mpr hle
  have hkQ := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (spIntegralSectionRing l E T) Q b hQ
  let eQ : DerivedCategory.Q.obj Q ≅ F.functor.mapDerivedCategory.obj M :=
    (F.functor.mapDerivedCategoryFactors.app P).symm ≪≫
      F.functor.mapDerivedCategory.mapIso eP
  let φ := spIntegralReductionScalar l E T coefficient n
  let S := (D.scalar φ).model
  have hext := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ Q S.E S.obj_eq (fun g ↦ S.map_eq g) hkQ
      (fun i ↦ (SheafOfModules.flat_to_cat (spIntegralSectionRing l E T) (Q.X i) (hQ i)).2)
  let V := (S.E.mapHomologicalComplex (.up ℤ)).obj Q
  have hV : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T)
      (R := Scheme.proEtaleConstantRing T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))
      (V.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (V.X i)).symm (hext.2 i)
  have hbounds (i : ℤ) (hi : i < a ∨ b < i) : IsZero (V.X i) := by
    apply S.E.map_isZero
    apply F.functor.map_isZero
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  have : IsIso (S.ε.app Q) := S.computes Q hkQ
  let eV : (spDerivedCoefficientEvaluation l E T D n).obj
      (red.obj (F.functor.mapDerivedCategory.obj M)) ≅ DerivedCategory.Q.obj V :=
    (evaluation n).app (F.functor.mapDerivedCategory.obj M) ≪≫
      S.T.mapIso eQ.symm ≪≫ asIso (S.ε.app Q)
  exact (scalarExtension_tor_flat_model T _ _ a b hab).mpr ⟨V, hV, hbounds, ⟨eV⟩⟩

-- The general instances have an unconstrained coefficient-size parameter.
-- Use the existing fixed-size pro-etale instances for this declaration only.

/-- Derived reductions form a functorial normalized strict coefficient tower for every
scheme. In the integral-heart setting, bounded constructible integral complexes give
normalized constructible finite-Tor towers, retaining every Tor interval.

Source: blueprint latest, part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/
sec-coefficients/sk-prop-sp-integral-towers/`sk-prop-sp-integral-towers-reduction.md`
and its proof, all three paragraphs; part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/`sk-lem-int-integral-heart`, standing field and finite-type setting
(blueprint: det-sp-reduction-tower-normalized).

Proof:
1. Choose a flat-term K-flat representative P over the pulled-back condensed integral
ring. Strict coefficient-tensor descent (lem-sp-strict-coefficient-tensor-descent)
forms the complex of towers with levels P tensor R_n and quotient-induced transitions.
It preserves quasi-isomorphisms between these representatives, and hence descends
independently of representatives to a functor on ordinary derived categories. Exact
evaluation (det-sp-coefficient-towers-abelian) gives M tensor^L R_n. The exact
internal/section-module equivalence identifies this construction with r.red.
2. Successive derived scalar extension
(lem-sfb-successive-derived-quotient-normalization) is the associativity isomorphism
(x tensor c) tensor d mapped to x tensor c-bar d, with inverse x tensor d mapped to
(x tensor 1) tensor d. Its quotient-transition normalization identifies it with the
specified reduction map, including the identity case m = n. Thus every M is normalized.
3. Now assume the integral-heart field and geometric hypotheses, over any field
with l invertible (Q42 general-field audit of sk-lem-int-integral-heart). By
sk-lem-int-integral-heart and finite truncation triangles
(lem-weil-pbc-truncation-triangle), M is a finite extension of shifted stratum sheaves
a_!C. Exact open/closed sequences (det-sf-open-closed-sequence-ring-sheaf) and the finite
stratified scalar models give these pieces with stratum Tor amplitude [-1,0]. A
length-one finite free DVR resolution reduces to finite free quotient modules, whose
cohomology is constructible. Open and closed immersion tensor projection
(lem-sfb-open-immersion-derived-tensor-projection and
lem-sfb-closed-immersion-derived-tensor-projection) identifies the reductions of a_!C
with a_! of its reductions. Extension by zero and the constructible Serre property
(lem-weil-constructible-coefficient-serre) preserve constructibility. Derived coefficient
change (lem-pur-derived-change-of-rings) preserves the finite extension and shift steps;
their number and shifts are independent of n.
4. The same projection formulas give the Tor bounds of the shifted stratum pieces;
finite shifts and extensions give finite Tor amplitude for M
(det-def-sfb-constructible-tor-amplitude). For every Tor interval [a,b] of M, balanced
derived tensor/restriction (lem-trf-site-derived-tensor-restriction) identifies tensor
of its nth reduction with a quotient-module N with M tensor Res N. This transfers the
same interval to every level. Testing with the quotient ring bounds cohomology in the
same interval. Combined with constructibility and normalization, these uniform bounds
are precisely sk-def-sp-normalized-towers.
-/
theorem sp_reduction_tower_integral_heart_statement
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    ∃ r : SpReductionTowerConstruction l E T D,
      ∃ red : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (spIntegralCondensed l E) T)) ⥤
          spDerivedCoefficientTowers l E T D,
        Nonempty (spIntegralInternalization l E T ⋙ red ≅ r.red) ∧
        (∀ M, IsSpNormalizedTower l E T D (red.obj M)) ∧
        (∀ (k : Type u) [Field k], IsUnit (l : k) →
          ∀ [T.Over (Spec (.of k))]
            [IsSeparated (T ↘ Spec (.of k))]
            [LocallyOfFiniteType (T ↘ Spec (.of k))]
            [QuasiCompact (T ↘ Spec (.of k))],
            ∀ M, constantModelBoundedConstructible (spIntegralCondensed l E) T M →
              DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
                (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                  (condensedRingObj (spIntegralCondensed l E) T)) M ∧
              spNormalizedConstructibleTorTowers l E T D (red.obj M) ∧
              ∀ (a b : ℤ), a ≤ b →
                DerivedCategory.torAmplitudeIn.{u + 1, u + 1, u + 2}
                  (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                    (condensedRingObj (spIntegralCondensed l E) T)) a b M →
                ∀ n : ℕ,
                  Scheme.HasProEtaleTorAmplitude T
                    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
                    ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
                  ∀ i : ℤ, (i < a ∨ b < i) → IsZero
                    ((@DerivedCategory.homologyFunctor
                      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                        (Padic.coefficientExtensionIntegers l E ⧸
                          spEllIdeal l E ^ (n + 1))))
                      _ _ (HasDerivedCategory.standard _) i).obj
                      ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)))) := by
  classical
  have hlimit :=
    (sfb_integral_coefficient_limit l E T).choose_spec.choose_spec.choose_spec.2.2.2.2.2
  have hmon : IsMonHom (spIntegralAbComparison l E T).hom := hlimit.choose_spec.1.1
  obtain ⟨coefficient, hcomparison, _⟩ := liftSectionRingIso (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (spIntegralAbComparison l E T)
  have hcoefficient : ∀ (U : T.ProEtᵒᵖ)
      (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
      coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x := by
    intro U x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) hcomparison) U) x
  obtain ⟨ordinary, hadditive, level, transition, rred, counit, universal,
      computes, evaluation, -⟩ :=
    sp_reduction_tower_presentation_descent l E T D coefficient
  let := hadditive
  let r : SpReductionTowerConstruction l E T D := {
    coefficient := coefficient
    coefficient_normalized := hcoefficient
    ordinary := ordinary
    level := level
    transition := transition
    red := rred
    counit := counit
    universal := universal
    computes := computes
    evaluation := evaluation }
  have hnorm := sp_reduction_tower_adjunct_normalization l E T D coefficient
    ordinary level transition rred counit universal computes evaluation
  let F := spIntegralModuleEquivalence l E T
  let : F.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : F.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let red := F.functor.mapDerivedCategory ⋙ rred
  refine ⟨r, red, ⟨?center⟩, (fun M ↦ hnorm _), ?bounds⟩
  case center =>
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategory.counitIso rred ≪≫ Functor.leftUnitor _
  case bounds =>
    intro k hk hell hOver hSep hFt hQc M hM
    let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of k))
    obtain ⟨e, he⟩ := heartCoefficientIso l E
    let := he
    let G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (spIntegralCondensed l E) T) ⥤
        Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integralHeartCoefficientRingObj l E) T) :=
      Mod.comap (coefficientMap e.hom T)
    have hGM : constantModelBoundedConstructible (integralHeartCoefficientRingObj l E) T
        (G.mapDerivedCategory.obj M) := by
      refine ⟨G.bounded_mapDerivedCategory_obj hM.1, ?_⟩
      intro q
      have hq := constructible_comap e.hom T _ (hM.2 q)
      exact constructible_iso
        ((G.mapDerivedCategoryHomologyFunctorIso q).app M) hq
    obtain ⟨a, b, htor⟩ := finiteTor_of_integral_heart k l hell E T _ hGM
    have hfinite : DerivedCategory.finiteTorAmplitude _ M := by
      let : G.IsEquivalence :=
        (Mod.comapEquivalenceOfIsIso (coefficientMap e.hom T)).isEquivalence_functor
      let : G.PreservesFlat := Functor.preservesFlat_of_isEquivalence G
      exact ⟨a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff G a b M).mp
        htor⟩
    let M' := F.functor.mapDerivedCategory.obj M
    let eM : (spIntegralInternalization l E T).obj M' ≅ M :=
      F.mapDerivedCategory.unitIso.symm.app M
    let := (constantModelConstructibleFiniteTor_wellDefined
      (spIntegralCondensed l E) T).2.1
    have hM' : constantModelBoundedConstructible (spIntegralCondensed l E) T
        ((spIntegralInternalization l E T).obj M') :=
      (constantModelBoundedConstructible (spIntegralCondensed l E) T).prop_of_iso eM.symm hM
    have hconstructible := sp_reduction_tower_level_constructibility l E T D
      coefficient hcoefficient rred evaluation M' hM'
    have hinterval (a b : ℤ) (hab : a ≤ b) (htor : DerivedCategory.torAmplitudeIn _ a b M)
        (n : ℕ) :
        Scheme.HasProEtaleTorAmplitude T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
          ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
        ∀ i : ℤ, (i < a ∨ b < i) → IsZero
          ((@DerivedCategory.homologyFunctor
            (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
              (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
            _ _ (HasDerivedCategory.standard _) i).obj
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by
      have ht := reduction_preserves_tor_interval l E T D
        coefficient rred evaluation M a b hab htor n
      refine ⟨ht, ?_⟩
      intro i hi
      obtain ⟨P, _, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T _ _ a b hab).mp ht
      exact ((P.sc i).isZero_homology_of_isZero_X₂ (hb i hi)).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
          (DerivedCategory.homologyFunctorFactors _ i).app P)
    refine ⟨hfinite, ⟨?_, hnorm M'⟩, hinterval⟩
    obtain ⟨a, b, htor⟩ := hfinite
    have hab : min a b ≤ b := min_le_right a b
    have ht := htor.mono (min_le_left a b) le_rfl
    have hlevel := hinterval (min a b) b hab ht
    constructor
    · intro n
      exact ⟨⟨min a b, b, hab, (hlevel n).2⟩, hconstructible n,
        min a b, b, (hlevel n).1⟩
    · exact ⟨min a b, b, min a b, b, hab, hab, fun n ↦
        ⟨(hlevel n).2, (hlevel n).1⟩⟩

end AlgebraicGeometry.ProEtale

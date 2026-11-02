/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldFiniteness
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Open direct image with a relative cohomological-dimension Tor bound

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-cor-sf-direct-image-ctf/_section.md (blueprint: sk-cor-sf-direct-image-ctf).
-/

@[expose] public section

set_option autoImplicit false

universe u

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.Etale

/-- The relative prime-power dimension bounds module-valued higher images because
forgetting coefficients reflects zero objects. Source: blueprint sk-cor-sf-direct-image-ctf,
proof paragraph 3 (blueprint: sk-cor-sf-direct-image-ctf). -/
private theorem openRelativeHeartBound
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [CommRing A]
    (hA : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0)
    {U X : Scheme.{u}} (j : U ⟶ X) [QuasiCompact j] [QuasiSeparated j]
    (d : ℕ) (hd : ProEtale.relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j ≤ d)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)
    (hq : (d : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  let V := sheafCompose U.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let W := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have ht : ProEtale.IsEllPowerTorsion ℓ (Fact.out : ℓ.Prime) (V.obj F) := by
    apply (ProEtale.ellPowerTorsion_iff_local_general U.smallEtaleTopology
      ℓ (Fact.out : ℓ.Prime) (V.obj F)).2
    intro T x
    refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
    intro Y f _
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    have hkill : ((ℓ ^ n : ℕ) : A) = 0 := by simpa only [nsmul_eq_mul, mul_one] using hn
    change (ℓ ^ n : ℕ) • F.obj.map f.op x = 0
    rw [← Nat.cast_smul_eq_nsmul A, hkill, zero_smul]
  have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (V.obj F)))) := by
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    by_contra hn
    have hr : (r : WithTop ℕ) ≤
        ProEtale.relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j := by
      rw [ProEtale.relativeCohomologicalDimension_eq_etale]
      exact le_sSup ⟨r, rfl, V.obj F, ht, hn⟩
    have hrd : r ≤ d := WithTop.coe_le_coe.mp (hr.trans hd)
    omega
  have hplus : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (V.obj F)))) :=
    hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (V.obj F))))
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso A j q F
  have hzero := hplus.of_iso e
  have hm : IsZero (higherDirectImage A j q F) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply W.map_injective
    exact hzero.eq_of_src _ _
  exact hm.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The open direct image over the pro-etale site preserves finite-coefficient
constant-model constructibility and finite Tor amplitude, with the upper Tor endpoint
shifted by any bound for the relative ell-cohomological dimension.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-cor-sf-direct-image-ctf/_section.md,
node statement; Stacks Project, Tags 0F10, 0F12, and 0F4M
(blueprint: sk-cor-sf-direct-image-ctf).

Conventions: `k` is finite or algebraically closed with `ℓ ≠ char k`, schemes are
separated of finite type over `k` (blueprint sec-conventions, prose-01-09; part six,
prose-P1-01), and `A` is a finite commutative `ℓ`-primary ring.

Proof (the four steps of the node):
1. `X` and `U` are Noetherian, so `j` is quasi-compact. `Rj_*K` is bounded constructible by
   sk-cor-geo-open-finiteness. By sk-cor-pe-finite-tor-comparison, `K ≅ ν_U^* K_et` with
   `K_et ∈ D^b_ctf(U_et, A)`, and by lem-exc-comparison-tor-interval `K_et` has Tor
   amplitude in `[a,b]` exactly when `K` does. `cd_ℓ(j)` is finite by
   sk-prop-classical-inputs, so some `d ≥ cd_ℓ(j)` exists.
2. For an `A`-module `M`, the projection map
   `(Rj_* K_et) ⊗ᴸ M_X → Rj_*(K_et ⊗ᴸ M_U)` in `D(X_et, A)` is an isomorphism: for
   quasi-compact etale `V → X` and `V_U = V ×_X U`, the torsion cohomological dimension of
   `V` and `V_U` is finite (det-prop-sf-finiteness, det-base-field-cd-finite-field), so
   lem-kun-0f12 gives `RΓ(V, -)` of the projection map as an isomorphism; hence its cone
   has vanishing cohomology sheaves and is zero.
3. At a geometric point `x̄`, lem-sfb-etale-derived-tensor-stalk and step 2 identify
   `(Rj_* K_et)_x̄ ⊗ᴸ M` with a stalk of `Rj_*(K_et ⊗ᴸ M_U)`. The complex
   `K_et ⊗ᴸ M_U` has `ℓ`-power torsion cohomology sheaves in `[a,b]`; by sk-def-cd,
   `R^q j_*` vanishes on them for `q > d` (and for `q < 0`), so truncation triangles put
   `Rj_*(K_et ⊗ᴸ M_U)` in `[a,b+d]`. The stalk criterion lem-sf-etale-stalk-tor-test gives
   Tor amplitude `[a,b+d]` of `Rj_* K_et`.
4. sk-prop-pe-unbounded-classical gives `Rj_* K ≅ ν_X^* Rj_{et,*} K_et`, and
   lem-exc-comparison-tor-interval transfers Tor amplitude `[a,b+d]` to it, tested against
   every module sheaf on `X_proet` (sk-def-sfb-constructible). With step 1 this gives both
   conjuncts. The empty scheme, the zero ring, `j = id` and `a > b` need no separate case.
-/
theorem openDirectImage_preserves_constantModelConstructibleFiniteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (_hbase : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ℓ)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    [QuasiCompact j]
    (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
    : letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := ⟨rfl⟩
      letI : IsTopologicalRing A := by infer_instance
      (∀ K : ConstantModelConstructibleFiniteTor
          (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U,
        (constantModelBoundedConstructible (Profinite.continuousMapRingObjOfUniverse.{u, u} A) X ⊓
          DerivedCategory.finiteTorAmplitude _)
          ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
            (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j)).obj K.obj)) ∧
      ∀ (d : ℕ),
        relativeCohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) j ≤ (d : WithTop ℕ) →
        ∀ (a b : ℤ)
          (K : DerivedCategory
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U))),
          (constantModelBoundedConstructible
              (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U K ∧
            DerivedCategory.torAmplitudeIn _ a b K) →
          constantModelBoundedConstructible (Profinite.continuousMapRingObjOfUniverse.{u, u} A) X
              ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
                (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j)).obj K) ∧
            DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))
              ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
                (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j)).obj K) := by
  classical
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have : IsTopologicalRing A := by infer_instance
  obtain ⟨n, hn, hAn⟩ := _hA
  have hkill : ((ℓ ^ n : ℕ) : A) = 0 := by
    simpa only [nsmul_eq_mul, mul_one] using hAn
  have hkill' : ((ℓ ^ n : ℕ) : ULift.{u + 1} A) = 0 := by
    apply ULift.ext
    exact hkill
  have hell : (ℓ : k) ≠ 0 := fun hz ↦
    _hchar (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz)
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients (ℓ ^ n) (ULift.{u + 1} A)
      (Spec (.of k)) := by
    have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr hell).pow n
    exact ⟨pow_pos (Fact.out : ℓ.Prime).pos n, inferInstance, hkill',
      by simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
  obtain ⟨hreal, hpush⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization_allChar
    k A E
  let V : Over (Spec (.of k)) := Over.mk (U ↘ Spec (.of k))
  let T : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  have : IsSeparated V.hom := inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  have : LocallyOfFiniteType T.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated T.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  let f : V ⟶ T := j.asOver (Spec (.of k))
  have : QuasiCompact f.left := inferInstanceAs (QuasiCompact j)
  have : QuasiSeparated f.left := inferInstanceAs (QuasiSeparated j)
  have hordered (d : ℕ)
      (hd : relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j ≤ d)
      (a b : ℤ) (hab : a ≤ b)
      (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A U))
      (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) U K ∧
        DerivedCategory.torAmplitudeIn _ a b K) :
      constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
          ((CondensedRing.moduleObjectDerivedPushforward
            (FiniteDiscreteOrdinary.coefficient A) j).obj K) ∧
        DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))
          ((CondensedRing.moduleObjectDerivedPushforward
            (FiniteDiscreteOrdinary.coefficient A) j).obj K) := by
    obtain ⟨eU, ⟨heU⟩⟩ := hreal V a b hab
    let L := eU.inverse.obj ⟨K, hK⟩
    let eL : (FiniteDiscreteOrdinary.internalEtaleRealization A U (E U)).obj L.obj ≅ K :=
      (heU.app L).symm ≪≫ (ObjectProperty.ι _).mapIso
        (eU.counitIso.app ⟨K, hK⟩)
    have hQ := Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
      k (ULift.{u + 1} A) (ℓ ^ n) hcoeff (X ↘ Spec (.of k)) j L.obj L.property.1
    have hcd (F : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) (q : ℕ) (hq : d < q) :
        IsZero
          (((AlgebraicGeometry.Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).rightDerived q).obj F) := by
      have hz := Etale.openRelativeHeartBound ℓ (ULift.{u + 1} A)
        ⟨n, by simpa only [nsmul_eq_mul, mul_one] using hkill'⟩ j d hd F q
        (by exact_mod_cast hq)
      exact hz.of_iso
        ((AlgebraicGeometry.Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homologyRightDerivedFunctorObjSingleFunctorIso
          F q).symm
    have hta := (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := ULift.{u + 1} A) (K := L.obj)).1 L.property.2
    have htQ := Etale.torAmplitudeIn_rightDerivedLowerStar_of_cohomologicalDimension
      (ULift.{u + 1} A) j d hcd a b hta
    have htQ' := (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := ULift.{u + 1} A) (K :=
        (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj L.obj)).2 htQ
    have habd : a ≤ b + (d : ℤ) := le_trans hab (le_add_of_nonneg_right (by omega))
    obtain ⟨eX, ⟨heX⟩⟩ := hreal T a (b + (d : ℤ)) habd
    let Q := eX.functor.obj ⟨_, hQ, htQ'⟩
    have hplus : ∃ c : ℤ, L.obj.IsGE c := by
      obtain ⟨c, e, hce, hLe⟩ := L.property.1.2
      exact ⟨c, (DerivedCategory.isGE_iff _ _).2 fun q hq ↦ hLe q (Or.inl hq)⟩
    obtain ⟨epush⟩ := hpush V T f
    let eQ := (heX.app ⟨_, hQ, htQ'⟩) ≪≫ epush.app ⟨L.obj, hplus⟩ ≪≫
      (CondensedRing.moduleObjectDerivedPushforward
        (FiniteDiscreteOrdinary.coefficient A) j).mapIso eL
    have hfield := (openDirectImage_field_finiteness_and_baseChange
      k ℓ _hchar.symm A n hn (by simpa only [Nat.cast_pow] using hkill)
      (U ↘ Spec (.of k)) (X ↘ Spec (.of k)) j (comp_over j _) K hK.1).1
    exact ⟨hfield, (DerivedCategory.torAmplitudeIn (FiniteDiscreteOrdinary.Internal A X)
      a (b + (d : ℤ))).prop_of_iso eQ Q.property.2⟩
  have hresult (d : ℕ)
      (hd : relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j ≤ d)
      (a b : ℤ) (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A U))
      (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) U K ∧
        DerivedCategory.torAmplitudeIn _ a b K) :
      constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
          ((CondensedRing.moduleObjectDerivedPushforward
            (FiniteDiscreteOrdinary.coefficient A) j).obj K) ∧
        DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))
          ((CondensedRing.moduleObjectDerivedPushforward
            (FiniteDiscreteOrdinary.coefficient A) j).obj K) := by
    by_cases hab : a ≤ b
    · exact hordered d hd a b hab K hK
    have h := hordered d hd b b le_rfl K ⟨hK.1, hK.2.mono (by omega) le_rfl⟩
    refine ⟨h.1, ?_⟩
    have hc := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hK.2
    have hzero : IsZero K := DerivedCategory.isZero_of_forall_isZero_homology K (by
      intro q
      by_cases hqa : q < a
      · exact (DerivedCategory.isGE_iff _ _).1 hc.1 q hqa
      · exact (DerivedCategory.isLE_iff _ _).1 hc.2 q (by omega))
    have : (CondensedRing.moduleObjectDerivedPushforward
        (FiniteDiscreteOrdinary.coefficient A) j).IsRightAdjoint :=
      (CondensedRing.derivedUpperStarLowerStarAdjunction
        (FiniteDiscreteOrdinary.coefficient A) j).isRightAdjoint
    have hzeroQ := (CondensedRing.moduleObjectDerivedPushforward
      (FiniteDiscreteOrdinary.coefficient A) j).map_isZero hzero
    intro N
    have hz := (MonoidalCategory.tensorRight ((DerivedCategory.singleFunctor _ 0).obj N))
      |>.map_isZero hzeroQ
    exact ⟨(DerivedCategory.isGE_iff _ _).2
        (fun q _ ↦ (DerivedCategory.homologyFunctor _ q).map_isZero hz),
      (DerivedCategory.isLE_iff _ _).2
        (fun q _ ↦ (DerivedCategory.homologyFunctor _ q).map_isZero hz)⟩
  refine ⟨?_, hresult⟩
  have hbase : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤ := by
    rcases _hbase with hfin | halg
    · exact lt_of_le_of_lt ((cohomologicalDimension_baseField ℓ (Fact.out : ℓ.Prime) k).2
        hfin) (WithTop.coe_lt_top 1)
    · rw [(cohomologicalDimension_baseField ℓ (Fact.out : ℓ.Prime) k).1 halg]
      exact WithTop.coe_lt_top 0
  have hfin := relativeCohomologicalDimension_lt_top_of_finiteType
    ℓ (Fact.out : ℓ.Prime) hbase j
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfin.ne
  intro K
  obtain ⟨a, b, hTor⟩ := K.property.2
  obtain ⟨hc, ht⟩ := hresult d hd.ge a b K.obj ⟨K.property.1, hTor⟩
  exact ⟨hc, a, b + (d : ℤ), ht⟩

end AlgebraicGeometry.ProEtale

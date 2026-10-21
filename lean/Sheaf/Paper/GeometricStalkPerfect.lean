/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Adjunction.Additive

import Sheaf.Paper.IntegralStalkRoosControl
import Sheaf.Paper.IntegralStalkResidueFinite
import all Sheaf.Paper.PointSectionsIntegralCohomologyControl
import Sheaf.Paper.FlatScalarExtensionFiniteCohomology
import Sheaf.RingTheory.DerivedCompleteModuleFinite
import Sheaf.RingTheory.DerivedCompleteHomology
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import all Sheaf.SixFunctors.FlatModelGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.LocalRing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Category.ModuleCat.Descent
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfIntegralConstructible

/-!
# Perfect geometric stalks

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-trace-perfectness`, order 1825
(blueprint: fix-lem-finite-tor-perfect).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

private theorem coefficientRing_local
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) :
    IsLocalRing (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) := by
  let R := Padic.coefficientExtensionRing l E n
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hdata.2.2.2.1
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hdata.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hproper : Padic.coefficientExtensionIdeal l E n ≠ ⊤ := by
    change Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n ≠ ⊤
    rw [hgen]
    intro htop
    have hle : Padic.coefficientExtensionMaximalIdeal l E ^ n ≤
        Padic.coefficientExtensionMaximalIdeal l E :=
      Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    exact hmax.ne_top (top_le_iff.mp (htop ▸ hle))
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing R := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)) Ideal.Quotient.mk_surjective
  have : IsLocalHom (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom :=
    ⟨fun a h ↦ h.map (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).symm.toRingHom⟩
  exact RingHom.domain_isLocalRing ULift.ringEquiv.toRingHom

attribute [-instance] WeilConjectures.pointReductionModuleDerived
  WeilConjectures.scalarReductionSiteSmall in
/-- Finite-coefficient pro-etale stalks have bounded finite-free models.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: exactness of the stalk identifies stalk cohomology with stalks of cohomology,
which are finite and bounded by constructibility. Apply the ringed-point derived tensor
comparison to a constant sheaf of an arbitrary coefficient module N. Its stalk is N,
so the finite Tor interval of M is also a Tor interval of its stalk. Apply the local
Artinian finite-Tor perfectness criterion to this bounded finite-cohomology complex.
Its perfect model has finite projective terms; localness makes these finite free. -/
theorem finiteTorConstructible_proEtale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ)
    (hK : WeilConjectures.finiteTorConstructible l E n hn Y (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (finiteCoefficientModuleStalkFunctor y (Padic.coefficientExtensionRing l E n))
           (ComplexShape.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  let A := ULift.{u + 1, u} B
  have : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have : IsLocalRing A := coefficientRing_local l E n hn
  have : IsNoetherianRing A := inferInstance
  let T := finiteCoefficientModuleStalkFunctor y B
  let C := T.mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  let V := ProEtale.finiteCoefficientIntrinsicRealization Y B
  letI : V.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact Y B).1
  let K₀ := V.mapDerivedCategory.objPreimage (DerivedCategory.Q.obj K)
  let e₀ := V.mapDerivedCategory.objObjPreimageIso (DerivedCategory.Q.obj K)
  obtain ⟨⟨_, hc⟩, a, b, ht⟩ := hK
  have ht₀ := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    B Y a b ht.1 K₀).mp (amplitude_iso Y B e₀.symm a b ht)
  obtain ⟨P, ha, hb, hp, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht₀
  let VP := (V.mapHomologicalComplex (.up ℤ)).obj P
  let ev : DerivedCategory.Q.obj VP ≅ DerivedCategory.Q.obj K :=
    (V.mapDerivedCategoryFactors.app P).symm ≪≫ V.mapDerivedCategory.mapIso e ≪≫ e₀
  let Ps := (T.mapHomologicalComplex (.up ℤ)).obj VP
  let es : DerivedCategory.Q.obj Ps ≅ C :=
    (T.mapDerivedCategoryFactors.app VP).symm ≪≫ T.mapDerivedCategory.mapIso ev
  have hps (i : ℤ) : ObjectProperty.flat (Ps.X i) := by
    let R := proEtaleModuleRestriction Y B
    let q : R.obj (V.obj (P.X i)) ≅ P.X i :=
      V.preimageIso (AlgebraicGeometry.flatModel_realize_restrict_iso Y B (V.obj (P.X i)))
    have hf : ObjectProperty.flat (R.obj (V.obj (P.X i))) :=
      ObjectProperty.prop_of_iso _ q.symm (hp i)
    have hff : ObjectProperty.flat
        (((ProEtale.geometricPoint y).sheafFiber (A := ModuleCat.{u + 1} A)).obj
          (R.obj (V.obj (P.X i)))) :=
      (ProEtale.geometricPoint y).flat_sheafFiber_obj hf
    let estalk :
        ((ProEtale.geometricPoint y).sheafFiber (A := ModuleCat.{u + 1} A)).obj
          (R.obj (V.obj (P.X i))) ≅ Ps.X i :=
      (ProEtale.geometricStalkIsoFiber y A _).symm ≪≫
        AlgebraicGeometry.flatModel_stalk_iso B (V.obj (P.X i)) y
    exact (ObjectProperty.flat (A := ModuleCat.{u + 1} A)).prop_of_iso estalk hff
  have htor : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) C :=
    ⟨a, b, (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso es
      (DerivedCategory.torAmplitudeIn_Q_obj_of_flat Ps a b hps)⟩
  have hbounded : DerivedCategory.TStructure.t.bounded C := by
    apply (DerivedCategory.exists_homologyConcentratedIn_iff_bounded C).mp
    exact ⟨_, _, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
      htor.choose_spec.choose_spec⟩
  have hfinite (i : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj C) := by
    let H := (DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj K)
    have hco := (proEtaleModuleRestriction_constructible_iff Y B H).mp (hc i)
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hco
    obtain ⟨c, _⟩ := (proEtale_comparison_stalk Y Ω y).2.2 A
    let S := sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood y)ᵒᵖ Y.ProEtᵒᵖ
        (ModuleCat.{u + 1} A)).obj (proEtaleGeometricNeighbourhoodForget y).op ⋙ colim
    let eH : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)).obj G ≅
        T.obj H := (c.app G).symm ≪≫ S.mapIso eG ≪≫
      AlgebraicGeometry.flatModel_stalk_iso B H y
    have : Module.Finite A
        (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)).obj G) :=
      (ModuleCat.isFinitelyGenerated_iff _).mp
        (hG.isFiniteSheaf.isFinitelyGenerated_sheafFiber Ω y)
    have hTH : Module.Finite A (T.obj H) := Module.Finite.equiv eH.toLinearEquiv
    exact @Module.Finite.equiv A _ _ _ _ _ _ _ hTH
      ((T.mapDerivedCategoryHomologyFunctorIso i).app (DerivedCategory.Q.obj K)).toLinearEquiv
  obtain ⟨Q, c, d, hQ₁, hQ₂, hQ, ⟨eQ⟩⟩ :=
    (DerivedCategory.isPerfect_of_finiteTorAmplitude hbounded hfinite htor).exists_free
  exact ⟨Q, c, d, hQ₁, hQ₂, hQ,
    ⟨(T.mapDerivedCategoryFactors.app K).symm ≪≫ eQ⟩⟩

attribute [-instance] WeilConjectures.pointReductionModuleDerived
  WeilConjectures.scalarReductionSiteSmall in
/-- The small-etale finite-coefficient assertion, with the actual derived-tensor
Tor predicate on etale module sheaves.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: exact geometric stalks preserve cohomology. Constructibility gives finite
cohomology, and boundedness gives finite support. The geometric ringed-topos point
commutes with derived tensor; apply it to every constant coefficient module N.
The given finite Tor interval therefore works for the stalk. The local Artinian
finite-Tor perfectness criterion supplies a bounded finite-projective model,
whose terms are finite free since the coefficient ring is local. -/
theorem finiteTorConstructible_etale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (_hn : 1 ≤ n)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) ℤ)
    (hK : AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((((pointSmallEtale y).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E n)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let Φ := (pointSmallEtale y).ulift.{u + 1}
  let T := Φ.sheafFiber (A := ModuleCat.{u + 1} A)
  letI : T.Additive := Φ.sheafFiber_additive
  let C := T.mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n _hn
  have : IsLocalRing A := coefficientRing_local l E n _hn
  have : IsNoetherianRing A := inferInstance
  obtain ⟨⟨_, hc⟩, a, b, ht⟩ := hK
  obtain ⟨P, ha, hb, hp, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht
  let Ps := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let es : DerivedCategory.Q.obj Ps ≅ C :=
    (T.mapDerivedCategoryFactors.app P).symm ≪≫ T.mapDerivedCategory.mapIso e
  have hps (i : ℤ) : ObjectProperty.flat (Ps.X i) := Φ.flat_sheafFiber_obj (hp i)
  have htor : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) C :=
    ⟨a, b, (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso es
      (DerivedCategory.torAmplitudeIn_Q_obj_of_flat Ps a b hps)⟩
  have hbounded : DerivedCategory.TStructure.t.bounded C := by
    apply (DerivedCategory.exists_homologyConcentratedIn_iff_bounded C).mp
    exact ⟨_, _, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
      htor.choose_spec.choose_spec⟩
  have hfinite (i : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj C) := by
    have hf := (hc i).isFiniteSheaf.isFinitelyGenerated_sheafFiber Ω y
    have hf' : Module.Finite A (T.obj
        ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj K))) := by
      apply (ModuleCat.isFinitelyGenerated_iff _).mp
      exact (ConcreteCategory.isFinitelyGenerated_iff_of_iso
        (((pointSmallEtale y).uliftSheafFiberIso (ModuleCat.{u + 1} A)).app _)).mpr hf
    letI := hf'
    exact @Module.Finite.equiv A _ _ _ _ _ _ _ hf'
      ((T.mapDerivedCategoryHomologyFunctorIso i).app
        (DerivedCategory.Q.obj K)).toLinearEquiv
  obtain ⟨Q, c, d, hQ₁, hQ₂, hQ, ⟨eQ⟩⟩ :=
    (DerivedCategory.isPerfect_of_finiteTorAmplitude hbounded hfinite htor).exists_free
  exact ⟨Q, c, d, hQ₁, hQ₂, hQ,
    ⟨(T.mapDerivedCategoryFactors.app K).symm ≪≫ eQ⟩⟩

end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable {Y : AlgebraicGeometry.Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The geometric stalk of an integral representative, followed by field scalar extension.
For the rational stage take ι to be the identity; for a common-stage object (E,K),
take the inclusion of its finite field E into the fixed algebraic closure.
The use of representatives does not impose an extra hypothesis: raw scalar localization
has exactly the integral objects, and the common-stage category has these pairs as objects.
Source: blueprint order 1825 and the rationalization/common-stage definitions
(blueprint: fix-lem-finite-tor-perfect). -/
noncomputable def fieldGeometricStalkComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (F : Type u) [Field F] (ι : E →+* F)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} F)) ℤ :=
  let φ : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1, u} F :=
    (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom.comp
      (ι.comp ((Padic.coefficientExtensionIntegers l E).subtype.comp
        (ULift.ringEquiv : ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom))
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).left_adjoint_additive
  ((integralCoefficientModuleStalkFunctor l E y ⋙
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K

attribute [-instance] WeilConjectures.pointReductionModuleDerived
  WeilConjectures.scalarReductionSiteSmall in
/-- A rational-coefficient geometric stalk has a bounded finite-dimensional model
and is perfect. The integral representative has only the recorded derived-complete
constructibility condition; no finite-Tor hypothesis is added at field coefficients.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: take all finite reductions of one flat-term K-flat resolution of K.
Exact stalks and derived tensor comparison give coherent quotient identifications
between their stalks (`def-weil-integral-derived-reduction`,
`lem-pur-kflat-change-of-rings`). Evaluation at strict localization commutes with
products (`lem-cbc-proetale-classical-stalk`), so the derived-completeness triangle
identifies the integral stalk with the derived limit of this tower, using exact
products of modules (`lem-weil-derived-limit-products-core`). The coefficient DVR
is complete: compatible lifts modulo uniformizer powers form a Cauchy sequence
in E, and the closed valuation balls give its prescribed residues and uniqueness
(`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-l-adic-extension-complete`).
The first reduction is over the residue field; choose bases of its finitely many
nonzero cohomology groups and lift them to cycles. Their finite sum gives a
quasi-isomorphism from a bounded finite-dimensional complex, hence a perfect model.
Apply `lem-weil-pbc-rlim-perfect-complete` to obtain a bounded finite-projective
O_E model of the integral stalk. The constant-to-completed map fixes its O_E action.
Localization O_E → E is flat, so termwise scalar extension preserves the derived
isomorphism; finite projective terms become finite-dimensional E-vector spaces.
This bounded model is perfect over E (`def-weil-rationalization-karoubi`). -/
theorem rationalConstructible_stalk_perfect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hK : sfIntegralConstructible l E Y (DerivedCategory.Q.obj K)) :
    (∃ (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, FiniteDimensional (ULift.{u + 1, u} E) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E y E (RingHom.id E) K) ≅
        DerivedCategory.Q.obj P)) ∧
      DerivedCategory.IsPerfect
        (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E y E (RingHom.id E) K)) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let R := ULift.{u + 1, u} O
  let J : Ideal O := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  let C := ((integralCoefficientModuleStalkFunctor l E y).mapHomologicalComplex (.up ℤ)).obj K
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let M : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R) := DerivedCategory.Q.obj C
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv O ULift.ringEquiv.symm
  have hO : Function.Bijective (AdicCompletion.of J O) :=
    ((Padic.finite_module_adic_complete_and_hom.{u, u, u} l E).1 O).2.1
  have : IsAdicComplete J O := AdicCompletion.of_bijective_iff.mp hO
  have hR : IsAdicComplete I R := by
    have ht := (IsAdicComplete.congr_ringEquiv J
      (ULift.ringEquiv.symm : O ≃+* R)).mpr (inferInstance : IsAdicComplete J O)
    dsimp only [J] at ht
    rw [Ideal.map_span, Set.image_singleton] at ht
    convert! ht using 1
  have hcomplete : Function.Bijective (AdicCompletion.of I R) :=
    AdicCompletion.of_bijective_iff.mpr hR
  obtain ⟨a, b, hab, hb⟩ := hK.2
  obtain ⟨hs, hc⟩ := integralStalk_roos_control l E y K hK.1 a b hab (fun n ↦ (hb n).2)
  have hcone := integralStalk_residue_finite l E y K (hb 0).1
  have hfg (i : ℤ) : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M) := by
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M
    have : Finite (N ⧸ (I • ⊤ : Submodule R N)) :=
      finite_quotient_of_finite_cone C (ULift.up (Padic.coefficientExtensionUniformizer l E))
        i (hcone i)
    exact (ModuleCat.finite_and_completion_bijective_of_isDerivedComplete I hcomplete
      N (DerivedCategory.isDerivedComplete_homology I M hc i)
      (inferInstance : Module.Finite (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N)))).1
  let f := pointIntegralToField l E
  have hf : f.Flat := by
    letI := (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).1
    have ho : (O.subtype : O →+* E).Flat :=
      RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat E (Submonoid.powers (Padic.coefficientExtensionUniformizer l E)))
    exact RingHom.Flat.ulift_iff.mpr ho
  have hfd := DerivedCategory.pointFiniteDimensional_of_flat_scalar_extension f hf C hs hfg
  have hperf : DerivedCategory.IsPerfect (DerivedCategory.Q.{u + 1}.obj
      (fieldGeometricStalkComplex l E y E (RingHom.id E) K)) := by
    apply (DerivedCategory.isPerfect_iff _).mpr
    constructor
    · obtain ⟨s, hs⟩ := hfd.1
      obtain ⟨c, hc⟩ := s.finite_toSet.bddBelow
      obtain ⟨d, hd⟩ := s.finite_toSet.bddAbove
      refine ⟨c, d, (DerivedCategory.isGE_iff _ c).mpr (fun i hi ↦ ?_),
        (DerivedCategory.isLE_iff _ d).mpr (fun i hi ↦ ?_)⟩
      · exact hs i (fun his ↦ (not_le_of_gt hi) (hc his))
      · exact hs i (fun his ↦ (not_le_of_gt hi) (hd his))
    · exact hfd.2
  refine ⟨?_, hperf⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hperf
  exact ⟨P, a, b, ha, hb, fun i ↦ (hP i).2, ⟨e⟩⟩

attribute [-instance] WeilConjectures.pointReductionModuleDerived
  WeilConjectures.scalarReductionSiteSmall in
/-- The geometric stalk of the common-stage object represented by (E,K) has a bounded
finite-dimensional model over the fixed algebraic closure and is perfect.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: every common-stage object is a pair with a finite field of definition, with
no idempotent completion. Apply the rational-stage assertion to its integral
representative. Extend the bounded finite-dimensional model along E → Qlbar.
Tensor over a field is exact, preserves the cohomology isomorphism, and sends each
finite-dimensional term to a vector space of the same finite dimension. The same
finite degree interval therefore gives the required perfect model. -/
theorem commonStageConstructible_stalk_perfect
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [IsAlgClosure ℚ_[l] F] (E : Padic.FiniteCoefficientFields l F)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E.val Y) ℤ)
    (hK : sfIntegralConstructible l E.val Y (DerivedCategory.Q.obj K)) :
    (∃ (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} F)) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, FiniteDimensional (ULift.{u + 1, u} F) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E.val y F E.val.subtype K) ≅
        DerivedCategory.Q.obj P)) ∧
      DerivedCategory.IsPerfect
        (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E.val y F E.val.subtype K)) := by
  classical
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val)
  let B := ULift.{u + 1, u} E.val
  let A := ULift.{u + 1, u} F
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} B) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let f : R →+* B :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((Padic.coefficientExtensionIntegers l E.val).subtype.comp ULift.ringEquiv.toRingHom)
  let g : B →+* A :=
    ULift.ringEquiv.symm.toRingHom.comp (E.val.subtype.comp ULift.ringEquiv.toRingHom)
  let S := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} g
  letI : S.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} g).isLeftAdjoint
  letI : S.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} g).left_adjoint_additive
  letI : PreservesFiniteColimits S := inferInstance
  letI : PreservesFiniteLimits S :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (letI := g.toAlgebra; inferInstanceAs (Module.Flat B A))
  obtain ⟨⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩, _⟩ :=
    rationalConstructible_stalk_perfect l E.val y K hK
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyLE b := hb
  let Q := (S.mapHomologicalComplex (.up ℤ)).obj P
  have hQ (i : ℤ) : FiniteDimensional A (Q.X i) := by
    letI : Algebra B A := g.toAlgebra
    have : Module.Finite B (P.X i) := hP i
    exact Module.Finite.base_change B A _
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} f).left_adjoint_additive
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (g.comp f)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (g.comp f)).left_adjoint_additive
  let C := ((integralCoefficientModuleStalkFunctor l E.val y).mapHomologicalComplex
    (.up ℤ)).obj K
  have ecomp : fieldGeometricStalkComplex l E.val y F E.val.subtype K ≅
      (S.mapHomologicalComplex (.up ℤ)).obj
        (fieldGeometricStalkComplex l E.val y E.val (RingHom.id E.val) K) := by
    change ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (g.comp f)).mapHomologicalComplex (.up ℤ)).obj C ≅
      (S.mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).mapHomologicalComplex (.up ℤ)).obj C)
    exact (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u + 1, u + 1} f g) (.up ℤ)).app C
  let eQ : DerivedCategory.Q.obj
      (fieldGeometricStalkComplex l E.val y F E.val.subtype K) ≅ DerivedCategory.Q.obj Q :=
    DerivedCategory.Q.mapIso ecomp ≪≫
      (S.mapDerivedCategoryFactors.{u + 1, u + 1}.app _).symm ≪≫
      S.mapDerivedCategory.{u + 1, u + 1}.mapIso eP ≪≫
      S.mapDerivedCategoryFactors.{u + 1, u + 1}.app P
  refine ⟨⟨Q, a, b, inferInstance, inferInstance, hQ, ⟨eQ⟩⟩,
    Q, a, b, inferInstance, inferInstance, fun i ↦ ?_, ⟨eQ⟩⟩
  have := hQ i
  exact ⟨inferInstance, inferInstance⟩

end WeilConjectures

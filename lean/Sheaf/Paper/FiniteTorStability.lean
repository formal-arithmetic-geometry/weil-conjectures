/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import Sheaf.Paper.IntrinsicCoefficientTwists

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.SfDerivedDirectImage

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.ExplicitExceptionalPreservation
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.IntegralConstructibleInternalHom
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Paper.FiniteStageVerdierBiduality
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.CompactSupportCoefficientTransition
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.IntegralResidueTor
import all Sheaf.SixFunctors.IntegralVerdier
import Sheaf.SixFunctors.FiniteExceptional
import all Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Paper.IntrinsicSitePerfectHomWindow
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.RingedTensorComparisonExtension
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds
import Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality
import Sheaf.SixFunctors.IntegralVerdierSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactUniverses
import all Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.CompactSupportRepresentativeIndependence
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Stability of the constructible finite-Tor domains

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-verdier,
`thm-sf-ctf-stability` (blueprint: thm-sf-ctf-stability).
Positive coefficient exponents are written as `n + 1`.

## Main statements

- `finiteTor_stability`: pullback, tensor, general Hom, and both direct images.
- `finiteTor_stability_exceptional_verdier`: exceptional preservation and dimension bounds.
- `finiteTor_stability_constructible_adjunction`: the constructible exceptional adjunction.
- `finiteTor_stability_origin`: the origin counterexample to a dimension-free Hom bound.
- `finiteTor_stability_quotients`, `finiteTor_stability_geometric_quotients`: finite change.
- `finiteTor_stability_integral_hom`, `finiteTor_stability_integral_verdier`: integral duality.
- `finiteTor_stability_integral_adjunction`: integral exceptional adjunction and reductions.
- `finiteTor_stability_rational`, `finiteTor_stability_algebraicClosure`: coefficient passage.
-/

@[expose] public section


set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The standing prime is invertible in every residue field of a k-scheme.
This is an actual inverse, obtained by mapping the base-field unit to the residue field.
Source: blueprint standing conventions (blueprint: thm-sf-ctf-stability). -/
@[instance_reducible]
noncomputable def sfStabilityResidueInvertible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))] (x : X) :
    Invertible (l : X.residueField x) := by
  let φ : D.k →+* X.residueField x :=
    (X.evaluation ⊤ x (by trivial)).hom.comp
      ((X ↘ Spec (.of D.k)).appTop.hom.comp (Scheme.ΓSpecIso (.of D.k)).inv.hom)
  exact (show IsUnit (l : X.residueField x) from by
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ).invertible

section Finite

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)


/-- Geometric Verdier duality with the actual comparison-defined exceptional
inverse image of the constant coefficient unit along the structure morphism.
Source: blueprint (vi) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteVerdier
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ((proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))))ᵒᵖ ⥤
      (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :=
  Prod.sectL ((proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))))ᵒᵖ
    ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
      (NagataCompactification aX)).obj
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit) ⋙
        (finiteIntrinsicDerivedInternalHom l E X n)

private theorem sfStabilityTorOfIso
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

private theorem sfStabilityFiniteTorOfIso
    (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) (hK : finiteTorConstructible l E (n + 1) (by omega) X K) :
    finiteTorConstructible l E (n + 1) (by omega) X L := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
    (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

private noncomputable def sfStabilityPullbackComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfFiniteDerivedPullback l E (n + 1) (by omega) f ≅ finiteDerivedPullback l E n f := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : HasDerivedCategory (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  exact Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (D := proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1))))
    (constantPullbackModel.{u} (Padic.coefficientExtensionRing l E (n + 1)) f)

private noncomputable def sfStabilityClosedUnitIso
    (X : Scheme.{u}) :
    (finiteIntrinsicClosed l E X n).monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
  let S := finiteIntrinsicClosed l E X n
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
  let S₀ := h.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let U := S₀.monoidal.tensorUnit
  let e := (S.adjunction U).leftAdjointUniq (S₀.adjunction U)
  exact (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    (e.app S.monoidal.tensorUnit).symm ≪≫ S.monoidal.leftUnitor U ≪≫ h₀.unitIso

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sfStabilityVerdierComparison
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    sfStabilityFiniteVerdier D l E n X (X ↘ Spec (.of D.k)) ≅
      FiniteExceptional.dual l E D X n := by
  let e := (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
    (NagataCompactification (X ↘ Spec (.of D.k)))).mapIso
      (sfStabilityClosedUnitIso l E n (Spec (.of D.k)))
  exact NatIso.ofComponents
    (fun K ↦ (finiteIntrinsicDerivedInternalHom l E X n).mapIso (Iso.prod (Iso.refl K) e))
    (by
      intro K L f
      change (finiteIntrinsicDerivedInternalHom l E X n).map _ ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map _ =
          (finiteIntrinsicDerivedInternalHom l E X n).map _ ≫
            (finiteIntrinsicDerivedInternalHom l E X n).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext <;> simp)

include hl in
/-- Clauses (i)--(iv), including the general and the site-perfect Hom intervals.
The same assertion includes every ordered input interval; Tor already includes
its ordering condition. No site-perfectness is assumed in the general Hom clause.
Source: current blueprint (blueprint: thm-sf-ctf-stability).

Proof: pullback preserves the input interval. Tensor adds the intervals using
bounded flat models. Geometric Verdier duality gives constructibility of general
internal Hom and the dimension-dependent interval. A local bounded finite-projective
model for a site-perfect first input gives the sharper reversed interval and the
coefficient-dual tensor formula by evaluation. Finite direct-image vanishing in
degrees above twice the source dimension gives (iii). Factor a compactification
as an open immersion followed by a proper morphism; extension by zero preserves
constructibility and Tor bounds, and (iii) applies to the proper factor.
The inputs are lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf,
cor-weil-finite-constructible-hom, lem-sfb-ringed-site-perfect-duality,
lem-sf-site-perfect-tor-window, lem-sf-flat-model,
thm-sf-direct-image-tor-amplitude, cor-sf-direct-image-ctf-proetale,
lem-trf-open-ctf, and prop-compactification-coherence-detailed. -/
theorem finiteTor_stability
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    (∀ K : (proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        ((finiteDerivedPullback l E n f.left).obj K)) ∧
    (∀ K L : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) L →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        (((finiteIntrinsicDerivedTensor l E X.left n)).obj (K, L)) ∧
      ∀ a b c d : ℤ, (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
        K a b → (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) L c
        d →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          (((finiteIntrinsicDerivedTensor l E X.left n)).obj (K, L)) (a + c) (b + d)) ∧
    (∀ K L : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) L →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L)) ∧
      (∀ (a b c d : ℤ) (m : ℕ),
        topologicalKrullDim X.left ≤ (m : WithBot ℕ∞) →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) K a b →
          (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) L c d →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L))
          (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))) ∧
      (IsFiniteCoefficientSitePerfect l E X.left n K →
        (Nonempty (((finiteIntrinsicDerivedTensor l E X.left n)).obj
          (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, (finiteIntrinsicClosed l
            E X.left n).monoidal.tensorUnit), L) ≅
            ((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L))) ∧
        ∀ a b c d : ℤ, (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n +
          1))) K a b → (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n +
          1))) L c d →
          (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
            (((finiteIntrinsicDerivedInternalHom l E X.left n)).obj (op K, L)) (c - b) (d - a))) ∧
    (∀ K : (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))),
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)
        ((proEtaleConstantDerivedDirectImage f.left (Padic.coefficientExtensionRing l E (n +
        1))).obj K) ∧
      ∀ (a b : ℤ) (d : ℕ), topologicalKrullDim X.left ≤ (d : WithBot ℕ∞) →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))) K a b →
        (HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E (n + 1)))
          ((proEtaleConstantDerivedDirectImage f.left (Padic.coefficientExtensionRing l E (n +
          1))).obj K)
          a (b + 2 * (d : ℤ))) ∧
    (∀ (c : Compactification f.left) (K : (proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E (n + 1)))), (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj K))
        := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of D.k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of D.k)) := ‹IsSeparated Y.hom›
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact sfStabilityFiniteTorOfIso l E n X.left
      ((sfStabilityPullbackComparison l E n f.left).app K)
      (sf_pullback_finiteTorConstructible D l hl E (n + 1) (by omega) X Y f K hK)
  · intro K L hK hL
    classical
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := proEtaleConstantRing X.left A
    let C := proEtaleRingModules X.left R
    let : HasDerivedCategory C := HasDerivedCategory.standard C
    let Kc := (DerivedCategory.Q (C := C)).objPreimage K
    let Lc := (DerivedCategory.Q (C := C)).objPreimage L
    let eK := (DerivedCategory.Q (C := C)).objObjPreimageIso K
    let eL := (DerivedCategory.Q (C := C)).objObjPreimageIso L
    have hKc := sfStabilityFiniteTorOfIso l E n X.left eK.symm hK
    have hLc := sfStabilityFiniteTorOfIso l E n X.left eL.symm hL
    obtain ⟨P, g, hP, _, hg, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral Kc
    obtain ⟨t, _, _⟩ := ringedTensorComparison_extension.{u + 1, u, u, u + 2}
      (ProEt.topology X.left) R
      (finiteIntrinsicClosed l E X.left n) (finiteIntrinsicTensorModels.{u} l E X.left n)
    have : IsIso (DerivedCategory.Q.map g) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C g).2 hg
    let e : derivedTensor X.left A Kc Lc P g hg hP ≅
        (finiteIntrinsicDerivedTensor l E X.left n).obj (K, L) :=
      t P Lc (.inl hP) ≪≫
        (finiteIntrinsicDerivedTensor l E X.left n).mapIso
          (Iso.prod (asIso (DerivedCategory.Q.map g) ≪≫ eK) eL)
    have ht (a b c d : ℤ) (htK : HasProEtaleTorAmplitude X.left A K a b)
        (htL : HasProEtaleTorAmplitude X.left A L c d) :=
      (finiteCoefficient_tensor_ctf D l hl E (n + 1) (by omega) X.left
        Kc Lc P g hg hP a b hKc
        (sfStabilityTorOfIso X.left A eK.symm a b htK) hLc.1).2 c d hLc
        (sfStabilityTorOfIso X.left A eL.symm c d htL)
    refine ⟨?_, ?_⟩
    · obtain ⟨a, b, htK⟩ := hK.2
      obtain ⟨c, d, htL⟩ := hL.2
      exact sfStabilityFiniteTorOfIso l E n X.left e (ht a b c d htK htL).1
    · intro a b c d htK htL
      exact sfStabilityTorOfIso X.left A e (a + c) (b + d) (ht a b c d htK htL).2
  · intro K L hK hL
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.hom
    obtain ⟨a, b, htK⟩ := hK.2
    obtain ⟨c, e, htL⟩ := hL.2
    have hh := finite_constructible_derivedHom_proEtale D l hl E (n + 1) (by omega)
      X.left d hd a b c e htK.1 htL.1 K L hK hL htK htL
    refine ⟨hh.1, ?_, ?_⟩
    · intro a b c e m hm htK htL
      exact (finite_constructible_derivedHom_proEtale D l hl E (n + 1) (by omega)
        X.left m hm a b c e htK.1 htL.1 K L hK hL htK htL).2
    · intro hperfect
      exact finiteIntrinsic_sitePerfect_hom_window l E X.left n K L hperfect
  · intro K hK
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.hom
    obtain ⟨a, b, ht⟩ := hK.2
    have hh := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l hl E (n + 1) (by omega) X Y f d hd a b hK ht
    refine ⟨⟨hh.1, a, b + 2 * (d : ℤ), hh.2⟩, ?_⟩
    intro a b d hd ht
    exact (ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l hl E (n + 1) (by omega) X Y f d hd a b hK ht).2
  · intro c K hK
    exact (FiniteExceptional.operations_preserve l E D hl f.left c n).1 ⟨K, hK⟩

include hl in
/-- Clauses (v)--(vi): the specified exceptional image preserves the constructible
finite-Tor domain, has the double-dimension interval, and agrees with the geometric
duality composite. The last predicate includes exactness and the canonical evaluation
biduality map, rather than merely an unspecified isomorphism to the double dual.
Source: current blueprint (blueprint: thm-sf-ctf-stability).

Proof: constructible exceptional preservation follows from local smooth/closed
factorizations and open-complement vanishing. Geometric finite-stage duality
identifies it with D_X f* D_Y. A duality on dimension at most e sends [u,v] to
[-v-2e,-u]; applying this twice gives [a-2dX,b+2dY]. General geometric biduality
supplies the exact anti-equivalence and invertibility of its evaluation transpose.
Empty schemes give the zero category and admit the dimension bound zero. -/
theorem finiteTor_stability_exceptional_verdier
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    (∀ (c : Compactification f.left) (K : (proEtaleDerivedCategory Y.left
      (Padic.coefficientExtensionRing l E (n + 1)))), (finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y.left) K →
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)
        ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K) ∧
      Nonempty ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        K ≅
        (sfStabilityFiniteVerdier D l E n X.left X.hom).obj
          (op ((finiteDerivedPullback l E n f.left).obj
            ((sfStabilityFiniteVerdier D l E n Y.left Y.hom).obj (op K))))) ∧
      ∀ (a b : ℤ) (dX dY : ℕ),
        topologicalKrullDim X.left ≤ (dX : WithBot ℕ∞) →
        topologicalKrullDim Y.left ≤ (dY : WithBot ℕ∞) → (HasProEtaleTorAmplitude Y.left
          (Padic.coefficientExtensionRing l E (n + 1))) K a b →
        (HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1)))
          ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K)
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))) ∧
    FiniteProEtaleVerdierBiduality l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left X.hom ∧
    FiniteProEtaleVerdierBiduality l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y.left Y.hom := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of D.k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of D.k)) := ‹IsSeparated Y.hom›
  refine ⟨?_, (finite_stage_verdier_biduality D l hl E (n + 1) (Nat.succ_pos n)
    X.left X.hom).2, (finite_stage_verdier_biduality D l hl E (n + 1) (Nat.succ_pos n)
      Y.left Y.hom).2⟩
  intro c K hK
  let VY := sfStabilityVerdierComparison D l E n Y.left
  let VX := sfStabilityVerdierComparison D l E n X.left
  let P := finiteDerivedPullback l E n f.left
  let e := (FiniteExceptional.dualFormulaIso l E D hl f.left c n).app ⟨K, hK⟩
  let e' := (FiniteExceptional.dual l E D X.left n).mapIso
    ((P.mapIso (VY.app (op K))).op) ≪≫
      (VX.app (op (P.obj ((sfStabilityFiniteVerdier D l E n Y.left Y.hom).obj (op K))))).symm
  refine ⟨(FiniteExceptional.operations_preserve l E D hl f.left c n).2 ⟨K, hK⟩,
    ⟨e ≪≫ e'⟩, ?_⟩
  intro a b dX dY hdX hdY ht
  have hY := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E Y.left n K hK.1
    dY hdY a b ht
  have hP := sf_pullback_torAmplitude D l hl E (n + 1) (Nat.succ_pos n) X Y f
    ((FiniteExceptional.dual l E D Y.left n).obj (op K)) hY.1
      (-b - 2 * (dY : ℤ)) (-a) hY.2.1
  let ep := (sfStabilityPullbackComparison l E n f.left).app
    ((FiniteExceptional.dual l E D Y.left n).obj (op K))
  have hpctf := sfStabilityFiniteTorOfIso l E n X.left ep
    ⟨hP.1, -b - 2 * (dY : ℤ), -a, hP.2⟩
  have hptor := sfStabilityTorOfIso X.left _ ep _ _ hP.2
  have hX := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X.left n _ hpctf.1
    dX hdX (-b - 2 * (dY : ℤ)) (-a) hptor
  have htor := sfStabilityTorOfIso X.left _ e.symm _ _ hX.2.1
  have ha : - -a - 2 * (dX : ℤ) = a - 2 * (dX : ℤ) := by omega
  have hb : -(-b - 2 * (dY : ℤ)) = b + 2 * (dY : ℤ) := by omega
  change HasProEtaleTorAmplitude X.left _
    ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).obj K)
      (- -a - 2 * (dX : ℤ)) (-(-b - 2 * (dY : ℤ))) at htor
  simpa only [ha, hb] using htor


open CategoryTheory.Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency.types false in
include hl in
/-- Intrinsic form of the exact Verdier anti-equivalence, for the same canonical
realization as the fixed-scalar biduality statement above.
Source: blueprint (vi) (blueprint: thm-sf-ctf-stability).
Proof: transport finite geometric duality through the canonical constant-ring
realization. Its tensor-Hom comparison identifies the dualizing object and evaluation,
so it identifies the specified intrinsic duality functor on both objects and maps. -/
theorem finiteTor_stability_verdier_intrinsic
    (X : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    IsExactAntiEquivalenceOn ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le
      n)) X.left)) (sfStabilityFiniteVerdier D l E n X.left X.hom) := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  let P := finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.left
  let V : (proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E (n + 1)))ᵒᵖ ⥤
      proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1)) :=
    FiniteExceptional.dual l E D X.left n
  let eV : sfStabilityFiniteVerdier D l E n X.left X.hom ≅ V :=
    sfStabilityVerdierComparison D l E n X.left
  have hp (K : proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E (n + 1))) (hK : P K) : P (V.obj (op K)) := by
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le X.hom
    obtain ⟨a, b, ht⟩ := hK.2
    have h := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X.left n K hK.1
      d hd a b ht
    exact ⟨h.1, -b - 2 * (d : ℤ), -a, h.2.1⟩
  let Vc := P.lift (P.ι.op ⋙ V) (fun K ↦ hp K.unop.obj K.unop.property)
  obtain ⟨tensor, signed, reduction, finiteSigned, hswap, heval, hfswap, hfeval⟩ :=
    IntegralVerdier.signedCalculus D l hl E X.left
  let ω := integralDualizingFiniteTerm l E D X.left n
  have hδ (K : P.FullSubcategory) :
      IsIso (ObjectProperty.homMk
        (IntegralVerdier.delta X.left (reduction n).target (finiteSigned n) ω K.obj) :
          K ⟶ (Vc.rightOp ⋙ Vc).obj K) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    obtain ⟨a, b, ht⟩ := K.property.2
    exact IntegralVerdier.finiteIntrinsicVerdier_biduality D l hl E X.left n
      (reduction n).target (finiteSigned n) (hfswap n) (hfeval n) K.obj K.property.1 a b ht
  let δ : 𝟭 P.FullSubcategory ≅ Vc.rightOp ⋙ Vc :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _
      (ObjectProperty.homMk (IntegralVerdier.delta X.left (reduction n).target
        (finiteSigned n) ω K.obj)) (hδ K)) (by
          intro K L f
          apply ObjectProperty.hom_ext
          exact signed_delta_natural X.left (reduction n).target (finiteSigned n)
            (hfswap n) (hfeval n) ω K.obj L.obj f.hom)
  have : Vc.IsEquivalence := dual_equivalence Vc δ
  refine ⟨?_, ⟨Vc.asEquivalence, ⟨Functor.isoWhiskerLeft P.ι.op eV.symm⟩⟩, ?_⟩
  · intro K hK
    exact sfStabilityFiniteTorOfIso l E n X.left (eV.symm.app (op K)) (hp K hK)
  · obtain ⟨s, hs⟩ :=
      (@CategoryTheory.RingedHomUniverses.ringedInternalHom_exact.{u + 1, u, u, u + 2}
        X.left.ProEt inferInstance (ProEt.topology X.left) inferInstance inferInstance
        (integralCoefficientCommRingSheaf l E X.left n) (HasDerivedCategory.standard _)).1 ω
    let : V.CommShift ℤ := s
    let : (sfStabilityFiniteVerdier D l E n X.left X.hom).CommShift ℤ :=
      Functor.CommShift.ofIso eV.symm ℤ
    have : NatTrans.CommShift eV.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility eV.symm ℤ
    refine ⟨inferInstance, ?_⟩
    intro T _ _ _ hT
    have hVT : V.mapTriangle.obj T ∈ distTriang
        (proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))) :=
      hs.map_distinguished T hT
    exact CategoryTheory.Pretriangulated.isomorphic_distinguished (V.mapTriangle.obj T) hVT
      ((sfStabilityFiniteVerdier D l E n X.left X.hom).mapTriangle.obj T)
      ((Functor.mapTriangleIso eV.symm).app T).symm


section Morphism

variable (X Y : Over (Spec (.of D.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]

/-- Literal restriction of the specified finite pullback.
Source: blueprint (i) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFinitePullback :
    ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      Y.left)).FullSubcategory ⥤ ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ
      (Nat.zero_le n)) X.left)).FullSubcategory :=
  ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).lift
    (((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)).ι ⋙
    finiteDerivedPullback l E n f.left)
    (fun K ↦ (finiteTor_stability D l hl E n X Y f).1 K.obj K.property)

/-- Literal restriction of the chosen compactification's compact-support image.
Source: blueprint (iv) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteSupport (c : Compactification f.left) :
    ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      X.left)).FullSubcategory ⥤ ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ
      (Nat.zero_le n)) Y.left)).FullSubcategory :=
  ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)).lift
    (((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).ι ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    (fun K ↦ (finiteTor_stability D l hl E n X Y f).2.2.2.2 c K.obj K.property)

/-- Literal restriction of the comparison-defined finite exceptional image.
Source: blueprint (v) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteExceptional (c : Compactification f.left) :
    ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      Y.left)).FullSubcategory ⥤ ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ
      (Nat.zero_le n)) X.left)).FullSubcategory :=
  ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).lift
    (((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y.left)).ι ⋙
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c)
    (fun K ↦ ((finiteTor_stability_exceptional_verdier D l hl E n X Y f).1
      c K.obj K.property).1)

end Morphism

/-- Literal constructible restriction of the geometric Verdier functor.
Source: blueprint (vi) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityFiniteDual
    (X : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      X.left)).FullSubcategoryᵒᵖ ⥤ ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ
      (Nat.zero_le n)) X.left)).FullSubcategory :=
  ((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).lift
    (((finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left)).ι.op ⋙
    sfStabilityFiniteVerdier D l E n X.left X.hom)
    (fun K ↦ (finiteTor_stability_verdier_intrinsic D l hl E n X).1 K.unop.obj K.unop.property)

/-- The finite exceptional image is the constructible right adjoint, and its
identification with D_X f* D_Y is natural on the entire constructible domain.
Source: blueprint (v) (blueprint: thm-sf-ctf-stability).
Proof: the etale compact-support adjunction transports to bounded constructible
pro-etale objects by the fully faithful comparison. Restrict it using preservation.
Finite geometric duality identifies both representing Hom functors; Yoneda gives
the stated natural isomorphism, including its map action. -/
theorem finiteTor_stability_constructible_adjunction
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    Nonempty (sfStabilityFiniteSupport (D := D) (l := l) (hl := hl) (E := E) (n := n) X Y f c ⊣
      sfStabilityFiniteExceptional (D := D) (l := l) (hl := hl) (E := E) (n := n) X Y f c) ∧
    Nonempty (sfStabilityFiniteExceptional (D := D) (l := l) (hl := hl) (E := E) (n := n) X Y f c ≅
      (sfStabilityFiniteDual D l hl E n Y).rightOp ⋙
        (sfStabilityFinitePullback (D := D) (l := l) (hl := hl) (E := E) (n := n) X Y f).op ⋙
          sfStabilityFiniteDual D l hl E n X) := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of D.k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  have : IsSeparated (Y.left ↘ Spec (.of D.k)) := ‹IsSeparated Y.hom›
  refine ⟨⟨FiniteExceptional.adjunction l E D hl f.left c n⟩, ?_⟩
  let VX := sfStabilityVerdierComparison D l E n X.left
  let VY := sfStabilityVerdierComparison D l E n Y.left
  let ey : (FiniteExceptional.dual l E D Y.left n).rightOp ≅
      (sfStabilityFiniteVerdier D l E n Y.left Y.hom).rightOp :=
    { hom := VY.hom.rightOp
      inv := VY.inv.rightOp
      hom_inv_id := by
        ext K
        dsimp
        simp only [← op_comp, VY.inv_hom_id_app, op_id]
      inv_hom_id := by
        ext K
        dsimp
        simp only [← op_comp, VY.hom_inv_id_app, op_id]
        rfl }
  let P := finiteDerivedPullback l E n f.left
  let eH := Functor.isoWhiskerRight ey (P.op ⋙ FiniteExceptional.dual l E D X.left n) ≪≫
    Functor.isoWhiskerLeft
      (sfStabilityFiniteVerdier D l E n Y.left Y.hom).rightOp
      (Functor.isoWhiskerLeft P.op VX.symm)
  refine ⟨Functor.fullyFaithfulCancelRight
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.left).ι ?_⟩
  exact FiniteExceptional.dualFormulaIso l E D hl f.left c n ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y.left).ι eH


/-- The origin example in clause (ii). Both inputs have Tor interval [0,0], but
internal Hom is the supported minus-one twist shifted by -2 and has nonzero H².
Thus the site-perfect hypothesis in the elementary coefficient-dual formula cannot
be dropped. The affine line and its origin map are literal polynomial spectra.
Source: blueprint (ii) (blueprint: thm-sf-ctf-stability).

Proof: geometric stalks of the origin pushforward are A at the origin and zero
elsewhere, so this sheaf and the coefficient unit are flat. Closed-support Hom
identifies the displayed internal Hom with i_* i! A. Compare the closed ambient
adjoint with the constructible exceptional adjoint by the localization triangle
and full faithfulness of i_*. Codimension-one zero-section purity gives
 i! A = A(-1)[-2]. Exactness of i_* and tensor projection transport this to the
asserted isomorphism. The twisting line has rank one over the nonzero positive
coefficient quotient, and fully faithful i_* makes its H² nonzero. -/
noncomputable def sfStabilityOriginConclusions : Prop := by
  let Z : Scheme.{u} := Spec (.of D.k)
  let V : Scheme.{u} := Spec (.of (MvPolynomial (Fin 1) D.k))
  let a : V ⟶ Z := Spec.map (CommRingCat.ofHom (MvPolynomial.C : D.k →+*
    MvPolynomial (Fin 1) D.k))
  let i : Z ⟶ V := Spec.map (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (RingHom.id D.k) (fun _ : Fin 1 ↦ (0 : D.k))))
  letI : V.Over Z := ⟨a⟩
  letI : ∀ x : V, Invertible (l : V.residueField x) := sfStabilityResidueInvertible D l hl V
  let oneZ : proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E (n + 1)) :=
    (finiteIntrinsicClosed l E Z n).monoidal.tensorUnit
  let oneV : proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E (n + 1)) :=
    (finiteIntrinsicClosed l E V n).monoidal.tensorUnit
  let K : proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E (n + 1)) :=
    (proEtaleConstantDerivedDirectImage i
      (Padic.coefficientExtensionRing l E (n + 1))).obj oneZ
  let M : proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E (n + 1)) :=
    (finiteIntrinsicDerivedInternalHom l E V n).obj (op K, oneV)
  exact HasProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E (n + 1)) K 0 0 ∧
    HasProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E (n + 1)) oneV 0 0 ∧
  Nonempty (M ≅ (shiftFunctor (proEtaleDerivedCategory V (Padic.coefficientExtensionRing l E (n
    + 1))) (-2 : ℤ)).obj
    ((finiteComplexTwist l E V n (-1)).obj K)) ∧
  ¬ IsZero ((@DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E V n)
    _ _ (HasDerivedCategory.standard _) 2).obj M)

/-- The origin example in clause (ii). Both inputs have Tor interval [0,0], but
internal Hom is the supported minus-one twist shifted by -2 and has nonzero H².
Thus the site-perfect hypothesis in the elementary coefficient-dual formula cannot
be dropped. The affine line and its origin map are literal polynomial spectra.
Source: blueprint (ii) (blueprint: thm-sf-ctf-stability).

Proof: geometric stalks of the origin pushforward are A at the origin and zero
elsewhere, so this sheaf and the coefficient unit are flat. Closed-support Hom
identifies the displayed internal Hom with i_* i! A. Compare the closed ambient
adjoint with the constructible exceptional adjoint by the localization triangle
and full faithfulness of i_*. Codimension-one zero-section purity gives
 i! A = A(-1)[-2]. Exactness of i_* and tensor projection transport this to the
asserted isomorphism. The twisting line has rank one over the nonzero positive
coefficient quotient, and fully faithful i_* makes its H² nonzero. -/
theorem finiteTor_stability_origin :
    sfStabilityOriginConclusions (D := D) (l := l) (hl := hl) (E := E) (n := n) := by
  sorry

end Finite

section Quotients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized strict-tower quotient and the direct quotient factor induce
exactly the same scalar restriction. This fixes the normalization used in its mate.
Source: blueprint (vii), canonical finite quotients (blueprint: thm-sf-ctf-stability).
Proof: the tower quotient is a composite of adjacent coefficient quotient factors.
On a representative from the valuation ring, every factor sends its residue class
to the same residue class. Induct on the difference of the exponents, including
zero for the identity quotient, to identify the composite with the direct factor.
Constant sheafification and forgetting commutativity preserve this equality.
Restriction of module scalars and termwise derived localization then preserve it. -/
theorem sfStabilityQuotientRestrictionEquality
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h =
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory := by
  dsimp only [normalizedDVRRes]
  congr 1
  exact compactSupportModuleRes_eq l E W h

/-- Canonical finite-quotient compact-support comparison, obtained by scalar
adjunction from the normalized restriction square. This definition includes all
quotients, including the identity, and assumes no ambient exceptional adjunction.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilitySupportReduction
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        coefficientFiniteQuotientDerived l E Y h ⟶
      coefficientFiniteQuotientDerived l E X h ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  ((mateEquiv
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    ((coefficientDerivedSystemEvaluationCalculus l E Y).choose.quotientCalculus.adjunction h)).symm
      (TwoSquare.mk _ _ _ _
        ((Functor.isoWhiskerRight
          (eqToIso (sfStabilityQuotientRestrictionEquality l E X h)) _).hom ≫
          (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom ≫
          (Functor.isoWhiskerLeft _
            (eqToIso (sfStabilityQuotientRestrictionEquality l E Y h)).symm).hom))).natTrans

/-- The quotient reduction of the geometric dualizing object. The first factor is
uniqueness of the left adjoint to the very same exact scalar restriction; the
second is the specified exceptional coefficient mate, normalized at the unit.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityDualizingReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E X h).obj
        (integralDualizingFiniteTerm l E D X m) ⟶ integralDualizingFiniteTerm l E D X n :=
  (Adjunction.leftAdjointUniq
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h))).hom.app _ ≫
      integralDualizingFiniteComparison l E D X hl h

/-- The actual Verdier coefficient arrow is reduced evaluation followed by the
normalized dualizing-object comparison. Thus evaluation, not an arbitrary object
isomorphism, determines its value and its tensor-Hom transpose.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityVerdierReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1))) :
    (coefficientFiniteQuotientDerived l E X h).obj
        ((finiteIntrinsicDerivedInternalHom l E X m).obj
          (op K, integralDualizingFiniteTerm l E D X m)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((coefficientFiniteQuotientDerived l E X h).obj K),
          integralDualizingFiniteTerm l E D X n) :=
  finiteIntrinsicReductionHom l E X h K (integralDualizingFiniteTerm l E D X m) ≫
    (finiteIntrinsicDerivedInternalHom l E X n).map
      (Prod.mkHom (𝟙 _) (sfStabilityDualizingReduction D l hl E X h))

/-- Finite quotient change preserves the finite-Tor domain and commutes with
its actual internal Hom, tensor, Verdier duality and compact-support direct image.
The displayed evaluation compatibility includes naturality, every transpose and
internal composition; the tensor comparison is fixed on K-flat pure tensors.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: scalar extension on bounded flat models preserves the constructible Tor
domain. The tensor comparison is the normalized derived balancing comparison.
For general Hom use geometric Verdier duality and the finite Hom coefficient
theorem, which identifies exactly the transpose of reduced evaluation. Apply
exceptional coefficient change at the coefficient unit for the dualizing object;
composition with Hom reduction gives Verdier change. Compact support is open
extension followed by proper direct image, and both coefficient comparisons are
the canonical scalar mates of the normalized restriction squares. -/
theorem finiteTor_stability_quotients
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m) :
    (∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      finiteTorConstructible l E (n + 1) (Nat.le_add_left 1 n) X
        ((coefficientFiniteQuotientDerived l E X h).obj K)) ∧
    (∀ K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X L →
      IsIso (finiteIntrinsicReductionHom l E X h K L)) ∧
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X m)
      (finiteIntrinsicClosed l E X n) (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    (∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      IsIso (sfStabilityVerdierReduction D l hl E X h K)) ∧
    ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1))),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) X K →
      IsIso ((sfStabilitySupportReduction l E c h).app K) := by
  sorry

/-- The remaining geometric coefficient comparisons, stated using their published
canonical maps. The exceptional comparison is on the etale-origin presentation of
the finite-Tor domain, transported by the same comparison functors that define
sfFiniteExceptional. Its counit equation fixes the adjunction comparison.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the pullback map is ordinary scalar balancing on a K-flat representative.
For ordinary direct image, use the counit-defined coefficient map and finite-type
constructibility and cohomological dimension; pro-etale constructible origin gives
the assertion for every input of the fixed-scalar domain. Compact-support coefficient
change is open scalar balancing followed by the proper coefficient comparison.
Taking its mate through the two finite constructible adjunctions gives the
exceptional comparison. Geometric Verdier duality makes that mate invertible, and
its defining adjunction equation is precisely the displayed counit identity.
The mate identities then also identify units; no ambient pro-etale adjunction is used. -/
noncomputable def sfStabilityGeometricQuotientConclusions
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) {m n : ℕ} (h : n ≤ m) : Prop :=
    letI := c.hasCompactification
    let φ := (compactSupportLevelQuotient l E m n h).ulift
    (∀ K : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (m + 1)),
      finiteTorConstructible l E (m + 1) (Nat.le_add_left 1 m) Y.left K →
      IsIso ((explicitExceptionalCoefficientComparison l E n m h f.left).app K)) ∧
    (∀ K : DerivedCategory (Sheaf (ProEt.topology X.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))))),
      finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.le_add_left 1 m) X.left K →
      IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ f.left K)) ∧
    (∀ L : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))) Y.left,
      finiteTorConstructibleEtale l E (m + 1) (Nat.le_add_left 1 m) Y.left L →
      IsIso (Etale.ExceptionalCoefficients.mateMap φ f.left L) ∧
      (Etale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
          f.left).map (Etale.ExceptionalCoefficients.mateMap φ f.left L) ≫
        (Etale.rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
            f.left).counit.app ((Etale.scalarExtension φ Y.left).obj L) =
      Etale.ExceptionalCoefficients.comparisonInverse φ
        (HasCompactification.compactification f.left)
        ((Etale.rightDerivedUpperShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))))
            f.left).obj L) ≫
        (Etale.scalarExtension φ Y.left).map
          ((Etale.rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))))
              f.left).counit.app L))

include hl in
/-- The remaining geometric coefficient comparisons, stated using their published
canonical maps. The exceptional comparison is on the etale-origin presentation of
the finite-Tor domain, transported by the same comparison functors that define
sfFiniteExceptional. Its counit equation fixes the adjunction comparison.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the pullback map is ordinary scalar balancing on a K-flat representative.
For ordinary direct image, use the counit-defined coefficient map and finite-type
constructibility and cohomological dimension; pro-etale constructible origin gives
the assertion for every input of the fixed-scalar domain. Compact-support coefficient
change is open scalar balancing followed by the proper coefficient comparison.
Taking its mate through the two finite constructible adjunctions gives the
exceptional comparison. Geometric Verdier duality makes that mate invertible, and
its defining adjunction equation is precisely the displayed counit identity.
The mate identities then also identify units; no ambient pro-etale adjunction is used. -/
theorem finiteTor_stability_geometric_quotients
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) {m n : ℕ} (h : n ≤ m) :
    sfStabilityGeometricQuotientConclusions (D := D) (l := l) (E := E) X Y f c h := by
  sorry

end Quotients

section Integral

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integral dualizing object from the normalized finite exceptional tower.
It is characterized by its compact-support representing property; the choice is
only between canonically isomorphic representatives of that object.
Source: blueprint (vii), integral paragraph (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralDualizing
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    sfIntegralConstructibleCategory l E X :=
  let hd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  (prop_coef_integral_dualizing D l hl E X hd.choose hd.choose_spec).choose

/-- Geometric integral Verdier duality, using the ambient K-injective sheaf Hom
into the canonical integral dualizing object.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralVerdier
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  Prod.sectL _ (sfStabilityIntegralDualizing D l hl E X).obj ⋙
    integralDerivedInternalHom l E X

private theorem sfStabilityConstructible_iff_legacy
    (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    sfIntegralConstructible l E X K ↔
      boundedConstructibleDerivedCompleteIntegral D l hl E X K := by
  constructor
  · rintro ⟨hc, a, b, hab, h⟩
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hl K).mp hc, a, b, hab, ?_⟩
    intro n
    exact ⟨(h n).1, fun i hi ↦ (h n).2 hi⟩
  · rintro ⟨hc, a, b, hab, h⟩
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hl K).mpr hc, a, b, hab, ?_⟩
    intro n
    exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩

include hl in
/-- Integral constructibility equals the uniform finite-Tor constructibility
condition, and general ambient internal Hom preserves it with its canonical reductions.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the residue-field Tor criterion for the coefficient DVR upgrades the
bounded constructible residue interval to one Tor interval at every positive level.
Apply the integral Hom reduction theorem, whose map is the transpose of reduced
evaluation. Its finite reductions are constructible by geometric finite-coefficient
Hom; a dimension bound gives a common cohomological interval. Completeness of the
second argument implies completeness of internal Hom. This is the defining integral
constructibility condition. -/
theorem finiteTor_stability_integral_hom
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X) ∧
    ∀ K L : DerivedCategory (scalarReductionSource.{u, u} l E X),
      sfIntegralConstructible l E X K → sfIntegralConstructible l E X L →
      sfIntegralConstructible l E X ((integralDerivedInternalHom l E X).obj (op K, L)) ∧
      ∀ n : ℕ, IsIso (integralHomReductionComparison D l hl E X n K L) := by
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfStabilityResidueInvertible D l hl X
  refine ⟨(integral_residue_tor D l hl E X).2, ?_⟩
  intro K L hK hL
  have h := integral_constructible_internalHom D l hl E X K L
    ((sfStabilityConstructible_iff_legacy D l hl E X K).mp hK)
    ((sfStabilityConstructible_iff_legacy D l hl E X L).mp hL)
  exact ⟨(sfStabilityConstructible_iff_legacy D l hl E X _).mpr h.1, h.2.1⟩

/-- Integral geometric Verdier duality is an exact anti-equivalence.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the integral dualizing tower has the canonical finite dualizing reductions.
The preceding Hom reduction identifies every reduced Verdier functor with finite
Verdier duality, respecting evaluation. Finite biduality therefore makes every
reduction of the canonical biduality map invertible. Derived completeness makes
reduction conservative, so biduality is invertible integrally. Signed Hom exactness
on triangles gives the exact contravariant equivalence. -/
theorem finiteTor_stability_integral_verdier
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    IsExactAntiEquivalenceOn (sfIntegralConstructible l E X)
      (sfStabilityIntegralVerdier D l hl E X) := by
  classical
  let hd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  let h := prop_coef_integral_dualizing D l hl E X hd.choose hd.choose_spec
  let T := h.choose_spec.choose
  let hT := h.choose_spec.choose_spec
  let e := hT.2.1.choose
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  let p := hT.2.2.2.1.choose
  have hp := hT.2.2.2.1.choose_spec.choose_spec.2.1
  let r (n : ℕ) :
      (scalarReductionDerivedExtension l E X n).obj h.choose.obj ≅
        integralDualizingFiniteTerm l E D X n :=
    @asIso _ _ _ _ (normalizedDVRCounitComparison l E X D hl T h.choose.obj p n)
      (hp n) ≪≫ e n
  obtain ⟨tensor, symmetry, reduction, finiteSymmetry, heq, preservation, hanti, hexact,
      hrest⟩ := integral_verdier_biduality D l hl E X h.choose r
  let := hanti
  change IsExactAntiEquivalenceOn (sfIntegralConstructible l E X)
    (IntegralVerdier.dual l E X h.choose.obj)
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    exact preservation ⟨K, hK⟩
  · exact ⟨(IntegralVerdier.restrictedDual l E X h.choose.obj preservation).asEquivalence,
      ⟨Iso.refl _⟩⟩
  · exact hexact

/-- Literal constructible integral Verdier functor, with the existing map action.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralDual
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    ((sfIntegralConstructible l E X).ι.op ⋙ sfStabilityIntegralVerdier D l hl E X)
    (fun K ↦ (finiteTor_stability_integral_verdier D l hl E X).1 K.unop.obj K.unop.property)

/-- Canonical reduction of the chosen integral dualizing representative, extracted
from its normalized coherent tower and the counit of scalar extension/restriction.
Both the tower and its finite identifications are those of the representing theorem.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralDualizingReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E X n).obj
        (sfStabilityIntegralDualizing D l hl E X).obj ⟶ integralDualizingFiniteTerm l E D X n := by
  let hd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  let h := prop_coef_integral_dualizing D l hl E X hd.choose hd.choose_spec
  let T := h.choose_spec.choose
  let hT := h.choose_spec.choose_spec
  let e := hT.2.1.choose
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  let p := hT.2.2.2.1.choose
  exact normalizedDVRCounitComparison l E X D hl T h.choose.obj p n ≫ (e n).hom

/-- Reduced geometric Verdier duality is the evaluation-defined Hom comparison
followed by the normalized dualizing comparison.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralVerdierReduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (n : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (scalarReductionDerivedExtension.{u, u} l E X n).obj
        ((sfStabilityIntegralVerdier D l hl E X).obj (op K)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((scalarReductionDerivedExtension.{u, u} l E X n).obj K),
          integralDualizingFiniteTerm l E D X n) :=
  integralHomReductionComparison D l hl E X n K
      (sfStabilityIntegralDualizing D l hl E X).obj ≫
    (finiteIntrinsicDerivedInternalHom l E X n).map
      (Prod.mkHom (𝟙 _) (sfStabilityIntegralDualizingReduction D l hl E X n))

private theorem sfStabilityIsIsoHomComposite
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (F : C₁ × C₂ ⥤ C₃) {Z : C₁} {A B : C₂} {P : C₃}
    (r : A ⟶ B) (h : P ⟶ F.obj (Z, A)) (hr : IsIso r) (hh : IsIso h) :
    IsIso (h ≫ F.map (Prod.mkHom (𝟙 Z) r)) := by
  let := hr
  let := hh
  have : IsIso (Prod.mkHom (𝟙 Z) r) :=
    (isIso_prod_iff C₁ C₂).mpr ⟨inferInstance, hr⟩
  exact IsIso.comp_isIso

/-- Every canonical finite reduction of integral Verdier duality is invertible.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).
Proof: the normalized DVR counit for the dualizing tower and its finite exceptional
identifications are invertible. The general integral Hom coefficient comparison
is invertible on constructible pairs. Their displayed composite is therefore invertible. -/
theorem finiteTor_stability_integral_verdier_reduction
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : sfIntegralConstructible l E X K) (n : ℕ) :
    IsIso (sfStabilityIntegralVerdierReduction D l hl E X n K) := by
  classical
  let hd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  let h := prop_coef_integral_dualizing D l hl E X hd.choose hd.choose_spec
  let T := h.choose_spec.choose
  let hT := h.choose_spec.choose_spec
  let e := hT.2.1.choose
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  let p := hT.2.2.2.1.choose
  have hp := hT.2.2.2.1.choose_spec.choose_spec.2.1
  have : IsIso (normalizedDVRCounitComparison l E X D hl T h.choose.obj p n) := hp n
  have hred : IsIso (sfStabilityIntegralDualizingReduction D l hl E X n) := by
    change IsIso (normalizedDVRCounitComparison l E X D hl T h.choose.obj p n ≫
      (e n).hom)
    exact IsIso.comp_isIso
  have hhom := (finiteTor_stability_integral_hom D l hl E X).2 K
    (sfStabilityIntegralDualizing D l hl E X).obj hK
    (sfStabilityIntegralDualizing D l hl E X).property |>.2 n
  exact sfStabilityIsIsoHomComposite
    (finiteIntrinsicDerivedInternalHom l E X n) _ _ hred hhom

-- Keep the completed operations and their chosen localization models folded in proofs.
attribute [local irreducible] integralDerivedPullback integralDerivedInternalHom
  scalarReductionExistence scalarReductionDerivedExistence sfStabilityIntegralVerdier
  sfIntegralCompactSupportValue sfRationalCompactSupportValue

private theorem sfStabilityIntegralVerdierTor
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : sfIntegralConstructible l E X K) (n d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b) :
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj
        ((sfStabilityIntegralVerdier D l hl E X).obj (op K)))
      (-b - 2 * (d : ℤ)) (-a) := by
  obtain ⟨c, e, hce, hred⟩ := hK.2
  have hfinite := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X n _
    (hred n).1 d hd a b hTor
  have := finiteTor_stability_integral_verdier_reduction D l hl E X K hK n
  exact sfStabilityTorOfIso X _
    (asIso (sfStabilityIntegralVerdierReduction D l hl E X n K)).symm _ _ hfinite.2.1

private noncomputable def sfStabilityIntegralPullbackReduction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : sfIntegralConstructible l E Y K) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E X n).obj
        ((integralDerivedPullback l E f).obj K) ≅
      (sfFiniteDerivedPullback l E (n + 1) (Nat.succ_pos n) f).obj
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K) := by
  let h := goodRepresentative l E Y K
  let P := h.choose
  let e := h.choose_spec.some
  haveI := (integralOperations_preserve_constructible l E f).1 K hK |>.2 P e n
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : HasDerivedCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (proEtaleRingModules Y (proEtaleConstantRing Y A)) :=
    HasDerivedCategory.standard _
  let F := proEtaleConstantRingPullback A f
  exact asIso (integralPullbackFiniteComparison l E f K P e n) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (.up ℤ)).app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≪≫
    (F.mapDerivedCategoryFactors.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.app
      ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)).symm ≪≫
    F.mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.mapIso
      (finiteReductionIso l E Y K P e n).symm

section Morphism

variable (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Integral support on maps: apply the published coherent support-reduction tower,
then the total right derived inverse limit. The same chosen compactification is used
at every level. This is the general-morphism version of integralDualizingCompactTower,
using its exact same published tower construction, not an objectwise limit choice.
Source: blueprint (iv),(vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralSupportAmbient (c : Compactification f) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E Y) := by
  let h := exists_compactSupportReductionTower l E D.k X Y f
    (finiteFieldDatumPrimeUnit D l hl) c
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose ⋙ integralDualizingLimit l E Y

/-- The constructible candidate for integral exceptional inverse image, constructed
from the canonical geometric dualizing objects and completed inverse image. Its
adjunction to integral compact support, asserted below, identifies it with the
specified exceptional adjoint by the unique compatible adjoint isomorphism.
Source: blueprint (v),(vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralExceptionalAmbient :
    DerivedCategory (scalarReductionSource.{u, u} l E Y) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  (sfStabilityIntegralVerdier D l hl E Y).rightOp ⋙
    (integralDerivedPullback l E f).op ⋙ sfStabilityIntegralVerdier D l hl E X

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem sfStabilityIntegralSupportConstructible (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : sfIntegralConstructible l E X K) :
    sfIntegralConstructible l E Y
      ((sfStabilityIntegralSupportAmbient D l hl E X Y f c).obj K) := by
  classical
  have h := exists_compactSupportRepresentativeComparison l E D.k
    (finiteFieldDatumPrimeUnit D l hl) X Y f c
  have hT := h.choose_spec.choose_spec
  have hR := hT.2.2.choose_spec.choose_spec
  have hF := hR.2.2.choose_spec.2
  let F := hF.choose
  let γ := hF.choose_spec.2.2.2.1.choose
  let ε : hT.2.2.choose ≅ integralDualizingLimit l E Y := eqToIso hR.1
  let δ := γ.app ⟨K, hK⟩ ≪≫ ε.app (h.choose.obj K) ≪≫
    (integralDualizingLimit l E Y).mapIso (eqToIso (Functor.congr_obj hT.1 K))
  exact ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y) δ
    (F.obj ⟨K, hK⟩).property

attribute [local irreducible] sfStabilityIntegralSupportAmbient

/-- Integral support and the duality-defined exceptional adjoint preserve bounded
constructibility and derived completeness. The exceptional reductions have a common
finite Tor interval for every supplied pair of nonnegative dimension bounds.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).
Proof: the coherent support tower is constructible with uniformly bounded finite
reductions, and normalized DVR effectivity gives its complete limit. Integral Hom
and duality preserve the category by the preceding clauses, as does completed
pullback. Reduce the duality composite: finite duality, unchanged pullback intervals
and finite duality again give [a-2dX,b+2dY] uniformly in the positive level. -/
theorem finiteTor_stability_integral_images (c : Compactification f) :
    (∀ K : DerivedCategory (scalarReductionSource.{u, u} l E X),
      sfIntegralConstructible l E X K →
      sfIntegralConstructible l E Y
        ((sfStabilityIntegralSupportAmbient D l hl E X Y f c).obj K)) ∧
    (∀ L : DerivedCategory (scalarReductionSource.{u, u} l E Y),
      sfIntegralConstructible l E Y L →
      sfIntegralConstructible l E X
        ((sfStabilityIntegralExceptionalAmbient D l hl E X Y f).obj L) ∧
      ∀ (a b : ℤ) (dX dY : ℕ),
        topologicalKrullDim X ≤ (dX : WithBot ℕ∞) →
        topologicalKrullDim Y ≤ (dY : WithBot ℕ∞) →
        (∀ n : ℕ, HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E Y n).obj L) a b) →
        ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((sfStabilityIntegralExceptionalAmbient D l hl E X Y f).obj L))
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))) := by
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfStabilityResidueInvertible D l hl X
  let : ∀ y : Y, Invertible (l : Y.residueField y) :=
    sfStabilityResidueInvertible D l hl Y
  have : LocallyOfFiniteType (X.asOver (Spec (.of D.k))).hom := ‹_›
  have : LocallyOfFiniteType (Y.asOver (Spec (.of D.k))).hom := ‹_›
  have : QuasiCompact (X.asOver (Spec (.of D.k))).hom := ‹_›
  have : QuasiCompact (Y.asOver (Spec (.of D.k))).hom := ‹_›
  have : IsSeparated (f.asOver (Spec (.of D.k))).left := ‹IsSeparated f›
  have : LocallyOfFiniteType (f.asOver (Spec (.of D.k))).left := ‹LocallyOfFiniteType f›
  have : QuasiCompact (f.asOver (Spec (.of D.k))).left := ‹QuasiCompact f›
  refine ⟨sfStabilityIntegralSupportConstructible D l hl E X Y f c, ?_⟩
  intro L hL
  let M := (sfStabilityIntegralVerdier D l hl E Y).obj (op L)
  have hM : sfIntegralConstructible l E Y M :=
    (finiteTor_stability_integral_verdier D l hl E Y).1 L hL
  let P := (integralDerivedPullback l E f).obj M
  have hP : sfIntegralConstructible l E X P :=
    ((integralOperations_preserve_constructible l E f).1 M hM).1
  refine ⟨(finiteTor_stability_integral_verdier D l hl E X).1 P hP, ?_⟩
  intro a b dX dY hdX hdY ht n
  have hMtor := sfStabilityIntegralVerdierTor D l hl E Y L hL n dY hdY a b (ht n)
  obtain ⟨c₀, d₀, hcd, hMred⟩ := hM.2
  have hfinite := sf_pullback_torAmplitude D l hl E (n + 1) (Nat.succ_pos n)
    (X.asOver (Spec (.of D.k))) (Y.asOver (Spec (.of D.k)))
    (f.asOver (Spec (.of D.k))) _ (hMred n).1
    (-b - 2 * (dY : ℤ)) (-a) hMtor
  let ep := sfStabilityIntegralPullbackReduction l E f M hM n
  have hPtor := sfStabilityTorOfIso X _ ep.symm _ _ hfinite.2
  have hX := sfStabilityIntegralVerdierTor D l hl E X P hP n dX hdX
    (-b - 2 * (dY : ℤ)) (-a) hPtor
  have ha : - -a - 2 * (dX : ℤ) = a - 2 * (dX : ℤ) := by omega
  have hb : -(-b - 2 * (dY : ℤ)) = b + 2 * (dY : ℤ) := by omega
  change HasProEtaleTorAmplitude X _
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj
      ((sfStabilityIntegralVerdier D l hl E X).obj (op P)))
    (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
  simpa only [ha, hb] using hX

/-- Restrict the actual coherent-limit support functor to its proved domain.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralSupport (c : Compactification f) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E X).ι ⋙ sfStabilityIntegralSupportAmbient D l hl E X Y f c)
    (fun K ↦ (finiteTor_stability_integral_images D l hl E X Y f c).1 K.obj K.property)

/-- Restrict the geometric duality composite to the integral constructible domain.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability). -/
noncomputable def sfStabilityIntegralExceptional :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X := by
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  letI : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  exact (sfIntegralConstructible l E X).lift
    ((sfIntegralConstructible l E Y).ι ⋙ sfStabilityIntegralExceptionalAmbient D l hl E X Y f)
    (fun L ↦ ((finiteTor_stability_integral_images D l hl E X Y f
      (NagataCompactification f)).2 L.obj L.property).1)

/-- The integral exceptional functor is the constructible right adjoint. Its finite
reductions are the finite exceptional functors, as natural comparisons of the actual
functors. The direct-limit coefficient passages are stated separately below.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).
Proof: form the adjunction on coherent normalized coefficient systems before taking
inverse limits. Its units and counits are the finite adjunction maps with their
quotient cocycles. The strict reduction/limit adjunction and normalized effectivity
transport this to integral constructible objects. Integral Verdier duality identifies
the resulting right adjoint with the displayed double-duality composite by Yoneda.
Finite evaluation of the coherent adjunction yields the natural reduction comparison. -/
theorem finiteTor_stability_integral_adjunction (c : Compactification f) :
    Nonempty (sfStabilityIntegralSupport D l hl E X Y f c ⊣
      sfStabilityIntegralExceptional D l hl E X Y f) ∧
    ∀ n : ℕ, Nonempty
      (sfStabilityIntegralExceptional D l hl E X Y f ⋙
          (sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
        (sfIntegralConstructible l E Y).ι ⋙ scalarReductionDerivedExtension.{u, u} l E Y n ⋙
          ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c) := by
  sorry

/-- Passage of the integral conclusions to the specified raw rational localization.
The natural isomorphisms fix the localized operations on objects and all localized
morphisms. In particular no new objects or idempotent completion are introduced.
The Hom-pair equalities say that the recorded general rational internal Hom is
permitted on every pair, without a site-perfectness condition.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the integral operations and duality are linear, so raw scalar localization
extends their functors and all structural maps uniquely. Localize the Hom adjunction
and the exceptional adjunction; the triangle identities and duality identities remain
identities after tensoring morphism groups with E. Exactness descends to the specified
image triangles. Every rational object has an integral representative, and integral
Hom preservation makes every rational pair permitted. The defining localization
comparisons give precisely the stated natural isomorphisms. -/
noncomputable def sfStabilityRationalConclusions (c : Compactification f) : Prop :=
    letI : ∀ x : X, Invertible (l : X.residueField x) := sfStabilityResidueInvertible D l hl X
    letI : ∀ y : Y, Invertible (l : Y.residueField y) := sfStabilityResidueInvertible D l hl Y
    constructibleRationalHomPairs l E X = ⊤ ∧
    constructibleRationalHomPairs l E Y = ⊤ ∧
    ∃ (F : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
      (G : sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l E X)
      (DX : (sfRationalConstructibleCategory l E X)ᵒᵖ ≌ sfRationalConstructibleCategory l E X)
      (DY : (sfRationalConstructibleCategory l E Y)ᵒᵖ ≌ sfRationalConstructibleCategory l E Y),
      Nonempty (sfRationalConstructibleLocalization l E X ⋙ F ≅
        sfStabilityIntegralSupport D l hl E X Y f c ⋙ sfRationalConstructibleLocalization l E Y) ∧
      Nonempty (sfRationalConstructibleLocalization l E Y ⋙ G ≅
        sfStabilityIntegralExceptional D l hl E X Y f ⋙ sfRationalConstructibleLocalization l E X) ∧
      Nonempty ((sfRationalConstructibleLocalization l E X).op ⋙ DX.functor ≅
        sfStabilityIntegralDual D l hl E X ⋙ sfRationalConstructibleLocalization l E X) ∧
      Nonempty ((sfRationalConstructibleLocalization l E Y).op ⋙ DY.functor ≅
        sfStabilityIntegralDual D l hl E Y ⋙ sfRationalConstructibleLocalization l E Y) ∧
      Nonempty (F ⊣ G) ∧
      Nonempty (G ≅ DY.functor.rightOp ⋙ (rationalDerivedPullback l E f).op ⋙ DX.functor) ∧
      IsExactAntiEquivalenceOn (⊤ : ObjectProperty (sfRationalConstructibleCategory l E X))
        DX.functor ∧
      IsExactAntiEquivalenceOn (⊤ : ObjectProperty (sfRationalConstructibleCategory l E Y))
        DY.functor

/-- Passage of the integral conclusions to the specified raw rational localization.
The natural isomorphisms fix the localized operations on objects and all localized
morphisms. In particular no new objects or idempotent completion are introduced.
The Hom-pair equalities say that the recorded general rational internal Hom is
permitted on every pair, without a site-perfectness condition.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: the integral operations and duality are linear, so raw scalar localization
extends their functors and all structural maps uniquely. Localize the Hom adjunction
and the exceptional adjunction; the triangle identities and duality identities remain
identities after tensoring morphism groups with E. Exactness descends to the specified
image triangles. Every rational object has an integral representative, and integral
Hom preservation makes every rational pair permitted. The defining localization
comparisons give precisely the stated natural isomorphisms. -/
theorem finiteTor_stability_rational (c : Compactification f) :
    sfStabilityRationalConclusions (D := D) (l := l) (hl := hl) (E := E)
      (X := X) (Y := Y) (f := f) c := by
  sorry

end Morphism

end Integral

section AlgebraicClosure

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The same conclusions at the specified algebraic closure of Q_l. The functors
are fixed on every finite stage by the actual integral operations and raw localization,
and hence on the filtered common-stage category. All pairs are permitted for the
recorded common-stage internal Hom. This uses neither arbitrary vector-space scalar
extension nor a Karoubi completion.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: at every finite field stage apply the rational passage statement. The canonical
finite-extension scalar comparisons identify pullback, tensor, general Hom, exceptional
image and geometric duality, respecting evaluation and the adjunction maps. Their identity
and composition laws give functors on common-stage pairs and their colimit Hom groups.
Every finite diagram is represented at one compositum stage; the rational adjunction,
exactness and biduality identities therefore hold in the common-stage category.
The displayed restriction isomorphisms identify these operations with the specified
coefficient-passage operations, and the duality formula descends in the same way. -/
noncomputable def sfStabilityAlgebraicClosureConclusions (c : Compactification f) : Prop :=
    letI : ∀ x : X, Invertible (l : X.residueField x) := sfStabilityResidueInvertible D l hl X
    letI : ∀ y : Y, Invertible (l : Y.residueField y) := sfStabilityResidueInvertible D l hl Y
    commonStageHomPairs l Ω X = ⊤ ∧ commonStageHomPairs l Ω Y = ⊤ ∧
    ∃ (F : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (G : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (DX : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ ≌
        generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (DY : (generalAlgebraicallyClosedConstructibleCategory l Ω Y)ᵒᵖ ≌
        generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      Nonempty (F ⊣ G) ∧
      Nonempty (G ≅ DY.functor.rightOp ⋙
        (commonStageDerivedPullback l Ω f).op ⋙ DX.functor) ∧
      IsExactAntiEquivalenceOn
        (⊤ : ObjectProperty (generalAlgebraicallyClosedConstructibleCategory l Ω X)) DX.functor ∧
      IsExactAntiEquivalenceOn
        (⊤ : ObjectProperty (generalAlgebraicallyClosedConstructibleCategory l Ω Y)) DY.functor ∧
      ∀ E₀ : Padic.FiniteCoefficientFields l Ω,
        let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀
        let iX := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E₀
        let iY := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E₀
        Nonempty (sfRationalConstructibleLocalization l E X ⋙ iX ⋙ F ≅
          sfStabilityIntegralSupport D l hl E X Y f c ⋙
            sfRationalConstructibleLocalization l E Y ⋙ iY) ∧
        Nonempty (sfRationalConstructibleLocalization l E Y ⋙ iY ⋙ G ≅
          sfStabilityIntegralExceptional D l hl E X Y f ⋙
            sfRationalConstructibleLocalization l E X ⋙ iX) ∧
        Nonempty ((sfRationalConstructibleLocalization l E X ⋙ iX).op ⋙ DX.functor ≅
          sfStabilityIntegralDual D l hl E X ⋙ sfRationalConstructibleLocalization l E X ⋙ iX) ∧
        Nonempty ((sfRationalConstructibleLocalization l E Y ⋙ iY).op ⋙ DY.functor ≅
          sfStabilityIntegralDual D l hl E Y ⋙ sfRationalConstructibleLocalization l E Y ⋙ iY)

/-- The same conclusions at the specified algebraic closure of Q_l. The functors
are fixed on every finite stage by the actual integral operations and raw localization,
and hence on the filtered common-stage category. All pairs are permitted for the
recorded common-stage internal Hom. This uses neither arbitrary vector-space scalar
extension nor a Karoubi completion.
Source: blueprint (vii) (blueprint: thm-sf-ctf-stability).

Proof: at every finite field stage apply the rational passage statement. The canonical
finite-extension scalar comparisons identify pullback, tensor, general Hom, exceptional
image and geometric duality, respecting evaluation and the adjunction maps. Their identity
and composition laws give functors on common-stage pairs and their colimit Hom groups.
Every finite diagram is represented at one compositum stage; the rational adjunction,
exactness and biduality identities therefore hold in the common-stage category.
The displayed restriction isomorphisms identify these operations with the specified
coefficient-passage operations, and the duality formula descends in the same way. -/
theorem finiteTor_stability_algebraicClosure (c : Compactification f) :
    sfStabilityAlgebraicClosureConclusions (D := D) (l := l) (hl := hl) (Ω := Ω)
      (X := X) (Y := Y) (f := f) c := by
  sorry

end AlgebraicClosure

end WeilConjectures

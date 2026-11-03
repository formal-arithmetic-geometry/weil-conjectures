/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteCoefficientSystemEvaluation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Logic.Small.Basic
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.Shrink

/-! # Bounded integral realization of normalized exceptional towers

Source: Bhatt--Scholze, Section 6.8, and sk-lem-sp-tower.
(blueprint: lem-sfb-coherent-exceptional-tower-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite-dimensional coefficient fields fit in the scheme universe.
Source: finite-extension hypothesis of sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization). -/
theorem coefficientFieldSmall (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : Small.{u} E := by
  exact small_of_injective (Module.finBasis ℚ_[l] E).repr.injective

/-- A finite coefficient extension has an algebraically identical small presentation.
Source: the universe-independent finite-extension hypothesis of sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: use the finite basis to shrink E, transfer its field and algebra
structures, and transport finite dimensionality across the resulting equivalence. -/
theorem smallCoefficientModel :
    ∃ F : Type u, ∃ hF : Field F, letI := hF
      ∃ hA : Algebra ℚ_[l] F, letI := hA
        FiniteDimensional ℚ_[l] F ∧ Nonempty (F ≃ₐ[ℚ_[l]] E) := by
  let : Small.{u} E := coefficientFieldSmall l E
  refine ⟨Shrink.{u} E, inferInstance, inferInstance, ?_, ⟨Shrink.algEquiv ℚ_[l] E⟩⟩
  exact (Shrink.algEquiv ℚ_[l] E).symm.toLinearEquiv.finiteDimensional

/-- Coefficient algebra equivalences preserve spectral absolute values.
Source: uniqueness of the finite-extension norm
(blueprint: lem-sfb-coherent-exceptional-tower-realization). -/
theorem coefficientNorm_algEquiv
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (e : F ≃ₐ[ℚ_[l]] E) (x : F) :
    Padic.coefficientExtensionAbsoluteValue l E (e x) =
      Padic.coefficientExtensionAbsoluteValue l F x := by
  let f := e.toRingEquiv.toRingHom
  let a : AbsoluteValue F ℝ :=
    { toFun := fun y ↦ Padic.coefficientExtensionAbsoluteValue l E (f y)
      map_mul' := fun y z ↦ by rw [map_mul, map_mul]
      nonneg' := fun y ↦ AbsoluteValue.nonneg _ _
      eq_zero' := fun y ↦ by
        rw [AbsoluteValue.eq_zero]
        exact map_eq_zero_iff f e.injective
      add_le' := fun y z ↦ by rw [map_add]; exact map_add_le_add _ _ _ }
  have ha : ∀ y : ℚ_[l], a (algebraMap ℚ_[l] F y) = ‖y‖ := by
    intro y
    change Padic.coefficientExtensionAbsoluteValue l E
      (e (algebraMap ℚ_[l] F y)) = ‖y‖
    rw [e.commutes]
    exact spectralNorm_extends (K := ℚ_[l]) (L := E) y
  exact spectralNorm_unique_field_norm_ext ha x

/-- Restrict a coefficient algebra equivalence to the spectral integer rings.
Source: coefficient presentation transport for sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: membership is spectral norm at most one. The norm identity identifies
these predicates. Restrict the two inverse algebra maps to the subrings. -/
theorem coefficientIntegerTransport
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (e : F ≃ₐ[ℚ_[l]] E) :
    ∃ eO : Padic.coefficientExtensionIntegers l F ≃+*
        Padic.coefficientExtensionIntegers l E,
      ∀ x, (eO x).val = e x.val := by
  have hF (x : F) := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := ℚ_[l]) (L := F))).choose_spec.choose_spec.1 x
  have hE (x : E) := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
  have hm (x : F) : x ∈ Padic.coefficientExtensionIntegers l F ↔
      e x ∈ Padic.coefficientExtensionIntegers l E := by
    change x ∈ (Padic.extension_integers_dvr l F
      (Padic.coefficientExtensionAbsoluteValue l F)
      (spectralNorm_extends (K := ℚ_[l]) (L := F))).choose ↔
      e x ∈ (Padic.extension_integers_dvr l E
        (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose
    rw [hF, hE, coefficientNorm_algEquiv l E F e x]
  refine ⟨{
    toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
    invFun := fun y ↦ ⟨e.symm y.val, (hm _).mpr (by simp)⟩
    left_inv := fun x ↦ by apply Subtype.ext; exact e.symm_apply_apply x.val
    right_inv := fun y ↦ by apply Subtype.ext; exact e.apply_symm_apply y.val
    map_mul' := fun x y ↦ by apply Subtype.ext; exact e.map_mul x.val y.val
    map_add' := fun x y ↦ by apply Subtype.ext; exact e.map_add x.val y.val }, fun _ ↦ rfl⟩

/-- The restricted coefficient equivalence preserves spectral distances.
Source: coefficient presentation transport for sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: distances are spectral norms of differences; apply the norm identity. -/
theorem coefficientIntegerTransport_isometry
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (e : F ≃ₐ[ℚ_[l]] E) :
    letI := spectralNorm.normedField ℚ_[l] F
    letI := spectralNorm.normedField ℚ_[l] E
    ∃ eO : Padic.coefficientExtensionIntegers l F ≃+*
        Padic.coefficientExtensionIntegers l E,
      (∀ x, (eO x).val = e x.val) ∧ Isometry eO := by
  let := spectralNorm.normedField ℚ_[l] F
  let := spectralNorm.normedField ℚ_[l] E
  obtain ⟨eO, heO⟩ := coefficientIntegerTransport l E F e
  refine ⟨eO, heO, ?_⟩
  apply Isometry.of_dist_eq
  intro x y
  change Padic.coefficientExtensionAbsoluteValue l E ((eO x).val - (eO y).val) =
    Padic.coefficientExtensionAbsoluteValue l F (x.val - y.val)
  rw [heO, heO]
  simpa only [Padic.coefficientExtensionAbsoluteValue,
      MulRingNorm.mulRingNormEquivAbsoluteValue_apply, spectralMulAlgNorm_def, map_sub] using
    coefficientNorm_algEquiv l E F e (x.val - y.val)

/-- Ring presentations induce the same positive ell-power quotient presentations.
Source: the coefficient quotients of sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: a ring equivalence preserves the natural-number scalar ell and powers;
therefore it maps the principal ideal generated by ell^(n+1) to that same ideal. -/
def positiveQuotientTransport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (n : ℕ) :
    R ⧸ Ideal.span {(l : R) ^ (n + 1)} ≃+*
      S ⧸ Ideal.span {(l : S) ^ (n + 1)} :=
  Ideal.quotientEquiv _ _ e (by simp [Ideal.map_span])

omit [Fact l.Prime] in
/-- Positive quotient presentation sends a residue class to its transported class.
Source: the coefficient quotients of sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization). -/
theorem positiveQuotientTransport_mk {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (n : ℕ) (x : R) :
    positiveQuotientTransport l e n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (e x) := rfl

omit [Fact l.Prime] in
/-- Positive quotient transport respects every original horizontal quotient map.
Source: the coefficient quotients of sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: both maps send the class of x to the class of e(x). Quotient induction
therefore identifies the ring homomorphisms, retaining the transition maps. -/
theorem positiveQuotientTransport_factor {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (m n : ℕ)
    (hR : Ideal.span {(l : R) ^ (m + 1)} ≤ Ideal.span {(l : R) ^ (n + 1)})
    (hS : Ideal.span {(l : S) ^ (m + 1)} ≤ Ideal.span {(l : S) ^ (n + 1)}) :
    (positiveQuotientTransport l e n).toRingHom.comp (Ideal.Quotient.factor hR) =
      (Ideal.Quotient.factor hS).comp (positiveQuotientTransport l e m).toRingHom := by
  ext x
  rfl

/-- A continuous ring presentation induces the actual continuous condensed-ring iso.
Source: coefficient presentation in sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: postcompose continuous functions on each profinite test with the two
inverse continuous ring maps. These inverse maps commute with restriction.
Sheafification transports their natural isomorphism. -/
def continuousPresentationIso {R S : Type (u + 1)} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    (e : R ≃+* S) (he : Continuous e) (hi : Continuous e.symm) :
    continuousPoint.{u} R ≅ continuousPoint.{u} S := by
  let eU (U : Profinite.{u}ᵒᵖ) : C(U.unop, R) ≃+* C(U.unop, S) :=
    { toFun := e.toRingHom.compLeftContinuous U.unop he
      invFun := e.symm.toRingHom.compLeftContinuous U.unop hi
      left_inv := fun f ↦ by ext x; exact e.symm_apply_apply (f x)
      right_inv := fun f ↦ by ext x; exact e.apply_symm_apply (f x)
      map_mul' := map_mul _
      map_add' := map_add _ }
  exact (presheafToSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).mapIso
    (NatIso.ofComponents (fun U ↦ (eU U).toCommRingCatIso) (by
      intros; ext f; rfl))

/-- The forward presentation is the published continuous postcomposition map.
Source: coefficient presentation in sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization). -/
theorem continuousPresentationIso_hom {R S : Type (u + 1)} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    (e : R ≃+* S) (he : Continuous e) (hi : Continuous e.symm) :
    (continuousPresentationIso e he hi).hom = continuousPointMap e.toRingHom he := rfl

/-- Continuous coefficient postcomposition preserves composition before sheafification.
Source: coefficient transport in sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: the two presheaf maps agree on each continuous function; apply functoriality
of sheafification. -/
theorem continuousPointMap_comp {R S T : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsTopologicalRing T]
    (f : R →+* S) (g : S →+* T) (hf : Continuous f) (hg : Continuous g) :
    continuousPointMap (g.comp f) (hg.comp hf) =
      continuousPointMap f hf ≫ continuousPointMap g hg := by
  unfold continuousPointMap
  rw [← Functor.map_comp]
  rfl

/-- The constructed coefficient presentation isomorphisms preserve composition.
Source: coefficient transport in sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: their forward maps are the published continuous postcomposition maps;
apply continuousPointMap_comp and extensionality of isomorphisms. -/
theorem continuousPresentationIso_trans {R S T : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsTopologicalRing T]
    (e : R ≃+* S) (f : S ≃+* T)
    (he : Continuous e) (hi : Continuous e.symm)
    (hf : Continuous f) (hj : Continuous f.symm) :
    continuousPresentationIso (e.trans f) (hf.comp he) (hi.comp hj) =
      continuousPresentationIso e he hi ≪≫ continuousPresentationIso f hf hj := by
  apply Iso.ext
  simp only [Iso.trans_hom, continuousPresentationIso_hom]
  exact continuousPointMap_comp e.toRingHom f.toRingHom he hf

/-- The actual coherent sequence category has the exact strict-system presentation.
Source: Zheng Construction 4.1, applied to the coefficient diagram in sk-lem-sp-tower
(blueprint: lem-sfb-coherent-exceptional-tower-realization).
Proof: apply the sectionwise strict-system/sequence-site equivalence to the actual
coherent coefficient diagram. Both directions preserve finite products, hence
are additive. Exact equivalences descend to inverse derived equivalences. -/
def coherentStrictSequenceEquivalence (X : Scheme.{u}) :
    DerivedCategory (SheafOfModules.StrictRingSystem.{u + 1, u, u + 1}
      (rings (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X))) ≌
        DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (coefficients l E X) (transitions l E X) := by
  let e := SheafOfModules.strictSystemSequenceEquivalence
    (rings (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X))
  let : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact e.mapDerivedCategory

/-- A genuine normalized quotient system with a bounded constructible finite-Tor
first level is the reduction of a functorial bounded constructible integral object.

Source: sk-lem-sp-tower and the normalization and uniform-bounds paragraph of
lem-sfb-dc-proper-pushforward-left-adjoint-oe.
(blueprint: lem-sfb-coherent-exceptional-tower-realization)

Proof: transport the section-ring realization through the exact internal-module
and sheaf-of-modules equivalences, and identify the ell-power quotients with the
quotients in sk-lem-sp-tower. The scalar-adjunction definition identifies the
specified fixedReduction maps with the actual tower reduction maps. Their
invertibility gives normalization. Finite Tor amplitude of the first level
and its finite stratification give common Tor and cohomological bounds at every
level. For any module over a later quotient, its finite ell-power filtration
has first-quotient modules as subquotients. Tensor associativity and the first
Tor interval bound their derived tensors, and exact triangles give the same
interval for the whole module. This also bounds ordinary cohomology. Lift finite
presentations on each stratum through the nilpotent quotients to obtain
constructibility on that same finite stratification.
The Noetherian hypothesis permits the bounded normalized tower equivalence of
sk-lem-sp-tower. Apply its total inverse-limit functor to C. Its limit-closure
statement gives bounded constructibility; its actual counit, with the preceding
quotient identifications, gives the asserted natural isomorphism. The functor
is therefore constructed by total derived limit, and the comparison retains
the transitions of the input derived system. Empty schemes and zero inputs
require no exceptions.
-/
theorem coherent_exceptional_tower_realization
    {Z Y : Scheme.{u}} [IsNoetherian Z]
    (C : Bc l E Y ⥤ DS.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Z) (coefficients l E Z) (transitions l E Z))
    (hnorm : ∀ (K : Bc l E Y) {m n : ℕ} (h : n ≤ m),
      IsIso (fixedReduction l E Z h (C.obj K)))
    (hfirst : ∀ K : Bc l E Y,
      ∃ L : Etale.DerivedCategoryModule (Etale.FiniteProperQuotient.Ring l E 0) Z,
        Etale.FiniteProperQuotient.Ctf l E Z 0 L ∧
        Nonempty ((fixedDerivedEvaluation l E Z 0).obj (C.obj K) ≅
          (nu l E Z 0).obj L)) :
    ∃ H : Bc l E Y ⥤ Bc l E Z,
      Nonempty (H ⋙ reductionBc l E Z ≅ C) := by
  sorry

end AlgebraicGeometry.ProEtale.CoherentReduction

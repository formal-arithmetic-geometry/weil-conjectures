/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
/-! # Ordinary coefficient comparison through a locally closed immersion

Source: thm-coef-finite-hom, proof paragraph 4.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

private lemma coefficient_hasInvertibleExponent_local
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) (aT : T ⟶ Spec (.of D.k)) :
    HasInvertibleExponent (coefficient l E ⟨n, hn⟩) T := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hv : Padic.coefficientExtensionAbsoluteValue l E (D.p : E) = 1 := by
    have he := spectralNorm_extends (K := Padic l) (L := E) (D.p : Padic l)
    have hn' : ‖(D.p : Padic l)‖ = 1 := Padic.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes (Fact.out : l.Prime) D.prime).2 hl)
    change spectralNorm (Padic l) E (D.p : E) = 1
    simpa only [map_natCast, hn'] using he
  have hu : IsUnit (D.p : Padic.coefficientExtensionIntegers l E) :=
    (h.2.2.1 _).2 hv
  have hq : IsUnit (D.p : Padic.coefficientExtensionRing l E n) := by
    simpa using hu.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  letI : CharP D.k D.p := charP_of_injective_algebraMap
    (algebraMap D.k₀ D.k).injective D.p
  have hqu : IsUnit (D.p : coefficient l E ⟨n, hn⟩) := by
    exact hq.map (ULift.ringEquiv.symm.toRingHom)
  letI : Invertible (D.p : coefficient l E ⟨n, hn⟩) := hqu.invertible
  letI : HasInvertibleExponent (coefficient l E ⟨n, hn⟩) (Spec (.of D.k)) :=
    HasInvertibleExponent.spec_of_charP _ D.p
  exact HasInvertibleExponent.of_hom aT
/-- The ordinary comparison through an open then closed immersion is invertible on the
finite-Tor bounded constructible internal Hom object.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-locally-closed-ordinary-comparison-iso).
Proof: apply the finite-coefficient direct-image comparison to the composite `j ≫ g`,
then cancel the canonical direct-image compositor using `finiteCoefficientDirectImageMap_comp`.
The geometric hypotheses are discharged by the Noetherian, separated and finite-type
assumptions on the immersion and by the finite-Tor constructibility of the object. -/
theorem locallyClosedOrdinaryComparison_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n) {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (Q : DerivedCategoryModule (coefficient l E n) S)
    (hQ : WeilConjectures.finiteTorConstructibleEtale l E n n.property S Q) :
    IsIso (ordinaryComparison (reduction l E n m hmn) g j Q) := by
  classical
  let A := coefficient l E n
  let B := coefficient l E m
  let φ : A →+* B := reduction l E n m hmn
  letI : Algebra A B := φ.toAlgebra
  letI : Module.Finite A B := Module.Finite.of_finite
  let aX : X ⟶ Spec (.of D.k) := X ↘ Spec (CommRingCat.of D.k)
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  letI : IsNoetherian X := by
    exact { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  letI : IsNoetherian Z := by
    let aZ : Z ⟶ Spec (.of D.k) := g ≫ aX
    exact { __ := LocallyOfFiniteType.isLocallyNoetherian aZ }
  letI : TopologicalSpace.NoetherianSpace S :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  letI : QuasiCompact j := inferInstance
  letI : HasInvertibleExponent A Z :=
    coefficient_hasInvertibleExponent_local D l _hl E n n.property Z (g ≫ aX)
  have hcomp : IsIso (finiteCoefficientDirectImageMap φ (j ≫ g) Q) := by
    let SOver : Over (Spec (CommRingCat.of D.k)) := Over.mk (j ≫ g ≫ aX)
    let XOver : Over (Spec (CommRingCat.of D.k)) := Over.mk aX
    let fOver : SOver ⟶ XOver := Over.homMk (j ≫ g) rfl
    letI : LocallyOfFiniteType SOver.hom := inferInstanceAs (LocallyOfFiniteType (j ≫ g ≫ aX))
    letI : QuasiCompact SOver.hom := inferInstanceAs (QuasiCompact (j ≫ g ≫ aX))
    letI : LocallyOfFiniteType XOver.hom := inferInstanceAs (LocallyOfFiniteType aX)
    letI : QuasiCompact XOver.hom := inferInstanceAs (QuasiCompact aX)
    letI : IsSeparated fOver.left := inferInstanceAs (IsSeparated (j ≫ g))
    letI : LocallyOfFiniteType fOver.left := inferInstanceAs (LocallyOfFiniteType (j ≫ g))
    letI : QuasiCompact fOver.left := inferInstanceAs (QuasiCompact (j ≫ g))
    have hQOver : @DerivedCategory.isBoundedConstructible.{u} A inferInstance
        (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property))
        S Q := hQ.1
    have hTOver : ∃ a b : ℤ, a ≤ b ∧
        DerivedCategory.hasTorAmplitudeIn A S a b Q := hQ.2
    exact finiteCoefficientDirectImageMap_isIso D l _hl E n n.property B SOver XOver fOver Q
      hQOver hTOver
  have hcomp_eq := finiteCoefficientDirectImageMap_comp φ j g Q
  let cA := (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) j g).symm.hom.app Q
  let cB := (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) j g).symm.inv.app
    ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (S.smallEtaleTopology) φ).obj Q)
  haveI : IsIso cA := by dsimp [cA]; infer_instance
  haveI : IsIso cB := by dsimp [cB]; infer_instance
  have hmid : IsIso (ordinaryComparison φ g j Q) := by
    let middle := ordinaryComparison φ g j Q
    change IsIso middle
    let dA :=
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
        (X.smallEtaleTopology) φ).map cA
    haveI : IsIso dA := by dsimp [dA]; infer_instance
    have hfull : IsIso (dA ≫ (middle ≫ cB)) := by
      have heq : dA ≫ (middle ≫ cB) =
          finiteCoefficientDirectImageMap φ (j ≫ g) Q := by
        dsimp [dA, middle, ordinaryComparison]
        simpa only [Category.assoc] using hcomp_eq.symm
      rw [heq]
      exact hcomp
    letI : IsIso (dA ≫ (middle ≫ cB)) := hfull
    have hmiddleRight : IsIso (middle ≫ cB) :=
      IsIso.of_isIso_comp_left dA (middle ≫ cB)
    letI : IsIso (middle ≫ cB) := hmiddleRight
    exact IsIso.of_isIso_comp_right middle cB
  simpa only [CoefficientPairingChange.ordinaryComparison, φ, A, B] using hmid
end AlgebraicGeometry.Etale

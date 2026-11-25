/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedCoefficientModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit

/-! # Comparing the given unit ball with the canonical integral coefficient limit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace WeilConjectures.NormalizedScalar

/-- A homeomorphic ring isomorphism `A ≃+* B` induces, by postcomposition, an isomorphism of
the sheaves of continuous `A`-valued and `B`-valued functions on profinite sets. -/
def coefficientRingIso {A : Type u} {B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousCoefficientRingSheaf B :=
  { hom := ⟨
      { app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous _ he).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
    inv := ⟨
      { app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous _ hei).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
    hom_inv_id := by
      ext S f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      exact e.symm_apply_apply (f.down x)
    inv_hom_id := by
      ext S f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      exact e.apply_symm_apply (f.down x) }



variable (l : ℕ) [Fact l.Prime] (E : Type u) [hE : NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The metric of the spectral norm on the finite extension `E` of `ℚ_[l]` equals the metric
of the given norm. -/
theorem spectralMetric_eq :
    (spectralNorm.normedField ℚ_[l] E).toMetricSpace = hE.toMetricSpace := by
  apply MetricSpace.ext
  apply Dist.ext
  funext a b
  rw [(spectralNorm.normedField ℚ_[l] E).dist_eq, hE.dist_eq]
  exact (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (-a + b)).symm

/-- The unit ball of the given norm on `E` is the canonical ring of integers of `E`. -/
theorem integers_eq : integers l E = Padic.coefficientExtensionIntegers l E := by
  ext x
  rw [Padic.mem_coefficientExtensionIntegers]
  change ‖x‖₊ ≤ 1 ↔ spectralNorm ℚ_[l] E x ≤ 1
  rw [← NNReal.coe_le_coe]
  change ‖x‖ ≤ 1 ↔ spectralNorm ℚ_[l] E x ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[l]]

/-- The condensed ring of continuous functions valued in the unit ball of the given norm is
isomorphic, as a monoid object, to the canonical condensed ring of integers of `E`. -/
def canonicalIntegersIso :
    Mon.mk (Profinite.continuousCoefficientRingObj (integers l E)) ≅
      sfbCondensedIntegers l E := by
  have ht := congrArg
    (fun m : MetricSpace E ↦ m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (spectralMetric_eq l E)
  let A := integers l E
  let B := Padic.coefficientExtensionIntegers l E
  let tb : TopologicalSpace B := Padic.coefficientExtensionIntegersTopology l E
  have htb : tb = TopologicalSpace.induced (fun b : B ↦ (b : E))
      hE.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    congrArg (TopologicalSpace.induced (fun b : B ↦ (b : E))) ht
  letI : TopologicalSpace B := tb
  letI : IsTopologicalRing B := by
    change @IsTopologicalRing B tb _
    rw [htb]
    infer_instance
  let e : A ≃+* B := RingEquiv.subringCongr (integers_eq l E)
  have he : Continuous e := by
    change @Continuous A B _ tb e
    rw [htb]
    apply continuous_induced_rng.2
    exact continuous_subtype_val
  have hei : Continuous e.symm := by
    change @Continuous B A tb _ e.symm
    rw [htb]
    apply continuous_induced_rng.2
    exact continuous_subtype_val
  let er := coefficientRingIso e he hei
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) er.hom
  exact Mon.mkIso ea (IsMonHom.one_hom ea.hom) (IsMonHom.mul_hom ea.hom)

/-- The statement that the unit-ball coefficients agree with the canonical condensed integers
and that the integral coefficient sheaf on `T` is the limit of its finite quotients, compatibly
with the canonical finite-quotient representations. -/
def IntegralLimit (T : Scheme.{u}) : Prop :=
    Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj (integers l E)) ≅
      sfbCondensedIntegers l E) ∧
    (∃ a : sfbFiniteConstantSets T ≅ sfbFiniteRepresentables T,
      ∃ (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
        (j : sfbIntegralProfinite l E ≅ c.pt),
        (∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
          (j.hom ≫ c.π.app (op n)) x =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
        Nonempty (IsLimit c) ∧
        Nonempty (IsLimit ((profiniteToProEtOf T ⋙ Scheme.ProEt.forget T ⋙
          Over.forget T).mapCone c)) ∧
        Nonempty (((sfbPullbackFromPoint T).obj (sfbCondensedIntegers l E).X).obj ⋙
          forget Ab.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf T).obj (sfbIntegralProfinite l E))) ∧
        Nonempty ((completedIntegralCoefficientSheafUnrestricted l E T).obj ⋙
          forget RingCat.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf T).obj (sfbIntegralProfinite l E))) ∧
        ∃! e : (coefficientRing T (sfbCondensedIntegers l E)).X ≅
            sfbCompletedIntegersAb l E T,
          (IsMonHom e.hom ∧ IsMonHom e.inv ∧
          ∀ (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E) (n : ℕ),
            (sfbIntegralFiniteRepresentation l E T a n).hom.app
                (op ((profiniteToProEtOf T).obj S))
              (((limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app
                  (op ((profiniteToProEtOf T).obj S)))
                ((e.hom.hom.app (op ((profiniteToProEtOf T).obj S)))
                  (((sfbIntegralPointAdjunction T).unit.app (sfbCondensedIntegers l E).X).hom.app
                    (op S) (ULift.up f.hom.hom)))) =
              ULift.up ((profiniteToProEtOf T).map (f ≫ j.hom ≫ c.π.app (op n)))))

/-- The statement `IntegralLimit l E T` holds for every scheme `T`. -/
theorem integral_limit (T : Scheme.{u}) :
    IntegralLimit l E T := by
  exact ⟨⟨canonicalIntegersIso l E⟩, sfb_integral_coefficient_limit l E T⟩

end WeilConjectures.NormalizedScalar

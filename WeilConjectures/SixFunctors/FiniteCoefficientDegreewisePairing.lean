/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology
import WeilConjectures.SixFunctors.ScalarCompositionPairing
import WeilConjectures.AlgebraicGeometry.CoefficientFrobenius
import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
import Mathlib.Algebra.Module.Shrink
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.NativeHomSourceShiftData

/-! # Degreewise duality for finite Frobenius coefficients

Source: current smooth identification proof, finite-coefficient complement.
(blueprint: lem-sf-finite-coefficient-degreewise-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalClosed
open scoped TensorProduct
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.SixFunctors

attribute [local instance] RingHomInvPair.of_ringEquiv

-- Evaluation commutes with a semilinear equivalence and its two dual equivalences.
private lemma reflexive_transport {A R M N : Type*} [CommRing A] [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module R N]
    (e : A ≃+* R) (f : M ≃ₛₗ[RingHomClass.toRingHom e] N) [Module.IsReflexive A M] :
    Module.IsReflexive R N := by
  let d : Module.Dual A M ≃ₛₗ[RingHomClass.toRingHom e] Module.Dual R N :=
    LinearEquiv.arrowCongr f e.toSemilinearEquiv
  let dd : Module.Dual A (Module.Dual A M) ≃ₛₗ[RingHomClass.toRingHom e]
      Module.Dual R (Module.Dual R N) :=
    LinearEquiv.arrowCongr d e.toSemilinearEquiv
  have h : (Module.Dual.eval R N : N → Module.Dual R (Module.Dual R N)) =
      dd ∘ Module.Dual.eval A M ∘ f.symm := by
    funext n
    ext g
    simp [dd, d]
  refine ⟨?_⟩
  rw [h]
  exact dd.bijective.comp ((Module.bijective_dual_eval A M).comp f.symm.bijective)

-- The coefficient theorem lives in universe zero; its finite carriers can be shrunk.
private lemma coefficient_reflexive (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (R : Type (u + 1)) [CommRing R]
    (e : Padic.coefficientExtensionRing ell E n ≃+* R)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] : Module.IsReflexive R M := by
  let A := Padic.coefficientExtensionRing ell E n
  have : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  have : Finite R := Finite.of_equiv A e.toEquiv
  have : Finite M := Module.finite_of_finite R
  let : Module A M := Module.compHom M (RingHomClass.toRingHom e)
  let f : Shrink.{0} M ≃ₛₗ[RingHomClass.toRingHom e] M :=
    { (Shrink.linearEquiv.{0} A M).toAddEquiv with
      map_smul' := (Shrink.linearEquiv.{0} A M).map_smul }
  have : Module.Finite A (Shrink.{0} M) :=
    Module.Finite.of_surjective f.symm.toLinearMap f.symm.surjective
  have : Module.IsReflexive A (Shrink.{0} M) :=
    ⟨((WeilConjectures.coefficient_frobenius ell E n hn).1.2.2.2.1
      (ModuleCat.of A (Shrink.{0} M)) inferInstance).2⟩
  exact reflexive_transport e f

-- Every coherent covering sieve of the terminal profinite set contains its identity.
private lemma point_cover (S : Sieve (⊤_ Profinite.{u}))
    (hS : S ∈ coherentTopology Profinite.{u} (⊤_ Profinite.{u})) : S (𝟙 _) := by
  obtain ⟨α, hα, Y, π, hπ, hmem⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S).mp hS
  have := hα
  have hsurj : ∀ b : (⊤_ Profinite.{u}), ∃ a x, π a x = b :=
    ((Profinite.effectiveEpiFamily_tfae Y π).out 0 2).mp hπ
  obtain ⟨a, x, _⟩ := hsurj ((terminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit)
  let s : (⊤_ Profinite.{u}) ⟶ Y a := CompHausLike.ofHom _ ⟨fun _ ↦ x, continuous_const⟩
  have h : s ≫ π a = 𝟙 _ := terminalIsTerminal.hom_ext _ _
  exact h ▸ S.downward_closed (hmem a) s

private lemma constant_point_unit (A : Type) [CommRing A] :
    IsIso ((constantSheafAdj (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
      terminalIsTerminal).unit.app (CommRingCat.of (ULift.{u + 1} A))) := by
  let J := coherentTopology Profinite.{u}
  let G := (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))
  change IsIso ((toSheafify J G).app (op (⊤_ Profinite.{u})))
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y h
    simpa using point_cover _ (Presheaf.equalizerSieve_mem J (toSheafify J G) x y h)
  · intro s
    obtain ⟨t, ht⟩ := point_cover _ (Presheaf.imageSieve_mem J (toSheafify J G) s)
    exact ⟨t, by simpa using ht⟩

-- Reconstructing a ring from its sheaf monoid retains its native multiplication.
private def section_reconstruction_equiv (A : Type) [CommRing A] :
    ((constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A))).obj.obj (op (⊤_ Profinite.{u})) ≃+*
      condensedScalarRing (IntegralModelsEmbedded.discreteObj.{u} A) := by
  letI : MonObj (IntegralModelsEmbedded.discreteObj.{u} A).obj :=
    (IntegralModelsEmbedded.discreteSheaf.{u} A).obj.monObjCompForget₂
  refine { Equiv.refl _ with map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
  intro a b
  exact (congrArg (fun f ↦ (f.app (op (⊤_ Profinite.{u}))).hom
    (a ⊗ₜ[ℤ] b)) (Sheaf.μ_comp_map_mul
      (IntegralModelsEmbedded.discreteObj.{u} A))).symm

private def discrete_scalar_equiv (A : Type) [CommRing A] :
    A ≃+* condensedScalarRing (IntegralModelsEmbedded.discreteObj.{u} A) := by
  have := constant_point_unit.{u} A
  exact ULift.ringEquiv.symm.trans ((CategoryTheory.Iso.commRingCatIsoToRingEquiv (asIso
    ((constantSheafAdj (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
      terminalIsTerminal).unit.app (CommRingCat.of (ULift.{u + 1} A))))).trans
        (section_reconstruction_equiv.{u} A))

private def scalar_equiv (Λ : ScalarSixRing.{u}) (A : Type) [CommRing A]
    (e : Mon.mk Λ.X ≅ Mon.mk (IntegralModelsEmbedded.discreteObj.{u} A)) :
    condensedScalarRing Λ.X ≃+* condensedScalarRing (IntegralModelsEmbedded.discreteObj.{u} A) := by
  let F := (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon ⋙
    ((Monoidal.monFunctorCategoryEquivalence Profinite.{u}ᵒᵖ Ab.{u + 1}).functor) ⋙
    (Functor.whiskeringRight _ _ _).obj InternalAbelianSheafModule.monToRing ⋙
    (evaluation _ RingCat.{u + 1}).obj (op (⊤_ Profinite.{u}))
  exact CategoryTheory.Iso.ringCatIsoToRingEquiv (F.mapIso e)

section
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
-- Transport the tensor-Hom adjunction using the prescribed native shift comparisons.
private def shiftedAdj (P : D) (i : ℤ) :
    tensorLeft (P⟦i⟧) ⊣ ihom P ⋙ shiftFunctor D (-i) :=
  ((shiftEquiv D i).toAdjunction.comp (ihom.adjunction P)).ofNatIsoLeft
    ((tensorLeft P).commShiftIso i ≪≫ (siteHomTensorParameterShift P i).symm)

private def tensorCancel (P Q : D) (i : ℤ) : P⟦i⟧ ⊗ Q⟦-i⟧ ≅ P ⊗ Q :=
  (siteHomTensorParameterShift P i).app (Q⟦-i⟧) ≪≫
    (shiftFunctor D i).mapIso (((tensorLeft P).commShiftIso (-i)).app Q) ≪≫
    (shiftFunctorCompIsoId D (-i) i (neg_add_cancel i)).app (P ⊗ Q)

private lemma shiftedAdj_evaluation {P Q : D} (b : P ⊗ Q ⟶ 𝟙_ D) (i : ℤ) :
    ((shiftedAdj P i).homEquiv (Q⟦-i⟧) (𝟙_ D)).symm
        ((shiftFunctor D (-i)).map (curry b)) = (tensorCancel P Q i).hom ≫ b := by
  let H := (ihom P).obj (𝟙_ D)
  let c := shiftFunctorCompIsoId D (-i) i (neg_add_cancel i)
  have hc : (shiftFunctor D i).map ((shiftFunctor D (-i)).map (curry b)) ≫
      c.hom.app H = c.hom.app Q ≫ curry b := c.hom.naturality (curry b)
  change (tensorLeft (P⟦i⟧)).map ((shiftFunctor D (-i)).map (curry b)) ≫
    (shiftedAdj P i).counit.app (𝟙_ D) = _
  simp only [shiftedAdj, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Adjunction.comp_counit_app, Functor.comp_obj]
  change (tensorLeft (P⟦i⟧)).map ((shiftFunctor D (-i)).map (curry b)) ≫
    (siteHomTensorParameterShift P i).hom.app (H⟦-i⟧) ≫
    ((tensorLeft P).commShiftIso i).inv.app (H⟦-i⟧) ≫
    (tensorLeft P).map (c.hom.app H) ≫ (ihom.ev P).app (𝟙_ D) = _
  have hp := (siteHomTensorParameterShift P i).hom.naturality
    ((shiftFunctor D (-i)).map (curry b))
  dsimp only [Functor.comp_map] at hp
  rw [reassoc_of% hp]
  have ht := ((tensorLeft P).commShiftIso i).inv.naturality
    ((shiftFunctor D (-i)).map (curry b))
  dsimp only [Functor.comp_map] at ht
  rw [reassoc_of% ht]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp]
  simp only [c, Functor.map_shiftFunctorCompIsoId_hom_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  change _ ≫ _ ≫ _ ≫ (P ◁ curry b ≫ (ihom.ev P).app (𝟙_ D)) = _
  rw [whiskerLeft_curry_ihom_ev_app]
  simp [tensorCancel, Category.assoc]

private lemma shiftedPairing_perfect {P Q : D} (b : P ⊗ Q ⟶ 𝟙_ D)
    (hb : IsPerfectPairing b) (i : ℤ) :
    IsPerfectPairing ((tensorCancel P Q i).hom ≫ b) := by
  let a := shiftedAdj P i
  let e := (ihom.adjunction (P⟦i⟧)).rightAdjointUniq a
  have heval : a.homEquiv _ _ ((tensorCancel P Q i).hom ≫ b) =
      (shiftFunctor D (-i)).map (curry b) := by
    apply (a.homEquiv _ _).symm.injective
    simpa using (shiftedAdj_evaluation b i).symm
  have h : curry ((tensorCancel P Q i).hom ≫ b) ≫ e.hom.app (𝟙_ D) =
      a.homEquiv _ _ ((tensorCancel P Q i).hom ≫ b) := by
    simp only [curry_eq, Adjunction.homEquiv_unit]
    rw [Category.assoc, e.hom.naturality]
    rw [← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (ihom P ⋙ shiftFunctor D (-i)).map
      ((tensorCancel P Q i).hom ≫ b)) (Adjunction.unit_rightAdjointUniq_hom_app
        (ihom.adjunction (P⟦i⟧)) a (Q⟦-i⟧))
  have := hb.isIso
  have : IsIso (curry ((tensorCancel P Q i).hom ≫ b) ≫ e.hom.app (𝟙_ D)) := by
    rw [h, heval]
    infer_instance
  exact ⟨IsIso.of_isIso_comp_right _ (e.hom.app (𝟙_ D))⟩
end

-- The generic cancellation is exactly the signed comparison in the degree value.
@[reassoc] private lemma native_cancel {R : Type (u + 1)} [CommRing R]
    (P Q : DerivedCategory (ModuleCat.{u + 1} R)) (i : ℤ) :
    (DerivedCategory.shiftTensorShiftIso (ModuleCat.{u + 1} R) P Q i (-i)).hom ≫
      (shiftFunctorZero' _ (i + -i) (add_neg_cancel i)).hom.app (P ⊗ Q) =
        (tensorCancel P Q i).hom := by
  simp [DerivedCategory.shiftTensorShiftIso, tensorCancel, siteHomTensorParameterShift,
    shiftFunctorCompIsoId, shiftFunctorAdd', shiftFunctorZero']

-- Closed adjunction for the shifted pairing, followed by the right unitor.
private def degreeHomEquiv {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (b : P ⊗ Q ⟶ 𝟙_ _) (hb : IsPerfectPairing b) (i : ℤ) :
    (𝟙_ _ ⟶ Q⟦-i⟧) ≃ₗ[R] (P⟦i⟧ ⟶ 𝟙_ _) := by
  let hs := shiftedPairing_perfect b hb i
  let e := (Linear.homCongr R (Iso.refl _) hs.iso).toEquiv |>.trans
    ((ihom.adjunction (P⟦i⟧)).homEquiv (𝟙_ _) (𝟙_ _)).symm |>.trans
      (Linear.homCongr R (ρ_ (P⟦i⟧)) (Iso.refl _)).toEquiv
  refine { e with map_add' := ?_, map_smul' := ?_ }
  · intro x y
    simp [e, Linear.homCongr_apply, Adjunction.homEquiv,
      MonoidalCategory.whiskerLeft_comp, Preadditive.comp_add, Preadditive.add_comp,
      MonoidalPreadditive.whiskerLeft_add]
  · intro r y
    simp [e, Linear.homCongr_apply, Adjunction.homEquiv,
      MonoidalCategory.whiskerLeft_comp, Linear.smul_comp,
      MonoidalLinear.whiskerLeft_smul]

private lemma degreeHomEquiv_apply {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (b : P ⊗ Q ⟶ 𝟙_ _) (hb : IsPerfectPairing b) (i : ℤ)
    (y : 𝟙_ _ ⟶ Q⟦-i⟧) :
    degreeHomEquiv b hb i y = (ρ_ (P⟦i⟧)).inv ≫ P⟦i⟧ ◁ y ≫
      (tensorCancel P Q i).hom ≫ b := by
  simp [degreeHomEquiv, Linear.homCongr_apply, Adjunction.homEquiv,
    IsPerfectPairing.iso, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ihom.ihom_adjunction_counit, whiskerLeft_curry_ihom_ev_app]

private lemma degreeHomEquiv_value {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (b : P ⊗ Q ⟶ 𝟙_ _) (hb : IsPerfectPairing b) (i : ℤ)
    (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q⟦-i⟧) :
    x ≫ degreeHomEquiv b hb i y =
      WeilConjectures.SixFunctors.identificationDegreeValue b i x y := by
  rw [degreeHomEquiv_apply]
  simp only [identificationDegreeValue, native_cancel_assoc]
  rw [← MonoidalCategory.rightUnitor_inv_comp_tensorHom_assoc, unitors_inv_equal]

/-- A perfect scalar derived pairing over a presented finite coefficient quotient
induces the specified perfect bilinear form in every complementary degree.
Source: current blueprint sk-thm-sf-identification.proof.md, complement
(blueprint: lem-sf-finite-coefficient-degreewise-pairing).

Proof: terminal sections of the coefficient presentation identify the scalar ring
with the finite Frobenius quotient A(E,n). Transport self-injectivity and
finite-module biduality from coefficient_frobenius along this ring isomorphism.
For each i, the native signed tensor-shift comparison transports the perfect
pairing to P[i] tensor Q[-i]. The closed adjunction and the right unitor identify
Hom(1,Q[-i]) with Hom(P[i],1). Its evaluation on x,y is the degree value in the
statement, by unitor naturality. A perfect scalar complex has finite cohomology;
finite-module biduality therefore makes H0(P[i]) reflexive. Apply
scalarCompositionPairing to P[i] and transport that perfect bilinear form by the
closed-adjunction linear isomorphism in the second variable. The scalar value
uses the same regular-unit and H0 identifications, so its value is precisely the
specified identificationScalarValue. No field assumption on A(E,n), no freeness
of its cohomology modules, and no restriction on the integer i is used. -/
theorem finiteCoefficientDegreewisePairing
    (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u})
    (hΛ : ∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
      Nonempty (Mon.mk Λ.X ≅ Mon.mk
        (IntegralModelsEmbedded.discreteObj (Padic.coefficientExtensionRing ell E n))))
    {P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))}
    (b : P ⊗ Q ⟶ 𝟙_ _) (hP : DerivedCategory.IsPerfectRingComplex P)
    (hb : MonoidalClosed.IsPerfectPairing b) : IdentificationDegreewise b := by
  obtain ⟨E, n, hn, ⟨eΛ⟩⟩ := hΛ
  let A := Padic.coefficientExtensionRing ell E n
  let R := condensedScalarRing Λ.X
  let eR : A ≃+* R :=
    (discrete_scalar_equiv A).trans (scalar_equiv Λ A eΛ).symm
  have : Module.Injective A A := (WeilConjectures.coefficient_frobenius ell E n hn).1.1
  have : Module.Injective R R := Module.Injective.of_ringEquiv eR eR.toSemilinearEquiv
  have : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  have : Finite R := Finite.of_equiv A eR.toEquiv
  have : IsNoetherianRing R := isNoetherian_of_finite R R
  have hp : DerivedCategory.IsPerfect P := hP
  intro i
  have : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj (P⟦i⟧)) :=
    (hp.shift i).finite_homology 0
  have := coefficient_reflexive ell E n hn R eR
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj (P⟦i⟧))
  obtain ⟨B, hval, hB⟩ := scalarCompositionPairing R (P⟦i⟧)
  let e := degreeHomEquiv b hb i
  let e₁ : (𝟙_ _ ⟶ P⟦i⟧) ≃ₗ[R] (𝟙_ _ ⟶ P⟦i⟧) := LinearEquiv.refl R _
  refine ⟨B.compl₁₂ e₁.toLinearMap e.toLinearMap, ?_, ?_⟩
  · intro x y
    exact (hval x (e y)).trans
      (congrArg identificationScalarValue (degreeHomEquiv_value b hb i x y))
  · have := hB
    exact LinearMap.IsPerfPair.compl₁₂ B e₁ e

end WeilConjectures.SixFunctors

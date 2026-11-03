/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCoefficientIso
import WeilConjectures.AlgebraicGeometry.CompactnessFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleCompactnessGeneralField
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre

/-!
# Hypotheses of Brown representability

This file states the Brown-hypotheses lemma for the finite or algebraically
closed base-field scope of the current blueprint, and proves it from the Noetherian
Brown criterion, the coefficient-specific compactness theorems and ring-object
isomorphism invariance.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-representability-for-all-coefficient-rings/sk-lem-brown-hypotheses/_section.md`,
lemma sk-lem-brown-hypotheses, with the standing base-field scope from
`literature/blueprint/latest/blueprint/part-six-operations/prose-P1-01.md`, final sentence.
(blueprint: sk-lem-brown-hypotheses)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

open scoped CategoryTheory.Obj in
private theorem constant_model_is_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let φ := condensedPullbackHom Λ (S.immersion a)
  have h := (hS a).isLocallyFinitelyPresented _
  unfold CondensedRing.upperStar at h
  exact lfp_of_comap (inv φ)
    (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))

/-- Brown representability hypotheses for every admissible coefficient ring over a
finite or algebraically closed field.  The conclusion is the recorded bundle of
local smallness, triangulation, coproducts, split idempotents, essential smallness,
compactness, and generation for the bounded constructible finite-Tor category.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-representability-for-all-coefficient-rings/sk-lem-brown-hypotheses/_section.md`
and its `.proof.md`, paragraphs 1-2; base-field scope from `part-six-operations/prose-P1-01.md`.

Proof (the four steps of the DAG node):
1. Put `S = D^b_ctf(X, Λ)` and `L = Loc(S)`.  The structural theorem
   (h1-brown-hypotheses-structural) gives local smallness, inherited triangulation,
   arbitrary ambient coproducts and split idempotents of `L` (Stacks 05QW).  `X` is
   Noetherian, being of finite type over a field (lem-weil-pbc-finite-type-over-noetherian),
   so det-brown-hypotheses-small makes `S` thick and essentially small.
2. For finite `Λ = A`, sk-prop-ctf-finite-compact makes each object of `S`
   compact in `L`; transport along the admissible ring-object isomorphism
   (lem-sfb-brown-coefficient-iso-invariance).
3. For `Λ = E` or `Q̄_ℓ`, sk-thm-constructible-compactness gives compactness of every
   object of `D^b_c` in its localizing closure, identified with `S` and `L` by
   `D^b_ctf = D^b_c` (lem-integral-ctf-equals-bc); for `O_E` use
   sk-prop-int-compactness through its compactness child (det-prop-int-compactness-compact),
   fed by the uniform integral Ext bound.  `Q_ℓ`, `Z_ℓ` are `E`, `O_E` for `E = Q_ℓ`.
4. For any small skeleton `G` of `S`, lifted into `L`, the localizing-closure generation
   lemma (lem-sfb-localizing-closure-generators): the shifted left orthogonal of `K`
   is localizing and contains `S`, hence `L`, so `id_K = 0`; thus `G` generates in the
   sense of def-pc-generators.
(blueprint: sk-lem-brown-hypotheses)
-/
theorem brownHypotheses_finite_or_algebraicallyClosed
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hℓp : ℓ ≠ p)
    (hk : Finite k ∨ IsAlgClosed k)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  classical
  let : X.Over (Spec (.of k)) := ⟨aX⟩
  have : IsSeparated (X ↘ Spec (.of k)) := inferInstanceAs (IsSeparated aX)
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType aX)
  have : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact aX)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let : Fact (ringChar k ≠ ℓ) := ⟨(ringChar.eq k p) ▸ hℓp.symm⟩
  have hk' : Finite k ∨ IsSepClosed k := by
    rcases hk with h | h
    · exact Or.inl h
    · let := h
      exact Or.inr inferInstance
  have assemble (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] (hR : IsLocalizingAdmissibleCoefficient ℓ R)
      (heq : (constantModelBoundedConstructible R X ⊓
        DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible R X)
      (hc : ∃ hSums : HasCoproducts.{u + 1}
          (localizingClosure (constantModelBoundedConstructible R X)).FullSubcategory,
        ∀ K : (localizingClosure (constantModelBoundedConstructible R X)).FullSubcategory,
          constantModelBoundedConstructible R X K.obj →
            @IsCompactObject _ _ _ hSums K) : BrownHypothesesFor R X := by
    apply (brownHypothesesFor_iff_compact_of_noetherian ℓ X R hR).mpr
    have hloc : localizingClosureProEtale R X =
        localizingClosure (constantModelBoundedConstructible R X) :=
      congrArg (fun S ↦ localizingClosure S) heq
    rw [hloc]
    obtain ⟨hSums, hc⟩ := hc
    exact ⟨hSums, fun K hK ↦ hc K hK.1⟩
  have hi (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      BrownHypothesesFor (Profinite.padicIntegersRingObj.{u} ℓ E) X := by
    have heq := (integral_ctf_equals_bc ℓ X
      (Mon.mk (Profinite.padicIntegersRingObj ℓ E))
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).2.2.2
    have hb := CondensedRing.hasUniformConstructibleExtBound_padicIntegersRingObj ℓ E aX hk'
    have hb' (C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X) :
        ∃ d : ℤ, ∀ N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
          ∀ q : ℤ, d < q →
            Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
              ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧) := by
      obtain ⟨d, hd⟩ := hb C.obj (constant_model_is_constructible _ X C.obj C.property)
      refine ⟨-d, fun N q hq ↦ ?_⟩
      let e := ((DerivedCategory.singleFunctors _).shiftIso q (-q) 0 (by omega)).app N.obj
      refine ⟨fun f g ↦ ?_⟩
      apply (cancel_mono e.hom).mp
      have hN := constant_model_is_constructible _ X N.obj N.property
      exact (hd N.obj hN (-q) (by omega) (f ≫ e.hom)).trans
        (hd N.obj hN (-q) (by omega) (g ≫ e.hom)).symm
    choose b hb using hb'
    let d := fun C ↦ (b C).toNat
    have hd (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
        (q : ℤ) (hq : (d C : ℤ) < q) :
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧) :=
      hb C N q ((Int.self_le_toNat (b C)).trans_lt hq)
    exact assemble _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))) heq
      (integralConstructibleCompactness ℓ E k p hp hℓp.symm X d hd).2.2
  have hq (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      BrownHypothesesFor (Profinite.continuousMapRingObj.{u} E) X := by
    have heq := (integral_ctf_equals_bc ℓ X
      (Mon.mk (Profinite.continuousMapRingObj E))
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩)))).2.2.2
    exact assemble _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))) heq
      (constructible_compactness_of_finite_or_isAlgClosed k hk p hp ℓ hℓp.symm E X).1.1
  rcases hΛ with hf | hz | hpadic | he | hoe | hbar
  · obtain ⟨A, _, _, _, _, hA, hpow, ⟨e⟩⟩ := hf
    let := hA
    apply (brownHypothesesFor_coefficientIso_iff e X).mpr
    apply (brownHypothesesFor_iff_compact_of_noetherian ℓ X _
      (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
        hA, hpow, ⟨Iso.refl _⟩⟩)).mpr
    obtain ⟨hTri, hSums, hc, _⟩ := compactness_finite_admissible ℓ hk hℓp.symm aX A hpow
    exact ⟨hSums, fun K hK ↦ (hc ⟨K.obj, hK⟩).choose_spec⟩
  · obtain ⟨e⟩ := hz
    obtain ⟨_, _, _, _, _, _, _, _, _, zIso, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact (brownHypothesesFor_coefficientIso_iff (e ≪≫ zIso) X).mpr (hi ⟨⊥, inferInstance⟩)
  · obtain ⟨e⟩ := hpadic
    obtain ⟨_, _, _, _, _, _, _, _, qIso, _, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact (brownHypothesesFor_coefficientIso_iff (e ≪≫ qIso) X).mpr (hq ⟨⊥, inferInstance⟩)
  · obtain ⟨E, ⟨e⟩⟩ := he
    exact (brownHypothesesFor_coefficientIso_iff e X).mpr (hq E)
  · obtain ⟨E, ⟨e⟩⟩ := hoe
    exact (brownHypothesesFor_coefficientIso_iff e X).mpr (hi E)
  · obtain ⟨e⟩ := hbar
    apply (brownHypothesesFor_coefficientIso_iff e X).mpr
    have heq := (integral_ctf_equals_bc ℓ X (Mon.mk (Profinite.padicAlgClRingObj ℓ))
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).2.2.2
    exact assemble _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))) heq
      (constructible_compactness_of_finite_or_isAlgClosed k hk p hp ℓ hℓp.symm
        ⟨⊥, inferInstance⟩ X).2.1

end CategoryTheory

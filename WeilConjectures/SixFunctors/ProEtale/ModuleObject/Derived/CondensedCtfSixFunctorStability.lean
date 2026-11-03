/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
-- Definition owner: def-sp-compatible-adjunction-restriction (existing declaration).
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfStabilityDirectImages
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetThmSfCtfStabilityInternalHom
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The six operations on constructible finite-Tor condensed complexes

Source: latest blueprint, sec-six-functors-basics/sk-thm-sf-ctf-stability,
statement and proof; sk-def-cd and sk-prop-ctf-finite-compact-etale for the
finite cohomological dimension needed by the prescribed localizing Brown construction
(blueprint: sk-thm-sf-ctf-stability).

The categories are the ordinary uncompleted module-object derived categories.
The three restricted adjunctions retain their specified ambient Hom bijections.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem compatibleRestriction
    {A : Type*} {B : Type*} {A₀ : Type*} {B₀ : Type*}
    [Category A] [Category B] [Category A₀] [Category B₀]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (iA : A₀ ⥤ A) (iB : B₀ ⥤ B)
    (hA : iA.FullyFaithful) (hB : iB.FullyFaithful)
    (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀)
    (α : F₀ ⋙ iB ≅ iA ⋙ F) (β : G₀ ⋙ iA ≅ iB ⋙ G) :
    WeilConjectures.podCompatibleRestriction adj iA iB := by
  refine ⟨F₀, G₀, α, β, adj.restrictFullyFaithful hA hB α.symm β.symm, ?_⟩
  intro K L h
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply, hA.map_preimage]
  simp only [Iso.symm_hom, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem compatibleRestrictionOfPreserves
    {A : Type*} {B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (P : ObjectProperty A) (Q : ObjectProperty B)
    (hF : ∀ K, P K → Q (F.obj K)) (hG : ∀ L, Q L → P (G.obj L)) :
    WeilConjectures.podCompatibleRestriction adj P.ι Q.ι := by
  exact compatibleRestriction adj P.ι Q.ι P.fullyFaithfulι Q.fullyFaithfulι
    (Q.lift (P.ι ⋙ F) (fun K ↦ hF K.obj K.property))
    (P.lift (Q.ι ⋙ G) (fun L ↦ hG L.obj L.property)) (Iso.refl _) (Iso.refl _)

set_option maxHeartbeats 800000 in
-- The three restrictions elaborate several large derived-functor comparison expressions.
/-- Six-operation preservation, with the original adjunctions on the full subcategories.
The exceptional adjunction is the chosen one on the localizing closures, and not an
assertion of an exceptional right adjoint on the entire ambient derived category.
The final equality transfers every assertion to all bounded constructible inputs for
integral and rational coefficients. Finite coefficients retain the finite-Tor condition
on complexes; no assertion concerns the Tor dimension of their cohomology sheaves.

Source: latest blueprint sk-thm-sf-ctf-stability, statement and proof; finite-CD
compactness input sk-prop-ctf-finite-compact-etale and sk-def-cd
(blueprint: sk-thm-sf-ctf-stability).

Proof plan:
1. Separated cancellation, locally-finite-type cancellation and qcqs permanence
   (lem-weil-pbc-separated-cancellation, lem-weil-pbc-proper-fp-permanence,
   lem-weil-pbc-qcqs-morphism-permanence) show that the k-morphism is separated
   of finite type. Apply det-thm-sf-ctf-stability-direct-images to obtain preservation
   by pullback, direct image, compact support, exceptional pullback and tensor.
   Use the compactification chosen in det-def-sf-operations and sk-def-sfb-dc-setting.
2. Apply det-thm-sf-ctf-stability-internal-hom to both arbitrary finite-Tor
   constructible inputs. Its finite-cone reduction uses locally closed extensions of
   perfect local models, not finite-Tor cohomology sheaves or ambient perfection.
3. Restrict derivedUpperStarLowerStarAdjunction and derivedTensorHomAdjunction along
   the full finite-Tor inclusions. Adjunction.restrictFullyFaithful preserves the
   ambient Hom bijections, naturality, unit and counit. This is exactly the existing
   podCompatibleRestriction predicate, owned by def-sp-compatible-adjunction-restriction;
   use the left-factor tensor convention directly.
4. Restrict the chosen localizing adjunction of sk-thm-existence and
   det-def-sf-operations along its source_mem and target_mem inclusions. Its
   lower_ctf and right_ctf clauses put the images in the same full subcategories.
   The Hom bijection and hence the unit and counit are unchanged.
5. For integral and rational coefficients apply lem-integral-ctf-equals-bc to X and Y,
   which are qcqs in the standing setting. The equality is of ambient object
   predicates, so it transfers both preservation and all three restricted adjunctions.
-/
theorem condensedCtfSixFunctorStability
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ K : ConstantModelConstructibleFiniteTor Λ Y.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((upperStar Λ f.left).leftDerivedFunctor.obj K.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K.obj)) ∧
    (∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
      (constantModelBoundedConstructible Λ Y.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) K.obj →
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).right).obj K).obj) ∧
    (∀ K L : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedTensor Λ X.left).obj K.obj).obj L.obj) ∧
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)) ∧
    WeilConjectures.podCompatibleRestriction (derivedUpperStarLowerStarAdjunction Λ f.left)
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      WeilConjectures.podCompatibleRestriction (derivedTensorHomAdjunction Λ K.obj)
        (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
        (constantModelBoundedConstructible Λ X.left ⊓
          _root_.DerivedCategory.finiteTorAmplitude _).ι) ∧
    WeilConjectures.podCompatibleRestriction
      (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).adjunction
      (ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).source_mem)
      (ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).target_mem) ∧
    ((Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) →
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ X.left ∧
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ Y.left) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have : IsSeparated (f.left ≫ Y.hom) := f.w.symm ▸ ‹IsSeparated X.hom›
  let : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) :=
    f.w.symm ▸ ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : QuasiCompact f.left := inferInstance
  obtain ⟨hpull, htensor, _, hdirect, _, _⟩ :=
    constructibleFiniteTor_stability_direct_images ℓ k hcd Λ hΛ f.left
  have hhom (K L : ConstantModelConstructibleFiniteTor Λ X.left) :=
    (internalHom_stability Λ ℓ k hcd hΛ K.obj L.obj K.property L.property).1
  let R := sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ
  refine ⟨(fun K ↦ hpull K.obj K.property), (fun K ↦ hdirect K.obj K.property),
    ?_, R.right_ctf, (fun K L ↦ ⟨htensor K.obj L.obj K.property L.property, hhom K L⟩),
    ?_, ?_, ?_, ?_⟩
  · intro K
    exact R.lower_ctf ⟨K.obj, R.source_mem K.obj K.property⟩ K.property
  · exact compatibleRestrictionOfPreserves
      (derivedUpperStarLowerStarAdjunction Λ f.left) _ _ hpull hdirect
  · intro K
    apply compatibleRestrictionOfPreserves (derivedTensorHomAdjunction Λ K.obj)
    · intro M hM
      exact htensor K.obj M K.property hM
    · intro L hL
      exact (internalHom_stability Λ ℓ k hcd hΛ K.obj L K.property hL).1
  · exact compatibleRestriction R.adjunction
      (ObjectProperty.ιOfLE R.source_mem) (ObjectProperty.ιOfLE R.target_mem)
      (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
      (ctfLowerShriek Λ ℓ k hcd f hΛ) (ctfExceptionalInverseImage Λ ℓ k hcd f hΛ)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro K L g
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl))
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro K L g
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl))
  · intro h
    have h' : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
      rcases h with h | h | ⟨E, h⟩ | ⟨E, h⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inl h⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr h⟩))
      · exact Or.inr (Or.inr (Or.inr h))
    exact ⟨(integral_ctf_equals_bc ℓ X.left (Mon.mk Λ) h').2.2.2,
      (integral_ctf_equals_bc ℓ Y.left (Mon.mk Λ) h').2.2.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartPointScalarComparison
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolutionSupplement
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-! # Scalar coordinates for bounded finite free condensed complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

namespace IntegralHeartScalarCoordinates
open ContinuousScalarPresentation FiniteConstantModel CategoryTheory.MonoidalCategory
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem scalarSection_injective : Function.Injective (scalarSection A) := by
  intro a b h
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  apply (cancel_mono (scalarHom A)).mp
  apply (adj.homEquiv _ _).symm.injective
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
  rw [adj.homEquiv_counit, adj.homEquiv_counit]
  change Functor.LaxMonoidal.ε F ≫ F.map (a ≫ scalarHom A) ≫ adj.counit.app (Λ A) =
    Functor.LaxMonoidal.ε F ≫ F.map (b ≫ scalarHom A) ≫ adj.counit.app (Λ A)
  have hc : F.map (scalarHom A) ≫ adj.counit.app (Λ A) = φ A := scalarCounit A
  simp only [Functor.map_comp, Category.assoc, hc]
  exact h

private theorem H_regular_faithful : Function.Injective
    (fun f : Mod.regular (B A) ⟶ Mod.regular (B A) ↦ (H A).map f) := by
  intro f g h
  change (H A).map f = (H A).map g at h
  let a := (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ B A) ≫ f.hom
  let b := (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ B A) ≫ g.hom
  have hf : f = Mod.regularLift (Mod.regular (B A)) a :=
    Mod.regular_hom_ext (Mod.one_comp_regularLift _ _).symm
  have hg : g = Mod.regularLift (Mod.regular (B A)) b :=
    Mod.regular_hom_ext (Mod.one_comp_regularLift _ _).symm
  apply Mod.regular_hom_ext
  apply scalarSection_injective A
  have he : (regularIso A).hom ≫
      Mod.regularLift (Mod.regular (Λ A)) (scalarSection A a) =
      (regularIso A).hom ≫
        Mod.regularLift (Mod.regular (Λ A)) (scalarSection A b) := by
    rw [← regular_entry, ← regular_entry, ← hf, ← hg, h]
  have hh := (cancel_epi (regularIso A).hom).mp he
  simpa only [Mod.one_comp_regularLift] using
    congrArg (fun k ↦ (MonObj.one : 𝟙_ _ ⟶ Λ A) ≫ k.hom) hh

private theorem H_finiteFree_faithful (m n : ℕ) : Function.Injective
    (fun f : Mod.finiteFree (B A) m ⟶ Mod.finiteFree (B A) n ↦ (H A).map f) := by
  intro f g h
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  apply H_regular_faithful A
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ (H A).map (biproduct.ι _ j) ≫ t ≫
      (H A).map (biproduct.π _ k)) h

private theorem continuous_finiteFree_faithful (m n : ℕ) : Function.Injective
    (fun f : freeScalars A m ⟶ freeScalars A n ↦ (continuousScalarFunctor A).map f) := by
  intro f g h
  change (H A).map ((scalarModules A).map f) =
    (H A).map ((scalarModules A).map g) at h
  have : (scalarModules A).Faithful := scalarModules_faithful A
  apply (scalarModules A).map_injective
  apply (cancel_epi (scalarFiniteFreeIso A m).inv).mp
  apply (cancel_mono (scalarFiniteFreeIso A n).hom).mp
  apply H_finiteFree_faithful A m n
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ (H A).map (scalarFiniteFreeIso A m).inv ≫ t ≫
      (H A).map (scalarFiniteFreeIso A n).hom) h

end IntegralHeartScalarCoordinates

private theorem lift_finiteFreeComplex
    {A : Type*} [CommRing A] {D : Type*} [Category D] [Abelian D]
    (F : ModuleCat A ⥤ D) [F.Additive]
    (hfull : ∀ m n, Function.Surjective
      (fun f : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) ↦ F.map f))
    (hfaithful : ∀ m n, Function.Injective
      (fun f : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) ↦ F.map f))
    (C : CochainComplex D ℤ) (b c : ℤ)
    (hb : C.IsStrictlyGE b) (hc : C.IsStrictlyLE c)
    (hC : ∀ q, ∃ n : ℕ, Nonempty (F.obj (ModuleCat.of A (Fin n → A)) ≅ C.X q)) :
    ∃ P : CochainComplex (ModuleCat A) ℤ,
      P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
      (∀ q, Module.Free A (P.X q) ∧ Module.Finite A (P.X q)) ∧
      Nonempty (C ≅ (F.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  have hz : IsZero (ModuleCat.of A (Fin 0 → A)) := by
    rw [IsZero.iff_id_eq_zero]
    ext x i
    exact Fin.elim0 i
  let n (q : ℤ) : ℕ := if b ≤ q ∧ q ≤ c then (hC q).choose else 0
  have e (q : ℤ) : Nonempty (F.obj (ModuleCat.of A (Fin (n q) → A)) ≅ C.X q) := by
    by_cases hq : b ≤ q ∧ q ≤ c
    · have hn : n q = (hC q).choose := if_pos hq
      rw [hn]
      exact (hC q).choose_spec
    · have hzero : IsZero (C.X q) := by
        by_cases h : q < b
        · exact C.isZero_of_isStrictlyGE b q h
        · exact C.isZero_of_isStrictlyLE c q (by omega)
      have hn : n q = 0 := if_neg hq
      rw [hn]
      exact ⟨(F.map_isZero hz).iso hzero⟩
  let e' (q : ℤ) := (e q).some
  choose d hd using fun i j ↦ hfull (n i) (n j)
    ((e' i).hom ≫ C.d i j ≫ (e' j).inv)
  change ∀ i j, F.map (d i j) = (e' i).hom ≫ C.d i j ≫ (e' j).inv at hd
  let P : CochainComplex (ModuleCat A) ℤ :=
    { X q := ModuleCat.of A (Fin (n q) → A)
      d := d
      shape i j hij := by
        apply hfaithful (n i) (n j)
        change F.map (d i j) = F.map 0
        rw [hd, F.map_zero, C.shape i j hij]
        simp
      d_comp_d' i j k _ _ := by
        apply hfaithful (n i) (n k)
        change F.map (d i j ≫ d j k) = F.map 0
        rw [F.map_comp, hd, hd, F.map_zero]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, C.d_comp_d_assoc, comp_zero, zero_comp] }
  have hzero (q : ℤ) (hq : q < b ∨ c < q) : IsZero (P.X q) := by
    have hn : n q = 0 := if_neg (by omega)
    change IsZero (ModuleCat.of A (Fin (n q) → A))
    rw [hn]
    exact hz
  refine ⟨P, ?_, ?_, fun _ ↦ ⟨inferInstance, inferInstance⟩, ⟨?_⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ hzero q (Or.inl hq)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ hzero q (Or.inr hq)
  · exact (HomologicalComplex.Hom.isoOfComponents e' (by
      intro i j _
      symm
      change F.map (d i j) ≫ (e' j).hom = (e' i).hom ≫ C.d i j
      rw [hd]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])).symm


/-- Scalar matrices of a bounded finite free condensed complex lift simultaneously,
including the differential and its square-zero identity.
Source: blueprint latest, integral-heart-local-model, clause (1); Stacks Tag 093J
(blueprint: lem-sfb-integral-heart-scalar-complex-coordinates).

Proof: choose a finite free basis in each degree in the given interval, and rank zero
outside it. A map between the regular condensed modules is a scalar, since its value on
one determines the map, and sections on the one-point profinite set are the integer ring.
Thus each differential matrix has a unique ordinary scalar matrix. Faithfulness of this
matrix correspondence reflects the square-zero relations. These matrices form P, and the
chosen degreewise bases assemble to an isomorphism of complexes. The chosen zero ranks
outside the interval give the same strict bounds. Every term of P is an ordinary finite
power of the scalar ring, hence finite free. Empty intervals and zero ranks are included. -/
theorem integralHeart_scalarComplex_coordinates
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (C : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)) ℤ)
    (b c : ℤ) (hb : C.IsStrictlyGE b) (hc : C.IsStrictlyLE c)
    (hC : ∀ q, Mod.IsFree (SmallAdicCompletion.Coefficients.integerRing ℓ E) (C.X q)) :
    ∃ P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ,
      P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
      (∀ q, Module.Free (integralHeartScalars.{u} ℓ E) (P.X q) ∧
        Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
      Nonempty (C ≅
        ((integralHeartContinuousRealization.{u} ℓ E).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  let A := SmallAdicCompletion.Coefficients.integers.{u} ℓ E
  let R : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤ ModuleCat.{u + 1} A :=
    ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : integralHeartScalars.{u} ℓ E ≃+* A).symm.toRingHom
  let F := integralHeartContinuousRealization.{u} ℓ E
  have hfull (m n : ℕ) : Function.Surjective
      (fun f : ModuleCat.of (integralHeartScalars.{u} ℓ E)
          (Fin m → integralHeartScalars.{u} ℓ E) ⟶
        ModuleCat.of (integralHeartScalars.{u} ℓ E)
          (Fin n → integralHeartScalars.{u} ℓ E) ↦ F.map f) := by
    intro f
    obtain ⟨g, hg⟩ := ContinuousScalarPresentation.continuous_free_map_surjective A m n
      ((ContinuousScalarPresentation.continuousFreeIso A m).inv ≫ f ≫
        (ContinuousScalarPresentation.continuousFreeIso A n).hom)
    let M := ModuleCat.of (integralHeartScalars.{u} ℓ E)
      (Fin m → integralHeartScalars.{u} ℓ E)
    let N := ModuleCat.of (integralHeartScalars.{u} ℓ E)
      (Fin n → integralHeartScalars.{u} ℓ E)
    refine ⟨R.preimage (X := M) (Y := N) g, ?_⟩
    change (continuousScalarFunctor A).map (R.map (R.preimage (X := M) (Y := N) g)) = f
    rw [Functor.map_preimage]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using
      congrArg (fun k ↦ (ContinuousScalarPresentation.continuousFreeIso A m).hom ≫ k ≫
        (ContinuousScalarPresentation.continuousFreeIso A n).inv) hg
  have hfaithful (m n : ℕ) : Function.Injective
      (fun f : ModuleCat.of (integralHeartScalars.{u} ℓ E)
          (Fin m → integralHeartScalars.{u} ℓ E) ⟶
        ModuleCat.of (integralHeartScalars.{u} ℓ E)
          (Fin n → integralHeartScalars.{u} ℓ E) ↦ F.map f) := by
    intro f g h
    apply R.map_injective
    exact IntegralHeartScalarCoordinates.continuous_finiteFree_faithful A m n h
  apply lift_finiteFreeComplex F hfull hfaithful C b c hb hc
  intro q
  obtain ⟨n, ⟨e⟩⟩ := hC q
  exact ⟨n, ⟨ContinuousScalarPresentation.continuousFreeIso A n ≪≫ e.symm⟩⟩

end AlgebraicGeometry.ProEtale

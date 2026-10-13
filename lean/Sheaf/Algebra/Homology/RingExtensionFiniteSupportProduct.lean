/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Data.Int.Interval

/-! # Scalar extension of a finite-support product

Source: Stacks Project, more-algebra.tex, Lemma 0A6A (lemma-base-change-RHom).
(blueprint: lem-pc-ring-extension-finite-support-product)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private noncomputable def restrictFan_isLimit {C : Type*} [Category C] [HasZeroMorphisms C]
    (M : ℤ → C) (T : C) (π : ∀ p, T ⟶ M p) (hπ : IsLimit (Fan.mk T π))
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (M p)) :
    IsLimit (Fan.mk T (fun p : s ↦ π p)) := by
  classical
  let extend (c : Fan (fun p : s ↦ M p)) : Fan M :=
    Fan.mk c.pt (fun p ↦ if h : p ∈ s then c.proj ⟨p, h⟩ else 0)
  refine Fan.IsLimit.mk _ (fun c ↦ hπ.lift (extend c)) ?_ ?_
  · intro c p
    simpa [extend] using hπ.fac (extend c) ⟨p.val⟩
  · intro c m hm
    apply hπ.hom_ext
    intro p
    by_cases hp : p.as ∈ s
    · rw [hπ.fac]
      simpa [extend, hp] using hm ⟨p.as, hp⟩
    · exact (hz p.as hp).eq_of_tgt _ _

private noncomputable def extendFan_isLimit {C : Type*} [Category C] [HasZeroMorphisms C]
    (M : ℤ → C) (T : C) (π : ∀ p, T ⟶ M p)
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (M p))
    (hπ : IsLimit (Fan.mk T (fun p : s ↦ π p))) : IsLimit (Fan.mk T π) := by
  let restrict (c : Fan M) : Fan (fun p : s ↦ M p) :=
    Fan.mk c.pt (fun p ↦ c.proj p)
  refine Fan.IsLimit.mk _ (fun c ↦ hπ.lift (restrict c)) ?_ ?_
  · intro c p
    by_cases hp : p ∈ s
    · exact hπ.fac (restrict c) ⟨⟨p, hp⟩⟩
    · exact (hz p hp).eq_of_tgt _ _
  · intro c m hm
    apply hπ.hom_ext
    intro p
    exact (hm p.as).trans (hπ.fac (restrict c) p).symm

private noncomputable def transportFan_isLimit {C : Type*} [Category C]
    {M N : ℤ → C} {T T' : C} (π : ∀ p, T ⟶ M p) (hπ : IsLimit (Fan.mk T π))
    (e : T ≅ T') (eM : ∀ p, M p ≅ N p) :
    IsLimit (Fan.mk T' (fun p ↦ e.inv ≫ π p ≫ (eM p).hom)) := by
  let c' (c : Fan N) : Fan M := Fan.mk c.pt (fun p ↦ c.proj p ≫ (eM p).inv)
  refine Fan.IsLimit.mk _ (fun c ↦ hπ.lift (c' c) ≫ e.hom) ?_ ?_
  · intro c p
    change (hπ.lift (c' c) ≫ e.hom) ≫
      (e.inv ≫ π p ≫ (eM p).hom) = c.proj p
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hf : hπ.lift (c' c) ≫ π p = c.proj p ≫ (eM p).inv :=
      hπ.fac (c' c) ⟨p⟩
    rw [← Category.assoc, hf]
    simp
  · intro c m hm
    apply (cancel_mono e.inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply hπ.hom_ext
    intro p
    rw [hπ.fac]
    have h := hm p.as
    simpa [c', Category.assoc] using congrArg (fun f ↦ f ≫ (eM p.as).inv) h

private noncomputable def ringExtensionPresheafFunctor
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    RingSiteModules A ⥤
      PresheafOfModules.{u} ((sheafCompose ⊥
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf B)).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ)
  map a :=
    { app := fun U ↦ (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map
        (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap φ) _ a }
  map_id := by
    intro M
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp := by
    intro M N P a b
    apply PresheafOfModules.hom_ext
    intro U
    simp

private noncomputable def ringExtensionFunctor
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    RingSiteModules A ⥤ RingSiteModules B :=
  ringExtensionPresheafFunctor φ ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf B)).obj)

private theorem ringExtensionFunctor_additive
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ringExtensionFunctor φ).Additive := by
  have hscalar (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
      (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ((ringSiteMap φ).hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf B)).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  have hpre : (ringExtensionPresheafFunctor φ).Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [ringExtensionPresheafFunctor, SheafOfModules.add_val,
      PresheafOfModules.add_app] using
      (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map_add
        (f := a.val.app U) (g := b.val.app U)
  unfold ringExtensionFunctor
  infer_instance

/-- Scalar extension of a limiting fan with only finitely many nonzero factors is
again a limiting fan, with projections normalized on pure tensors.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, finite-product computation;
algebra.tex, tensor products and finite direct sums.
(blueprint: lem-pc-ring-extension-finite-support-product).

Proof: evaluate at the unique object. On the bottom-topology one-object site,
sheafification is an isomorphism and evaluation identifies module sheaves with modules.
Delete the zero factors outside [a,b] from the limiting product: maps into those factors
are unique, so restriction to the interval and extension by zero are inverse universal
properties. The interval is finite, including when a>b. Tensor product with B commutes
with its finite product, by the finite-direct-sum formula TensorProduct.piRight.
Transport the resulting limiting fan back to module sheaves and along hF. The
projections are the scalar extensions of the original projections transported by hF;
the tensor-product formula and naturality of the sheafification unit give the displayed
formula. No claim about F.map is needed, and no flatness hypothesis is used. -/
theorem ringExtension_finiteSupport_product
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : ℤ → RingSiteModules A) (T : RingSiteModules A) (π : ∀ p, T ⟶ M p)
    (hπ : IsLimit (Fan.mk T π))
    (hb : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (M p)) :
    ∃ ρ : ∀ p, F.obj T ⟶ F.obj (M p),
      Nonempty (IsLimit (Fan.mk (F.obj T) ρ)) ∧
      ∀ (p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : T.val.obj U),
        (ρ p).val.app U (ringExtensionPure φ F hF T U b x) =
          ringExtensionPure φ F hF (M p) U b ((π p).val.app U x) := by
  classical
  let E := ringExtensionFunctor φ
  let : E.Additive := ringExtensionFunctor_additive φ
  obtain ⟨a, b, hz⟩ := hb
  let s := Finset.Icc a b
  have hz' (p : ℤ) (hp : p ∉ s) : IsZero (M p) := by
    apply hz p
    simp only [s, Finset.mem_Icc, not_and_or, not_le] at hp
    exact hp
  let hsmall := restrictFan_isLimit M T π hπ s hz'
  let hsmallE := (Fan.isLimitMapConeEquiv E _ _)
    (isLimitOfPreserves E hsmall)
  let hlargeE := extendFan_isLimit (fun p ↦ E.obj (M p)) (E.obj T)
    (fun p ↦ E.map (π p)) s (fun p hp ↦ E.map_isZero (hz' p hp)) hsmallE
  let ρ : ∀ p, F.obj T ⟶ F.obj (M p) := fun p ↦
    eqToHom (hF T) ≫ E.map (π p) ≫ eqToHom (hF (M p)).symm
  refine ⟨ρ, ⟨transportFan_isLimit (fun p ↦ E.map (π p)) hlargeE
    (eqToIso (hF T)).symm (fun p ↦ (eqToIso (hF (M p))).symm)⟩, ?_⟩
  intro p U b x
  simp only [ρ, ringExtensionPure, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have he : ∀ z,
      (eqToHom (hF T)).val.app U ((eqToHom (hF T).symm).val.app U z) = z := by
    intro z
    change ((eqToHom (hF T).symm ≫ eqToHom (hF T)).val.app U) z = z
    simp
  rw [he]
  congr 1
  let α := (PresheafOfModules.toPresheaf _).map
    ((ringExtensionPresheafFunctor φ).map (π p))
  have hn := congr_app (toSheafify_naturality (J := ⊥) α) U
  let : Module A B := Module.compHom B φ
  have hv := congrArg (fun f ↦ f (b ⊗ₜ[A] x)) hn
  exact hv.symm

end CategoryTheory

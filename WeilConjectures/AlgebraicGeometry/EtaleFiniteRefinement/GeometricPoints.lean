/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Lifts of geometric points

For a morphism of schemes `u : U ⟶ X` and a geometric point `g : Spec Ω ⟶ X`, with `Ω`
separably closed, we count the lifts `s : Spec Ω ⟶ U` of `g` along `u`. For étale `u` this is
the number of geometric points of the fibre of `u` over the image of `g`, and it only depends on
that image point.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.liftsEquivOfSpecMap`: the lifts along an étale morphism do not
  change when the separably closed field is enlarged.
- `AlgebraicGeometry.Scheme.Hom.card_lifts_eq_card_lifts_sepClosurePoint`: the number of lifts
  only depends on the image point.
- `AlgebraicGeometry.Scheme.Hom.HasGeometricFibersCardLE`: a bound on the number of lifts of
  all geometric points.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-- Every morphism from the spectrum of a field factors through the spectrum of a residue
field. -/
lemma Scheme.exists_eq_specMap_comp_fromSpecResidueField {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ X) :
    ∃ (x : X) (ψ : X.residueField x ⟶ .of K), s = Spec.map ψ ≫ X.fromSpecResidueField x := by
  obtain ⟨⟨x, ψ⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective s
  exact ⟨x, ψ, rfl⟩

lemma Scheme.specMap_comp_fromSpecResidueField_eq_iff {K : Type u} [Field K] {x₁ x₂ : X}
    {ψ₁ : X.residueField x₁ ⟶ .of K} {ψ₂ : X.residueField x₂ ⟶ .of K} :
    Spec.map ψ₁ ≫ X.fromSpecResidueField x₁ = Spec.map ψ₂ ≫ X.fromSpecResidueField x₂ ↔
      ∃ e : x₁ = x₂, ψ₁ = (X.residueFieldCongr e).hom ≫ ψ₂ :=
  ((X.SpecToEquivOfField K).symm.injective.eq_iff (a := ⟨x₁, ψ₁⟩) (b := ⟨x₂, ψ₂⟩)).trans
    Scheme.SpecToEquivOfField_eq_iff

/-- **Lifts along an étale morphism after enlarging the field.** For `u` étale, a geometric
point `g : Spec Ω₁ ⟶ X` and a field extension `φ : Ω₁ →+* Ω₂`, composing with `Spec φ` is a
bijection between the lifts of `g` and those of `Spec φ ≫ g`: the residue fields of `U` are
separable over those of `X`, so their embeddings into `Ω₂` land in `Ω₁`. -/
noncomputable def Scheme.Hom.liftsEquivOfSpecMap (u : U ⟶ X) [Etale u] {Ω₁ Ω₂ : Type u}
    [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] (φ : Ω₁ →+* Ω₂) (g : Spec (.of Ω₁) ⟶ X) :
    {s // s ≫ u = g} ≃ {s // s ≫ u = Spec.map (CommRingCat.ofHom φ) ≫ g} :=
  Equiv.ofBijective (fun s ↦ ⟨Spec.map (CommRingCat.ofHom φ) ≫ s.1, by rw [Category.assoc, s.2]⟩)
    (by
      constructor
      · rintro ⟨s₁, _⟩ ⟨s₂, _⟩ h
        obtain ⟨x₁, ψ₁, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField s₁
        obtain ⟨x₂, ψ₂, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField s₂
        simp only [Subtype.mk.injEq, ← Spec.map_comp_assoc,
          Scheme.specMap_comp_fromSpecResidueField_eq_iff] at h
        obtain ⟨e, he⟩ := h
        refine Subtype.ext (Scheme.specMap_comp_fromSpecResidueField_eq_iff.2 ⟨e, ?_⟩)
        ext a
        exact φ.injective congr($he a)
      · rintro ⟨t, ht⟩
        obtain ⟨x, χ, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField t
        obtain ⟨x₀, γ, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField g
        rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
          ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
          Scheme.specMap_comp_fromSpecResidueField_eq_iff] at ht
        obtain ⟨rfl, he⟩ := ht
        simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
        let := (u.residueFieldMap x).hom.toAlgebra
        obtain ⟨ψ, hψ⟩ := IsSepClosed.exists_comp_eq γ.hom φ χ.hom congr(($he).hom)
        have hψγ : u.residueFieldMap x ≫ CommRingCat.ofHom ψ = γ := by
          ext a
          apply φ.injective
          have := congr(($he).hom a)
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
            CommRingCat.hom_ofHom] at this ⊢
          rw [← this, ← hψ]
          rfl
        refine ⟨⟨Spec.map (CommRingCat.ofHom ψ) ≫ U.fromSpecResidueField x, ?_⟩, ?_⟩
        · rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
            ← Spec.map_comp_assoc, hψγ]
        · refine Subtype.ext ?_
          dsimp only
          rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom])

/-- The geometric point `Spec κ(x)ˢᵉᵖ ⟶ X` at `x` given by the separable closure of the residue
field. -/
noncomputable def Scheme.sepClosurePoint (X : Scheme.{u}) (x : X) :
    Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x

/-- **The number of lifts of a geometric point along an étale morphism only depends on its
image point.** -/
theorem Scheme.Hom.card_lifts_eq_card_lifts_sepClosurePoint (u : U ⟶ X) [Etale u]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : Spec (.of Ω) ⟶ X) (a : Spec (.of Ω)) :
    ENat.card {s // s ≫ u = g} = ENat.card {s // s ≫ u = X.sepClosurePoint (g a)} := by
  obtain ⟨x₀, γ, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField g
  have ha : (Spec.map γ ≫ X.fromSpecResidueField x₀) a = x₀ := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  rw [ha]
  let := γ.hom.toAlgebra
  let φ : SeparableClosure (X.residueField x₀) →ₐ[X.residueField x₀] Ω := IsSepClosed.lift
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.sepClosurePoint x₀ =
      Spec.map γ ≫ X.fromSpecResidueField x₀ := by
    rw [Scheme.sepClosurePoint, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ φ.commutes a)
  rw [← hφ]
  exact (ENat.card_congr (u.liftsEquivOfSpecMap φ.toRingHom _)).symm

/-- `u` has **geometric fibres of cardinality at most `d`**: every geometric point
`Spec Ω ⟶ X`, with `Ω` separably closed, has at most `d` lifts along `u`. -/
def Scheme.Hom.HasGeometricFibersCardLE (u : U ⟶ X) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (g : Spec (.of Ω) ⟶ X),
    ENat.card {s // s ≫ u = g} ≤ d

/-! ### Lifts along composites and base changes -/

section Lifts

variable {T W V Y P : Scheme.{u}}

/-- Lifts along a base change `U ×_X Y ⟶ Y` are lifts along `U ⟶ X`. -/
noncomputable def Scheme.Hom.liftsPullbackSndEquiv (u : U ⟶ X) (p : Y ⟶ X) (h : T ⟶ Y) :
    {s // s ≫ pullback.snd u p = h} ≃ {s // s ≫ u = h ≫ p} where
  toFun s := ⟨s.1 ≫ pullback.fst u p, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2]⟩
  invFun s := ⟨pullback.lift s.1 h s.2, pullback.lift_snd _ _ _⟩
  left_inv s := by
    ext1
    apply pullback.hom_ext <;> simp [s.2]
  right_inv s := Subtype.ext (pullback.lift_fst _ _ _)

/-- Lifts along `w` are lifts along `w ≫ ι` for a monomorphism `ι`. -/
def Scheme.Hom.liftsCompMonoEquiv (w : W ⟶ V) (ι : V ⟶ Y) [Mono ι] (g : T ⟶ V) :
    {s // s ≫ w = g} ≃ {s // s ≫ w ≫ ι = g ≫ ι} where
  toFun s := ⟨s.1, by rw [reassoc_of% s.2]⟩
  invFun s := ⟨s.1, by rw [← cancel_mono ι, Category.assoc]; exact s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma Scheme.Hom.subsingleton_lifts_of_mono (j : U ⟶ Y) [Mono j] (h : T ⟶ Y) :
    Subsingleton {s // s ≫ j = h} :=
  ⟨fun s₁ s₂ ↦ Subtype.ext ((cancel_mono j).1 (s₁.2.trans s₂.2.symm))⟩

instance (K : Type u) [Field K] : Subsingleton (Spec (.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

/-- **Lifts of a geometric point through a decomposition into two opens.** If the open
`W ⊆ P` is the complement of the image of the open immersion `Γ`, every lift along `q : P ⟶ Y`
of a morphism from the spectrum of a field lifts through exactly one of `W` and `Γ`. -/
noncomputable def Scheme.Hom.liftsSumEquiv {K : Type u} [Field K] (q : P ⟶ Y) (Γ : U ⟶ P)
    [IsOpenImmersion Γ] (W : P.Opens) (hW : (W : Set P) = (Set.range Γ.base)ᶜ)
    (h : Spec (.of K) ⟶ Y) :
    {s // s ≫ W.ι ≫ q = h} ⊕ {s // s ≫ Γ ≫ q = h} ≃ {s // s ≫ q = h} :=
  Equiv.ofBijective
    (Sum.elim (fun s ↦ ⟨s.1 ≫ W.ι, by rw [Category.assoc]; exact s.2⟩)
      (fun s ↦ ⟨s.1 ≫ Γ, by rw [Category.assoc]; exact s.2⟩)) (by
    have hpt (a : Spec (.of K)) : (Set.univ : Set (Spec (.of K))) = {a} :=
      (Set.eq_singleton_iff_unique_mem.2 ⟨trivial, fun b _ ↦ Subsingleton.elim b a⟩)
    obtain ⟨a⟩ : Nonempty (Spec (.of K)) := inferInstance
    constructor
    · intro s₁ s₂ hs
      rcases s₁ with ⟨s₁, _⟩ | ⟨s₁, _⟩ <;> rcases s₂ with ⟨s₂, _⟩ | ⟨s₂, _⟩ <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hs
      · exact congrArg Sum.inl (Subtype.ext ((cancel_mono _).1 hs))
      · have h₁ : (s₁ ≫ W.ι) a ∈ (W : Set P) := by simp
        rw [hs, hW] at h₁
        exact (h₁ ⟨_, rfl⟩).elim
      · have h₁ : (s₂ ≫ W.ι) a ∈ (W : Set P) := by simp
        rw [← hs, hW] at h₁
        exact (h₁ ⟨_, rfl⟩).elim
      · exact congrArg Sum.inr (Subtype.ext ((cancel_mono _).1 hs))
    · rintro ⟨s, hs⟩
      by_cases ha : s a ∈ Set.range Γ.base
      · have hrange : Set.range s.base ⊆ Set.range Γ.base := by
          rintro _ ⟨b, rfl⟩
          rwa [Subsingleton.elim b a]
        refine ⟨Sum.inr ⟨IsOpenImmersion.lift Γ s hrange, ?_⟩, ?_⟩
        · rw [IsOpenImmersion.lift_fac_assoc]; exact hs
        · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
      · have hrange : Set.range s.base ⊆ Set.range W.ι.base := by
          rintro _ ⟨b, rfl⟩
          rw [Scheme.Opens.range_ι, hW, Subsingleton.elim b a]
          exact ha
        refine ⟨Sum.inl ⟨IsOpenImmersion.lift W.ι s hrange, ?_⟩, ?_⟩
        · rw [IsOpenImmersion.lift_fac_assoc]; exact hs
        · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _))

end Lifts

end AlgebraicGeometry

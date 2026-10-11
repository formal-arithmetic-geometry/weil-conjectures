/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricPoints
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Geometric fibres drop at points escaping an open subscheme

Let `u : U ⟶ X` be étale and separated, factoring as an open immersion `j : U ⟶ Y` followed by a
separated `p : Y ⟶ X`. If a point `y ∉ U` of `Y` is a specialization of a point `x ∈ U`, then the
geometric fibre of `u` over `p y` has fewer points than some other geometric fibre. This is the
induction step of Stacks 09Z0.

We realise the specialization `x ⤳ y` by a valuation ring `A` whose fraction field `L` is
separably closed. Such an `A` is strictly henselian, so every lift of the closed geometric point
`Spec κ_A ⟶ X` to `U` extends to `Spec A`
(`AlgebraicGeometry.Scheme.Hom.exists_lift_of_valuationSubring`). The restrictions to `Spec L` of
these extensions are pairwise distinct, by the valuative criterion of separatedness, and they
miss the lift through `x`, since its extension would send the closed point to `y`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes`
- `AlgebraicGeometry.Scheme.Hom.exists_lift_of_valuationSubring`
- `AlgebraicGeometry.Scheme.Hom.card_lifts_sepClosurePoint_lt`
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U X Y : Scheme.{u}}

/-- The residue field of the closed point of the spectrum of a local ring is separably closed if
the residue field of the ring is. -/
lemma isSepClosed_residueField_closedPoint (R : Type u) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] :
    IsSepClosed ((Spec (.of R)).residueField (closedPoint R)) := by
  have : IsSepClosed (maximalIdeal R).ResidueField :=
    IsSepClosed.of_ringEquiv (k := ResidueField R) (RingEquiv.ofBijective _
      (maximalIdeal R).bijective_algebraMap_quotient_residueField)
  exact @IsSepClosed.of_ringEquiv (maximalIdeal R).ResidueField _ _ _
    (Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).commRingCatIsoToRingEquiv.symm this

/-- Two morphisms from the spectrum of a field to an étale `S`-scheme agree if they agree over
`S`, have the same image point, and the residue field of the base point is separably closed. -/
lemma Scheme.Hom.eq_of_comp_eq_of_isSepClosed {P S : Scheme.{u}} (v : P ⟶ S) [Etale v]
    {K : Type u} [Field K] (f₁ f₂ : Spec (.of K) ⟶ P) (h : f₁ ≫ v = f₂ ≫ v) (b : Spec (.of K))
    (hb : f₁ b = f₂ b) (hsep : IsSepClosed (S.residueField (v (f₁ b)))) : f₁ = f₂ := by
  obtain ⟨z₁, ψ₁, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField f₁
  obtain ⟨z₂, ψ₂, rfl⟩ := Scheme.exists_eq_specMap_comp_fromSpecResidueField f₂
  have hz₁ : (Spec.map ψ₁ ≫ P.fromSpecResidueField z₁) b = z₁ := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  have hz₂ : (Spec.map ψ₂ ≫ P.fromSpecResidueField z₂) b = z₂ := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  rw [hz₁, hz₂] at hb
  rw [hz₁] at hsep
  subst hb
  rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    Scheme.specMap_comp_fromSpecResidueField_eq_iff] at h
  obtain ⟨e, he⟩ := h
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  suffices ψ₁ = ψ₂ by rw [this]
  let := (v.residueFieldMap z₁).hom.toAlgebra
  ext a
  obtain ⟨c, rfl⟩ := IsSepClosed.algebraMap_surjective (k := S.residueField (v z₁))
    (K := P.residueField z₁) a
  exact congr(($he).hom c)

/-- **Specializations come from valuation rings with separably closed fraction field.** If
`x ⤳ y` in `Y`, there are a valuation subring `A` of a separably closed field `L` and a morphism
`Spec A ⟶ Y` sending the closed point to `y` and the generic point to `x`. -/
theorem Scheme.exists_valuationSubring_of_specializes {x y : Y} (h : x ⤳ y) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (A : ValuationSubring L)
      (a : Spec (.of A) ⟶ Y), a (closedPoint A) = y ∧
        ∀ b, (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ a) b = x := by
  let L := SeparableClosure (Y.residueField x)
  let f : Y.presheaf.stalk y ⟶ .of L := Y.presheaf.stalkSpecializes h ≫ Y.residue x ≫
    CommRingCat.ofHom (algebraMap (Y.residueField x) L)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f.hom
  let g : Y.presheaf.stalk y ⟶ .of A := CommRingCat.ofHom (f.hom.codRestrict A.toSubring hA)
  have w : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ Spec.map g ≫ Y.fromSpecStalk y =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x) L)) ≫
        Y.fromSpecResidueField x := by
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨L, inferInstance, inferInstance, A, Spec.map g ≫ Y.fromSpecStalk y, ?_, fun b ↦ ?_⟩
  · have : IsLocalHom g.hom := hloc
    rw [Scheme.Hom.comp_apply]
    have hc : Spec.map g (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      IsLocalRing.comap_closedPoint g.hom
    rw [hc, Scheme.fromSpecStalk_closedPoint]
  · rw [w, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _

/-- The spectrum of the residue map of a local ring hits the closed point. -/
lemma specMap_residue_apply (R : Type u) [CommRing R] [IsLocalRing R]
    (b : Spec (.of (ResidueField R))) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) b = closedPoint R := by
  rw [Subsingleton.elim b (closedPoint _)]
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)

/-- **Lifts along an étale morphism extend over a strictly henselian valuation ring.** Let `A`
be a valuation subring of a separably closed field. Every lift along an étale `u` of the closed
geometric point `Spec κ_A ⟶ Spec A ⟶ X` extends to a lift of `Spec A ⟶ X`: the base change of
`u` to `Spec A` is étale, and étale algebras over `A` have sections through every point over the
closed point (`Algebra.Etale.exists_algHom_comap_maximalIdeal_eq`). -/
theorem Scheme.Hom.exists_lift_of_valuationSubring (u : U ⟶ X) [Etale u] {L : Type u} [Field L]
    [IsSepClosed L] (A : ValuationSubring L) (a : Spec (.of A) ⟶ X)
    (s : Spec (.of (ResidueField A)) ⟶ U)
    (hs : s ≫ u = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ a) :
    ∃ σ : Spec (.of A) ⟶ U,
      σ ≫ u = a ∧ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ = s := by
  let v := pullback.snd u a
  let s' : Spec (.of (ResidueField A)) ⟶ pullback u a := pullback.lift s _ hs
  obtain ⟨b⟩ : Nonempty (Spec (.of (ResidueField A))) := inferInstance
  have hvb : v (s' b) = closedPoint A := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact specMap_residue_apply A b
  obtain ⟨V, hV, hzV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show s' b ∈ (⊤ : (pullback u a).Opens) from trivial)
  let φ : CommRingCat.of A ⟶ Γ(pullback u a, V) :=
    (Scheme.ΓSpecIso _).inv ≫ v.appLE ⊤ V (by simp)
  have hφ : Spec.map φ = hV.fromSpec ≫ v := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec]
  let := φ.hom.toAlgebra
  have : Algebra.Etale A Γ(pullback u a, V) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.bijective)
      (HasRingHomProperty.appLE @Etale v inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _)
  let q : Ideal Γ(pullback u a, V) := (hV.primeIdealOf ⟨s' b, hzV⟩).asIdeal
  have hq : q.comap (algebraMap A _) = maximalIdeal A := by
    have : Spec.map φ (hV.primeIdealOf ⟨s' b, hzV⟩) = closedPoint A := by
      rw [hφ, Scheme.Hom.comp_apply, hV.fromSpec_primeIdealOf, hvb]
    exact congr(PrimeSpectrum.asIdeal $this)
  obtain ⟨ψ, hψ⟩ := Algebra.Etale.exists_algHom_comap_maximalIdeal_eq L q hq
  let σ' : Spec (.of A) ⟶ pullback u a :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec
  have hσv : σ' ≫ v = 𝟙 _ := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    change ((ψ (algebraMap A _ x) : A) : L) = x
    rw [ψ.commutes]
    rfl
  have hσ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ' = s' := by
    have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ σ') b = s' b := by
      rw [Scheme.Hom.comp_apply, specMap_residue_apply, Scheme.Hom.comp_apply]
      have : Spec.map (CommRingCat.ofHom ψ.toRingHom) (closedPoint A) =
          hV.primeIdealOf ⟨s' b, hzV⟩ := PrimeSpectrum.ext hψ
      rw [this]
      exact hV.fromSpec_primeIdealOf _
    refine Scheme.Hom.eq_of_comp_eq_of_isSepClosed v _ _ ?_ b hpt ?_
    · rw [Category.assoc, hσv, Category.comp_id, pullback.lift_snd]
    · have : IsSepClosed (ResidueField A) :=
        IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing L
      rw [hpt, hvb]
      exact isSepClosed_residueField_closedPoint A
  refine ⟨σ' ≫ pullback.fst u a, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσv, Category.id_comp]
  · rw [← Category.assoc, hσ, pullback.lift_fst]

/-- A morphism from `α` to `β` that is injective but misses a point of `β`. -/
lemma _root_.ENat.card_add_one_le_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) {b : β} (hb : ∀ a, f a ≠ b) :
    ENat.card α + 1 ≤ ENat.card β := by
  have : Function.Injective (Sum.elim f fun _ : Unit ↦ b) := by
    rintro (a₁ | ⟨⟩) (a₂ | ⟨⟩) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (hf h)
    · exact (hb _ h).elim
    · exact (hb _ h.symm).elim
    · rfl
  simpa using ENat.card_le_card_of_injective this

/-- **Uniqueness of lifts over a valuation ring** along a separated morphism. -/
lemma Scheme.Hom.eq_of_valuationSubring {P Q : Scheme.{u}} (f : P ⟶ Q) [IsSeparated f]
    {L : Type u} [Field L] (A : ValuationSubring L) (l₁ l₂ : Spec (.of A) ⟶ P)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ l₁ =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ l₂) (h₂ : l₁ ≫ f = l₂ ≫ f) :
    l₁ = l₂ := by
  let S : ValuativeCommSq f :=
    { R := A, K := L, i₁ := Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ l₁, i₂ := l₁ ≫ f,
      commSq := ⟨by rw [Category.assoc]⟩ }
  have := IsSeparated.valuativeCriterion f S
  exact congrArg CommSq.LiftStruct.l
    (Subsingleton.elim (⟨l₁, rfl, rfl⟩ : S.commSq.LiftStruct) ⟨l₂, h₁.symm, h₂.symm⟩)

/-- **Geometric fibres drop at points escaping an open subscheme.** Let `u : U ⟶ X` be étale
and separated, factoring as an open immersion `j : U ⟶ Y` followed by a separated `p : Y ⟶ X`.
If `y ∉ U` is a specialization of a point `x ∈ U`, the geometric fibre of `u` over `p y` has
fewer points than some geometric fibre of `u`. -/
theorem Scheme.Hom.card_lifts_add_one_le_of_specializes (u : U ⟶ X) [Etale u] [IsSeparated u]
    (j : U ⟶ Y) [IsOpenImmersion j] (p : Y ⟶ X) [IsSeparated p] (hjp : j ≫ p = u) {x y : Y}
    (hxy : x ⤳ y) (hx : x ∈ Set.range j.base) (hy : y ∉ Set.range j.base) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (g : Spec (.of Ω) ⟶ X),
      ENat.card {s // s ≫ u = X.sepClosurePoint (p y)} + 1 ≤ ENat.card {s // s ≫ u = g} := by
  obtain ⟨L, _, _, A, a, ha, hgen⟩ := Scheme.exists_valuationSubring_of_specializes hxy
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A L))
  let c := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ a ≫ p
  have : IsSepClosed (ResidueField A) :=
    IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing L
  obtain ⟨b⟩ : Nonempty (Spec (.of (ResidueField A))) := inferInstance
  have hcb : c b = p y := by
    simp only [c, Scheme.Hom.comp_apply, specMap_residue_apply, ha]
  refine ⟨L, inferInstance, inferInstance, ι ≫ a ≫ p, ?_⟩
  rw [← hcb, ← u.card_lifts_eq_card_lifts_sepClosurePoint c b]
  choose σ hσu hσs using fun s : {s // s ≫ u = c} ↦
    u.exists_lift_of_valuationSubring A (a ≫ p) s.1 s.2
  have hrange : Set.range (ι ≫ a).base ⊆ Set.range j.base := by
    rintro _ ⟨e, rfl⟩
    rw [hgen e]
    exact hx
  let t : {s // s ≫ u = ι ≫ a ≫ p} :=
    ⟨IsOpenImmersion.lift j (ι ≫ a) hrange, by
      rw [← hjp, IsOpenImmersion.lift_fac_assoc, Category.assoc]⟩
  refine ENat.card_add_one_le_of_injective (f := fun s ↦ ⟨ι ≫ σ s, by
    rw [Category.assoc, hσu]⟩) (b := t) ?_ ?_
  · intro s₁ s₂ h
    have h' : σ s₁ = σ s₂ := Scheme.Hom.eq_of_valuationSubring u A _ _
      congr($h.1) ((hσu s₁).trans (hσu s₂).symm)
    exact Subtype.ext ((hσs s₁).symm.trans (h' ▸ hσs s₂))
  · intro s h
    have hσj : σ s ≫ j = a := Scheme.Hom.eq_of_valuationSubring p A _ _
      (by
        have h1 : ι ≫ σ s = IsOpenImmersion.lift j (ι ≫ a) hrange := congr($h.1)
        rw [← Category.assoc, h1, IsOpenImmersion.lift_fac])
      (by rw [Category.assoc, hjp, hσu])
    apply hy
    rw [← ha, ← hσj]
    exact ⟨_, rfl⟩

/-- In the situation of `Scheme.Hom.card_lifts_add_one_le_of_specializes`, a bound `d + 1` on the
geometric fibres of `u` gives the bound `d` for the geometric fibre over `p y`. -/
theorem Scheme.Hom.card_lifts_le_of_specializes (u : U ⟶ X) [Etale u] [IsSeparated u]
    (j : U ⟶ Y) [IsOpenImmersion j] (p : Y ⟶ X) [IsSeparated p] (hjp : j ≫ p = u) {x y : Y}
    (hxy : x ⤳ y) (hx : x ∈ Set.range j.base) (hy : y ∉ Set.range j.base) {d : ℕ}
    (hd : u.HasGeometricFibersCardLE (d + 1)) :
    ENat.card {s // s ≫ u = X.sepClosurePoint (p y)} ≤ d := by
  obtain ⟨Ω, _, _, g, hg⟩ := u.card_lifts_add_one_le_of_specializes j p hjp hxy hx hy
  have := hg.trans (hd Ω g)
  push_cast at this
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this

end AlgebraicGeometry

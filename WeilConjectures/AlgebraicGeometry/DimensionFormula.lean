/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.HeightAddCoheight

/-!
# The dimension formula for schemes locally of finite type over a field

For a scheme `X` locally of finite type over a field `K` and a point `x ∈ X`,

`dim_x X = dim 𝒪_{X,x} + trdeg_K κ(x)`

(`AlgebraicGeometry.Scheme.topologicalKrullDimAt_eq_ringKrullDim_stalk_add`, blueprint
`lem-kun-dimension-formula`, Stacks `02FX`).

On an affine chart `Spec A ⊆ X` with `x` the prime `p`, `dim 𝒪_{X,x} = ht p` and
`trdeg_K κ(x) = trdeg_K (A ⧸ p) = dim (A ⧸ p)`. Every neighbourhood of `x` contains such a chart,
of dimension at least `ht p + dim (A ⧸ p)`. Conversely, removing the irreducible components of a
chart that do not pass through `x` gives a neighbourhood `Spec A[1/g]` of dimension at most
`ht p + dim (A ⧸ p)`, by the catenarity of finitely generated domains over a field
(`PrimeSpectrum.height_add_coheight_eq_of_finiteType`).
-/

@[expose] public section

universe u

open CategoryTheory Order Topology

namespace AlgebraicGeometry

namespace Scheme

variable {K : Type u} [Field K] {X : Scheme.{u}} (b : X ⟶ Spec (.of K))

/-- Every point of an open `U` of a scheme `X` over a field `K` lies in an affine chart
`Spec A ⟶ X` over `K` contained in `U`. -/
theorem exists_affineChart_over {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (j : Spec (.of A) ⟶ X)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧ Set.range j ⊆ U ∧
        j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  obtain ⟨R, j, _, hx, hU⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  let : Algebra K R := (Spec.preimage (j ≫ b)).hom.toAlgebra
  exact ⟨R, _, _, j, inferInstance, hx, hU, (Spec.map_preimage (j ≫ b)).symm⟩

variable {b}

/-- The ring of an affine chart over `K` of a scheme locally of finite type over `K` is a
finitely generated `K`-algebra. -/
theorem finiteType_of_affineChart [LocallyOfFiniteType b] {A : Type u} [CommRing A]
    [Algebra K A] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    Algebra.FiniteType K A := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
    hj ▸ inferInstance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

/-- On an affine chart `Spec A ⟶ X` over `K`, the `K`-algebra `κ(x)` at the image of a prime
`p` is the residue field of `p`, with `K` acting through `A`. -/
theorem residueFieldHomOfOver_comp_residueFieldMap {A : Type u} [CommRing A] [Algebra K A]
    (j : Spec (.of A) ⟶ X) (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (p : PrimeSpectrum A) :
    CommRingCat.ofHom (residueFieldHomOfOver b (j p)) ≫ j.residueFieldMap p ≫
        (Spec.residueFieldIso (.of A) p).hom =
      CommRingCat.ofHom (algebraMap K A) ≫
        CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField) := by
  have h1 : CommRingCat.ofHom (residueFieldHomOfOver b (j p)) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫ X.Γevaluation (j p) := rfl
  rw [h1, Category.assoc, Category.assoc, Γevaluation_naturality_assoc, ← Category.assoc b.appTop,
    ← Scheme.Hom.comp_appTop, hj, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 : (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).Γevaluation p =
      CommRingCat.ofHom (algebraMap A _) ≫ (Spec.residueFieldIso (.of A) p).inv :=
    (Spec.algebraMap_residueFieldIso_inv (.of A) p).symm
  rw [reassoc_of% h2]
  simp

/-- On an affine chart `Spec A ⟶ X` over `K`, the transcendence degree of `κ(x)` at the image of
a prime `p` is that of `A ⧸ p`: `κ(x)` is the fraction field of `A ⧸ p`. -/
theorem residueFieldTrdeg_eq_trdeg_quotient {A : Type u} [CommRing A] [Algebra K A]
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K A))) (p : PrimeSpectrum A) :
    residueFieldTrdeg b (j p) = Algebra.trdeg K (A ⧸ p.asIdeal) := by
  letI := (residueFieldHomOfOver b (j p)).toAlgebra
  let e : X.residueField (j p) ≅ CommRingCat.of p.asIdeal.ResidueField :=
    asIso (j.residueFieldMap p) ≪≫ Spec.residueFieldIso (.of A) p
  have he : ∀ k : K, e.hom (residueFieldHomOfOver b (j p) k) =
      algebraMap K p.asIdeal.ResidueField k := fun k ↦ by
    have := congrArg (fun φ ↦ φ.hom k) (residueFieldHomOfOver_comp_residueFieldMap j hj p)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    rw [IsScalarTower.algebraMap_apply K A p.asIdeal.ResidueField]
    exact this
  let e' : X.residueField (j p) ≃ₐ[K] p.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) he
  change Algebra.trdeg K (X.residueField (j p)) = _
  rw [e'.trdeg_eq]
  have : FaithfulSMul (A ⧸ p.asIdeal) p.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (A ⧸ p.asIdeal) p.asIdeal.ResidueField)
  have : FaithfulSMul K (A ⧸ p.asIdeal) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K (A ⧸ p.asIdeal)).injective
  have h := Algebra.trdeg_add_eq K (A ⧸ p.asIdeal) p.asIdeal.ResidueField
  rw [Algebra.trdeg_eq_zero (R := A ⧸ p.asIdeal), add_zero] at h
  exact h.symm

/-- On an affine chart `Spec A ⟶ X` over `K` of a scheme locally of finite type over `K`, the
transcendence degree of `κ(x)` at the image of a prime `p` is the coheight `dim (A ⧸ p)` of `p`,
a natural number. -/
theorem exists_coheight_eq_and_residueFieldTrdeg_eq [LocallyOfFiniteType b] {A : Type u}
    [CommRing A] [Algebra K A] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K A))) (p : PrimeSpectrum A) :
    ∃ m : ℕ, coheight p = m ∧ residueFieldTrdeg b (j p) = m := by
  have := finiteType_of_affineChart j hj
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast_of_finiteType K (A ⧸ p.asIdeal)
  refine ⟨m, ?_, ?_⟩
  · have := PrimeSpectrum.coheight_eq_ringKrullDim_quotient p
    rw [hm] at this
    exact_mod_cast this
  · rw [residueFieldTrdeg_eq_trdeg_quotient j hj p,
      Algebra.trdeg_eq_of_ringKrullDim_eq K (A ⧸ p.asIdeal) hm]

/-- On an affine chart `Spec A ⟶ X`, the dimension of the local ring at the image of a prime `p`
is the height of `p`. -/
theorem ringKrullDim_stalk_eq_height {A : Type u} [CommRing A] (j : Spec (.of A) ⟶ X)
    [IsOpenImmersion j] (p : PrimeSpectrum A) :
    ringKrullDim (X.presheaf.stalk (j p)) = height p := by
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion,
    ← idealHeight_eq_coheight (.of A) p, PrimeSpectrum.height_eq_orderHeight]

/-- Blueprint `lem-kun-dimension-formula`: Dimension formula for finite type schemes

Let `K` be a field, `X` a scheme locally of finite type over `K` (structure morphism `b`), and
`x ∈ X`. Then the transcendence degree `trdeg_K κ(x)` is a natural number `t`, and

`dim_x X = dim 𝒪_{X,x} + trdeg_K κ(x)`,

where `dim_x X` is the local dimension `topologicalKrullDimAt x`, the infimum of the dimensions
of the open neighbourhoods of `x` (Stacks `02FX`). -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_add [LocallyOfFiniteType b] (x : X) :
    ∃ t : ℕ, residueFieldTrdeg b x = t ∧
      topologicalKrullDimAt x = ringKrullDim (X.presheaf.stalk x) + t := by
  obtain ⟨A₀, _, _, j₀, _, ⟨p₀, rfl⟩, -, hj₀⟩ := exists_affineChart_over b (U := ⊤) trivial
  have := finiteType_of_affineChart j₀ hj₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing K A₀
  obtain ⟨t, ht, htr⟩ := exists_coheight_eq_and_residueFieldTrdeg_eq j₀ hj₀ p₀
  refine ⟨t, htr, ?_⟩
  rw [ringKrullDim_stalk_eq_height j₀ p₀, ← ht]
  apply le_antisymm
  · -- a neighbourhood `Spec A₀[1/g]` all of whose components pass through `x`
    obtain ⟨g, hg, hmin⟩ := exists_notMem_forall_minimalPrimes_le p₀.asIdeal
    let j : Spec (.of (Localization.Away g)) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (Localization.Away g))) ≫ j₀
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap A₀ (Localization.Away g)))) := IsOpenImmersion.of_isLocalization g
    have hx : j₀ p₀ ∈ j.opensRange := by
      obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge
        (show p₀ ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A₀)) from hg)
      exact ⟨q, by simp [j, ← hq]; rfl⟩
    refine (iInf₂_le _ hx).trans ?_
    calc topologicalKrullDim (j.opensRange : Set X)
        = topologicalKrullDim (Spec (.of (Localization.Away g))) := by
          rw [j.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range]
          rfl
      _ = ringKrullDim (Localization.Away g) :=
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ _ := ringKrullDim_localization_away_le_of_finiteType (K := K) p₀ hmin
  · refine le_iInf₂ fun U hU ↦ ?_
    obtain ⟨A, _, _, j, _, ⟨p, hp⟩, hjU, hj⟩ := exists_affineChart_over b hU
    obtain ⟨t', ht', htr'⟩ := exists_coheight_eq_and_residueFieldTrdeg_eq j hj p
    have htt : t' = t := by
      rw [hp, htr] at htr'
      exact_mod_cast htr'.symm
    have hheight : height p = height p₀ := by
      have h1 := ringKrullDim_stalk_eq_height j p
      rw [hp, ringKrullDim_stalk_eq_height j₀ p₀] at h1
      exact_mod_cast h1.symm
    calc (((height p₀ + coheight p₀ : ℕ∞)) : WithBot ℕ∞)
        = ((height p + coheight p : ℕ∞) : WithBot ℕ∞) := by rw [hheight, ht, ht', htt]
      _ ≤ ringKrullDim A := PrimeSpectrum.height_add_coheight_le p
      _ = topologicalKrullDim (Spec (.of A)) :=
          (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
      _ ≤ topologicalKrullDim U := by
          refine IsInducing.topologicalKrullDim_le
            (f := fun y : Spec (.of A) ↦ (⟨j y, hjU ⟨y, rfl⟩⟩ : U)) ?_
          exact .of_comp (by fun_prop) continuous_subtype_val j.isOpenEmbedding.isInducing

end Scheme

end AlgebraicGeometry

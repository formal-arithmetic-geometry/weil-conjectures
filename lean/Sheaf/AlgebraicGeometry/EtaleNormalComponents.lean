/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.RingTheory.EtaleNormalRing

/-!
# Normal integral components of a Noetherian etale scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, node
`lem-fin-etale-normal-components`, order 1605; Stacks Project, Tag 033C
(blueprint: lem-fin-etale-normal-components).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem normalPair_of_equiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : IsDomain A ∧ IsIntegrallyClosed A) :
    IsDomain B ∧ IsIntegrallyClosed B := by
  let := h.1
  let := h.2
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

private theorem normal_localizations_of_stalks {X : Scheme.{u}}
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) (p : Ideal Γ(X, U)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let x : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  let y : X := hU.fromSpec x
  have hy : y ∈ U := (hU.isoSpec.inv x).2
  let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk y) p := hU.isLocalization_stalk' x hy
  exact normalPair_of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk y)
      (Localization.AtPrime p)).toRingEquiv (hX y)

private theorem etale_normal_stalks {W Y : Scheme.{u}} (f : W ⟶ Y) [Etale f]
    (hY : IsNormalScheme Y) (w : W) :
    IsDomain (W.presheaf.stalk w) ∧ IsIntegrallyClosed (W.presheaf.stalk w) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f w)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hwU (f ⁻¹ᵁ U).isOpen
  have hVnormal := (f.etale_appLE hU hV hVU).isNormalRing
    (normal_localizations_of_stalks hY.2 hU)
  let p := (hV.primeIdealOf ⟨w, hwV⟩).asIdeal
  let := W.presheaf.algebra_section_stalk ⟨w, hwV⟩
  let : IsLocalization.AtPrime (W.presheaf.stalk w) p := hV.isLocalization_stalk ⟨w, hwV⟩
  exact normalPair_of_equiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (W.presheaf.stalk w)).toRingEquiv (hVnormal p)

private theorem components_eq_of_mem {X : Scheme.{u}}
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {C D : Set X} (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    {x : X} (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  let := hX x
  have hr : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn
  obtain ⟨E, hE, hrE⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hr
  have hle (C : Set X) (hC : C ∈ irreducibleComponents X) (hxC : x ∈ C) : C ⊆ E := by
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hgE : hC.1.genericPoint ∈ E := hrE (by
      rw [Scheme.range_fromSpecStalk]
      exact hg.specializes hxC)
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hgE)
      (isClosed_of_mem_irreducibleComponents E hE)
  exact (Set.Subset.antisymm (hle C hC hxC) (hC.2 hE.1 (hle C hC hxC))).trans
    (Set.Subset.antisymm (hle D hD hxD) (hD.2 hE.1 (hle D hD hxD))).symm

private theorem isOpen_component {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {C : Set X} (hC : C ∈ irreducibleComponents X) : IsOpen C := by
  have heq : C = (⋃₀ (irreducibleComponents X \ {C}))ᶜ := by
    ext x
    constructor
    · intro hxC hx
      obtain ⟨D, ⟨hD, hDC⟩, hxD⟩ := hx
      exact hDC (Set.mem_singleton_iff.mpr (components_eq_of_mem hX hD hC hxD hxC))
    · intro hx
      by_contra hxC
      apply hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      intro he
      exact hxC (Set.mem_singleton_iff.mp he ▸ mem_irreducibleComponent)
  rw [heq, Set.sUnion_eq_biUnion]
  exact ((finite_irreducibleComponents_of_isNoetherian (X := X)).sdiff.isClosed_biUnion
    fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl

/-- An etale morphism with Noetherian source and normal integral target has a finite
partition into clopen normal integral open subschemes. Normality uses the convention of
`def-sbc-normal-dominant-galois`, so it includes integrality.

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1605; Stacks Project, Tag 033C
(blueprint: lem-fin-etale-normal-components).

Proof: Choose affine neighborhoods of a source point and its image. Their ring map is etale
by `def-weil-pbc-scheme-conventions`. Normality of the target makes the target affine ring
normal. By `lem-weil-pbc-etale-over-normal-ring-normal` the source affine ring is normal,
so every source stalk is a normal domain and the source is reduced. By
`lem-weil-pbc-noetherian-finite-components`, the Noetherian source has finitely many
irreducible components. Distinct components cannot meet: an intersection point would have
more than one minimal prime in its local ring, contradicting that it is a domain.
Each component is closed, and its complement is the finite union of the other closed
components, hence it is also open. The components cover the source. On each component the
stalks are the source stalks, hence normal domains; reducedness and irreducibility make it
integral as in `def-sbc-normal-dominant-galois`. Enumerate these components by `Fin n`.
The empty source is covered by the empty family (`n = 0`). -/
theorem Etale.exists_clopen_normal_integral_components
    {W Y : Scheme.{u}} (f : W ⟶ Y) [Etale f] [IsNoetherian W]
    (hY : IsNormalScheme Y) :
    ∃ (n : ℕ) (U : Fin n → W.Opens),
      (∀ i, IsClosed (U i : Set W)) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧
      (∀ i, IsNormalScheme (U i).toScheme) := by
  classical
  have hW := etale_normal_stalks f hY
  let : ∀ w : W, _root_.IsReduced (W.presheaf.stalk w) := fun w ↦ by
    let := (hW w).1
    infer_instance
  let : IsReduced W := isReduced_of_isReduced_stalk W
  let : Fintype (irreducibleComponents W) :=
    (finite_irreducibleComponents_of_isNoetherian (X := W)).fintype
  let e := (Fintype.equivFin (irreducibleComponents W)).symm
  let U : Fin (Fintype.card (irreducibleComponents W)) → W.Opens :=
    fun i ↦ ⟨(e i).1, isOpen_component (fun w ↦ (hW w).1) (e i).2⟩
  refine ⟨_, U, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_of_mem_irreducibleComponents _ (e i).2
  · intro i j hij
    apply TopologicalSpace.Opens.coe_disjoint.mp
    refine Set.disjoint_left.mpr fun x hxi hxj ↦ ?_
    exact hij (e.injective (Subtype.ext
      (components_eq_of_mem (fun w ↦ (hW w).1) (e i).2 (e j).2 hxi hxj)))
  · apply top_le_iff.mp
    intro w _
    obtain ⟨i, hi⟩ := e.surjective
      ⟨irreducibleComponent w, irreducibleComponent_mem_irreducibleComponents w⟩
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change w ∈ (e i).1
    rw [hi]
    exact mem_irreducibleComponent
  · intro i
    let : IrreducibleSpace (U i).toScheme := Subtype.irreducibleSpace (e i).2.1
    refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
    intro w
    exact normalPair_of_equiv
      (asIso ((U i).ι.stalkMap w)).commRingCatIsoToRingEquiv (hW w.1)

end AlgebraicGeometry

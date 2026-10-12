module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.Etale.Field

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

theorem Dense.finite_compl_of_topologicalKrullDim_le_one {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1) {U : Set X}
    (hU : IsOpen U) (hd : Dense U) : Uᶜ.Finite := by
  have hcl : ∀ x ∉ U, IsClosed ({x} : Set X) := by
    intro x hx
    set Z := irreducibleComponent x
    have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    obtain ⟨V, hVo, hVne, hVZ⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
    obtain ⟨u, huV, huU⟩ := hd.inter_open_nonempty V hVo hVne
    have : IrreducibleSpace Z := isIrreducible_iff_irreducibleSpace.mp hZ.1
    have hdim : topologicalKrullDim Z ≤ 1 := (topologicalKrullDim_subspace_le X Z).trans h
    have hU' : IsOpen (Subtype.val ⁻¹' U : Set Z) := hU.preimage continuous_subtype_val
    have hc := hU'.isClosed_singleton_of_mem_compl hdim ⟨⟨u, hVZ huV⟩, huU⟩
      (x := ⟨x, mem_irreducibleComponent⟩) hx
    have := hZc.isClosedMap_subtype_val _ hc
    simpa using this
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hcl z hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀]

/-- A finite reduced scheme over a perfect field is étale over it. -/
theorem etale_of_isFinite_of_isReduced [PerfectField k₀] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k₀)) [IsFinite f] [IsReduced Z] : Etale f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  let φ₀ : CommRingCat.of k₀ ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k₀)).inv ≫ f.appTop
  let : Algebra k₀ Γ(Z, ⊤) := φ₀.hom.toAlgebra
  have : Module.Finite k₀ Γ(Z, ⊤) :=
    RingHom.Finite.comp f.finite_appTop (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k₀)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.Etale.of_isReduced_of_perfectField k₀ Γ(Z, ⊤)
  have hf : f = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ Γ(Z, ⊤))) := by
    rw [← Iso.inv_comp_eq, ← Category.comp_id f, ← toSpecΓ_SpecMap_ΓSpecIso_inv,
      Scheme.toSpecΓ_naturality_assoc, Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp]
    rfl
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap k₀ Γ(Z, ⊤)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  rw [hf]
  infer_instance

variable [Finite k₀]

/-- The reduced closed complement of a dense open of a smooth curve is finite over `k₀`. -/
theorem exists_isReduced_isClosedImmersion_range_eq_compl_of_curve {U C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))] :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ C)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))) (_ : IsReduced Z),
      Set.range i.base = (Set.range j.base)ᶜ := by
  have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian C := @IsNoetherian.mk _ inferInstance inferInstance
  have hfin : (Set.range j.base)ᶜ.Finite :=
    Dense.finite_compl_of_topologicalKrullDim_le_one (by exact_mod_cast
      topologicalKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1)
      j.isOpenEmbedding.isOpen_range j.denseRange
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds C)
  have hI : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨I.subschemeι ≫ C ↘ _⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite I.subscheme := by
    have := hfin.to_subtype
    rw [← hI] at this
    exact Finite.of_equiv _ (Equiv.ofInjective _ I.subschemeι.isClosedEmbedding.injective).symm
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    show LocallyOfFiniteType (I.subschemeι ≫ C ↘ _) from inferInstance
  have : LocallyQuasiFinite (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  exact ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, inferInstance,
    IsFinite.of_locallyQuasiFinite _, inferInstance, hI⟩

end AlgebraicGeometry

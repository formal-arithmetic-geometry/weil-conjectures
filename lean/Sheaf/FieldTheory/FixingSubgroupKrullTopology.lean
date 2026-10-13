module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The topology on the Galois group of a finite intermediate field
-/

@[expose] public section

universe u

/-- Source: the Krull neighborhood basis in Mathlib.FieldTheory.KrullTopology,
`krullTopology_mem_nhds_one_iff`; Stacks Project, Tag 0BMJ.
(blueprint: lem-exc-fixing-subgroup-krull-topology)

Proof: Write L for the finite intermediate field and e for fixingSubgroupEquiv L.
A basic neighborhood of the identity in Gal(Ks/L) fixes a finite intermediate
extension E/L. The field E, restricted to K, is finite over K by the tower formula;
the identity linear map carries the finite-dimensional K-module E onto its
restriction of scalars. The preimage under e of this fixing subgroup is the
intersection of L.fixingSubgroup with the corresponding K-fixing subgroup, hence
open in the subspace topology. This proves continuity at the identity, and the
continuous homomorphism criterion gives continuity everywhere. The source is a
closed subgroup of the compact absolute Galois group Gal(Ks/K). The target is
Hausdorff because Ks/L is algebraic (separability descends along the tower).
A continuous bijection from a compact space to a Hausdorff space has continuous
inverse. Apply this to the underlying equivalence of e. This also covers L=K,
L=Ks when finite, and a separably closed K. -/
theorem IntermediateField.continuous_fixingSubgroupEquiv
    (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] (L : IntermediateField K Ks) [FiniteDimensional K L] :
    Continuous L.fixingSubgroupEquiv ∧ Continuous L.fixingSubgroupEquiv.symm := by
  have hc : Continuous L.fixingSubgroupEquiv := by
    apply continuous_of_tendsto_nhds_one L.fixingSubgroupEquiv.toMonoidHom
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff L Ks s).mp hs
    have : FiniteDimensional L E := hE
    have : FiniteDimensional K E := Module.Finite.trans L E
    let f : E →ₗ[K] E.restrictScalars K :=
      { toFun := fun x ↦ ⟨x, x.property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          ext
          exact (E.val.restrictScalars K).toLinearMap.map_smul r x }
    have : FiniteDimensional K (E.restrictScalars K) :=
      Module.Finite.of_surjective f (fun x ↦ ⟨⟨x, x.property⟩, rfl⟩)
    have ho := (E.restrictScalars K).fixingSubgroup_isOpen.preimage
      (continuous_subtype_val : Continuous (Subtype.val : L.fixingSubgroup → Gal(Ks/K)))
    apply Filter.mem_of_superset (ho.mem_nhds (by simp))
    intro g hg
    apply hsub
    intro x
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x x.property
  have : CompactSpace L.fixingSubgroup :=
    isCompact_iff_compactSpace.mp L.fixingSubgroup_isClosed.isCompact
  have : Algebra.IsAlgebraic L Ks := inferInstance
  exact ⟨hc, hc.continuous_symm_of_equiv_compact_to_t2⟩

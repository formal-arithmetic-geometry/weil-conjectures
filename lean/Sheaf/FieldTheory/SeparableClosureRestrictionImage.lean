/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Topology.Separation.Hausdorff

/-!
# Image of restriction between absolute Galois groups

Source: Stacks Project, `fields.tex`, Tags 0BMJ and 0BML
(blueprint: lem-per-galois-restriction-image).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace IntermediateField

/-- Restriction along compatible embeddings of separable closures is continuous, has closed
image, and its image consists exactly of the automorphisms fixing the intersection with `L`.
Source: Stacks Project, `fields.tex`, Tags 0BMJ and 0BML
(blueprint: lem-per-galois-restriction-image).

`restrictRestrictAlgEquivMapHom K Ks L Ls` is Mathlib's canonical restriction homomorphism.
The two scalar towers express compatibility of the embeddings in `Ls`. Normality of `Ks/K`
is inferred from `IsSepClosure K Ks`; no hypothesis is imposed on the extension `L/K`.
The element condition on the right identifies `Ks ∩ L` by taking the inverse image in `Ks`
of the image of `L` in `Ls`. Both Galois groups carry Mathlib's Krull topology.

Proof, following the six steps of the DAG node:
1. By lem-weil-pbc-separable-closure-exists-galois, both closures are Galois. Each
   automorphism of `Ls/L` permutes the roots of the minimal polynomial over `K` of every
   element of `Ks`. Applying this also to its inverse shows that it preserves `Ks`.
   Restriction respects identity and composition, giving the displayed canonical homomorphism.
2. By lem-exc-galois-krull-finite-limit, each Galois group is the limit of its finite Galois
   quotients. By lem-dl-a1-finite-group-limit-profinite, both groups are compact Hausdorff
   totally disconnected topological groups.
3. For any finite intermediate field `F/K` in `Ks`, take a finite `K`-basis `S` of `F`.
   Its image in `Ls` is integral over `L`. By lem-sc-finite-generated-integral-subring,
   `L[S]` is finite dimensional over `L`. It is a field: multiplication by a nonzero
   element is an injective, hence surjective, linear endomorphism. The open subgroup
   fixing this finite field lies in the inverse image of the subgroup fixing `F`.
   Thus restriction is continuous at identity, and translations give continuity everywhere.
4. By lem-dl-a1-compact-hausdorff-closed-map, the image `H` is closed.
5. By lem-exc-etale-galois-fixed-field-subgroup, the fixed field of the full group of
   `Ls/L` is `L`. Thus an element of `Ks` is fixed by `H` exactly when its image lies in
   `L`. Consequently the fixed field of `H` is the intersection `Ks ∩ L`.
6. If an automorphism fixes that intersection, it fixes the fixed field of every open
   subgroup `U` containing `H`. By lem-exc-etale-open-subgroup-fixed-field-galois it
   belongs to `U`. By lem-wf-profinite-closed-subgroup-intersection-open it belongs
   to `H`. The reverse inclusion follows from step 5. No step assumes `L/K` algebraic
   or separable.
-/
theorem separableClosure_restriction_image
    (K : Type u) (L : Type v) (Ks : Type w) (Ls : Type z)
    [Field K] [Field L] [Field Ks] [Field Ls]
    [Algebra K L] [Algebra K Ks] [Algebra L Ls] [Algebra K Ls] [Algebra Ks Ls]
    [IsScalarTower K L Ls] [IsScalarTower K Ks Ls]
    [IsSepClosure K Ks] [IsSepClosure L Ls] :
    Continuous (restrictRestrictAlgEquivMapHom K Ks L Ls) ∧
      IsClosed ((restrictRestrictAlgEquivMapHom K Ks L Ls).range : Set (Ks ≃ₐ[K] Ks)) ∧
      ((restrictRestrictAlgEquivMapHom K Ks L Ls).range : Set (Ks ≃ₐ[K] Ks)) =
        {σ | ∀ x : Ks, algebraMap Ks Ls x ∈ Set.range (algebraMap L Ls) → σ x = x} := by
  classical
  let r := restrictRestrictAlgEquivMapHom K Ks L Ls
  have hres (τ : Ls ≃ₐ[L] Ls) (x : Ks) :
      algebraMap Ks Ls (r τ x) = τ (algebraMap Ks Ls x) :=
    AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) Ks x
  have hcont : Continuous r := by
    apply continuous_of_continuousAt_one r (continuousAt_def.mpr ?_)
    intro N hN
    rw [map_one, krullTopology_mem_nhds_one_iff] at hN
    obtain ⟨F, hF, hFN⟩ := hN
    have : FiniteDimensional K F := hF
    obtain ⟨S, hS⟩ := essFiniteType_iff.mp (inferInstance : Algebra.EssFiniteType K F)
    let T : Finset Ls := S.image (algebraMap Ks Ls)
    let A := adjoin L (T : Set Ls)
    have : FiniteDimensional L A :=
      finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
    apply Filter.mem_of_superset (A.fixingSubgroup_isOpen.mem_nhds (one_mem _))
    intro τ hτ
    apply hFN
    rw [SetLike.mem_coe, ← hS, mem_fixingSubgroup_iff]
    apply (forall_mem_adjoin_smul_eq_self_iff K (r τ)).mpr
    intro x hx
    apply (algebraMap Ks Ls).injective
    change algebraMap Ks Ls (r τ x) = algebraMap Ks Ls x
    rw [hres]
    exact (mem_fixingSubgroup_iff A τ).mp hτ _
      (subset_adjoin L _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hclosed : IsClosed (r.range : Set (Ks ≃ₐ[K] Ks)) := by
    change IsClosed (Set.range r)
    exact hcont.isClosedMap.isClosed_range
  have hfixed (x : Ks) : x ∈ fixedField r.range ↔
      algebraMap Ks Ls x ∈ Set.range (algebraMap L Ls) := by
    rw [mem_fixedField_iff, InfiniteGalois.mem_range_algebraMap_iff_fixed]
    constructor
    · intro hx τ
      rw [← hres, hx (r τ) ⟨τ, rfl⟩]
    · intro hx σ hσ
      obtain ⟨τ, rfl⟩ := hσ
      apply (algebraMap Ks Ls).injective
      rw [hres, hx τ]
  refine ⟨hcont, hclosed, ?_⟩
  ext σ
  change σ ∈ r.range ↔ _
  have hfixing : (fixedField r.range).fixingSubgroup = r.range :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨r.range, hclosed⟩
  rw [← hfixing]
  simp only [mem_fixingSubgroup_iff, hfixed, Set.mem_ofPred_eq]

end IntermediateField

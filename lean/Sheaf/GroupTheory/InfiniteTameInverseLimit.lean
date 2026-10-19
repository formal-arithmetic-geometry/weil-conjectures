/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.GroupTheory.PGroup

/-!
# Inverse limits of finite group extensions with p-group kernels

Source: Stacks Project, Tag 0BUA, `lemma-structure-decomposition`, final proof paragraph;
blueprint `lem-exc-dvr-galois`, second proof paragraph
(blueprint: lem-exc-infinite-tame-inverse-limit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace ProfiniteGrp

/-- The canonical map on the explicit compatible-family limits, obtained from Mathlib's
limit universal property. Its coordinates are the components of `θ`.
Source: Stacks Project, Tag 0BUA, final proof paragraph
(blueprint: lem-exc-infinite-tame-inverse-limit). -/
noncomputable def finiteExtensionLimitMap {Λ : Type u} [PartialOrder Λ]
    {I C : Λᵒᵖ ⥤ ProfiniteGrp.{u}} (θ : I ⟶ C) : limit I →ₜ* limit C :=
  ((limitConeIsLimit C).map (limitCone I) θ).hom

/-- The subgroup of compatible families whose every coordinate belongs to `P j`.
Mathlib supplies the product subgroup, its inverse image, and the subspace topology.
Source: Stacks Project, Tag 0BUA, final proof paragraph, `P = lim P_λ`
(blueprint: lem-exc-infinite-tame-inverse-limit). -/
def finiteExtensionLimitKernel {Λ : Type u} [PartialOrder Λ]
    (I : Λᵒᵖ ⥤ ProfiniteGrp.{u}) (P : ∀ j : Λᵒᵖ, Subgroup (I.obj j)) :
    Subgroup (limit I) :=
  (Subgroup.pi Set.univ P).comap (limitConePtAux I).subtype

/-- Taking inverse limits preserves the finite exact group sequences and gives a kernel
whose every finite continuous quotient has prime-power order.
Source: Stacks Project, Tag 0BUA, `lemma-structure-decomposition`, final proof paragraph;
blueprint `lem-exc-dvr-galois`, second proof paragraph
(blueprint: lem-exc-infinite-tame-inverse-limit).

The diagrams on `Λᵒᵖ` encode the identity and composition laws. The natural
transformation encodes compatibility of the finite quotient homomorphisms. The finite
objects carry the discrete topology. Both limits are Mathlib's actual subgroups of
products, with their subspace topologies. The kernel helper imposes exactly the further
coordinate conditions `x j ∈ P j`. The quotient uses Mathlib's quotient topology; the
normality witness supplies its group structure explicitly.

Proof, following the node's five steps:
1. Mathlib's explicit limits provide compact Hausdorff topological groups and the
   continuous coordinatewise homomorphism, with its displayed coordinate formula.
2. For a compatible `c`, the finite nonempty fibres of `θ.app j` form an inverse system
   by naturality. Mathlib's finite inverse-system nonemptiness theorem gives a compatible
   lift, proving surjectivity on limits; no surjectivity of fibre transitions is needed.
3. The kernel identity follows coordinatewise. The kernel is closed as the inverse image
   of the identity singleton and normal as a homomorphism kernel. The induced quotient
   homomorphism is bijective and continuous. Compactness of its source and Hausdorffness
   of its target give continuity of the inverse, with the displayed coset normalization.
4. The kernel of a continuous map to a finite discrete group is an identity neighbourhood,
   so it contains a product cylinder restricting finitely many coordinates. Choose an
   index above these coordinates, using any index if the finite set is empty. Compatibility
   shows that the kernel of evaluation at this index lies in the given map's kernel.
5. Descend the given surjective map through the image of this coordinate evaluation.
   That image is a subgroup of the finite p-group `P j`, hence a p-group; its surjective
   image is again a p-group. Finiteness and primality now give order `p^n`, including the
   trivial quotient of order `p^0`. Surjectivity of kernel projections is unnecessary.
-/
theorem finiteExtension_inverseLimit_exact_pro_p
    {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (p : ℕ) (hp : p.Prime) (I C : Λᵒᵖ ⥤ ProfiniteGrp.{u})
    [∀ j : Λᵒᵖ, Finite (I.obj j)] [∀ j : Λᵒᵖ, Finite (C.obj j)]
    [∀ j : Λᵒᵖ, DiscreteTopology (I.obj j)]
    [∀ j : Λᵒᵖ, DiscreteTopology (C.obj j)]
    (P : ∀ j : Λᵒᵖ, Subgroup (I.obj j)) [∀ j : Λᵒᵖ, (P j).Normal]
    (hPorder : ∀ j : Λᵒᵖ, ∃ n : ℕ, Nat.card (P j) = p ^ n)
    (θ : I ⟶ C) (hθsurj : ∀ j : Λᵒᵖ, Function.Surjective (θ.app j))
    (hθker : ∀ j : Λᵒᵖ, (θ.app j).hom.toMonoidHom.ker = P j)
    (hIsurj : ∀ {j k : Λᵒᵖ} (f : j ⟶ k), Function.Surjective (I.map f))
    (hCsurj : ∀ {j k : Λᵒᵖ} (f : j ⟶ k), Function.Surjective (C.map f))
    (hPsurj : ∀ {j k : Λᵒᵖ} (f : j ⟶ k),
      (P j).map (I.map f).hom.toMonoidHom = P k) :
    (∀ (x : limit I) (j : Λᵒᵖ),
      (finiteExtensionLimitMap θ x).val j = θ.app j (x.val j)) ∧
    Function.Surjective (finiteExtensionLimitMap θ) ∧
    (finiteExtensionLimitMap θ).toMonoidHom.ker = finiteExtensionLimitKernel I P ∧
    IsClosed (finiteExtensionLimitKernel I P : Set (limit I)) ∧
    (∃ hnormal : (finiteExtensionLimitKernel I P).Normal,
      ∃ e : @ContinuousMulEquiv
        (limit I ⧸ finiteExtensionLimitKernel I P) inferInstance (limit C) inferInstance
        (@QuotientGroup.Quotient.group (limit I) inferInstance
          (finiteExtensionLimitKernel I P) hnormal).toMul inferInstance,
        ∀ x : limit I, e (QuotientGroup.mk x) = finiteExtensionLimitMap θ x) ∧
    (∀ (Q : Type v) [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (f : finiteExtensionLimitKernel I P →ₜ* Q),
      Function.Surjective f → ∃ n : ℕ, Nat.card Q = p ^ n) := by
  classical
  have _ := @hIsurj
  have _ := @hCsurj
  have _ := @hPsurj
  clear hIsurj hCsurj hPsurj
  have hcoord (x : limit I) (j : Λᵒᵖ) :
      (finiteExtensionLimitMap θ x).val j = θ.app j (x.val j) := by
    rfl
  have hsurj : Function.Surjective (finiteExtensionLimitMap θ) := by
    intro c
    -- Finite fibres have a compatible family without surjectivity of their transitions.
    let F : Λᵒᵖ ⥤ Type u :=
      { obj := fun j ↦ {x : I.obj j // θ.app j x = c.val j}
        map := fun {j k} f ↦ ↾fun x ↦ ⟨I.map f x.val, by
          change (I.map f ≫ θ.app k) x.val = c.val k
          rw [θ.naturality]
          change C.map f (θ.app j x.val) = c.val k
          rw [x.property]
          exact c.property f⟩
        map_id := by
          intro j
          ext x
          exact congrArg (fun f ↦ f x.val) (I.map_id j)
        map_comp := by
          intro j k l f g
          ext x
          exact congrArg (fun f ↦ f x.val) (I.map_comp f g) }
    have (j : Λᵒᵖ) : Nonempty (F.obj j) := by
      obtain ⟨x, hx⟩ := hθsurj j (c.val j)
      exact ⟨⟨x, hx⟩⟩
    obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system F
    refine ⟨⟨fun j ↦ (x j).val, ?_⟩, ?_⟩
    · intro j k f
      exact congrArg Subtype.val (hx f)
    · apply limit_ext
      intro j
      exact (x j).property
  have hker : (finiteExtensionLimitMap θ).toMonoidHom.ker =
      finiteExtensionLimitKernel I P := by
    ext x
    change finiteExtensionLimitMap θ x = 1 ↔ ∀ j ∈ Set.univ, x.val j ∈ P j
    constructor
    · intro hx j _
      rw [← hθker j]
      change θ.app j (x.val j) = 1
      exact congrArg (fun y : limit C ↦ y.val j) hx
    · intro hx
      apply limit_ext
      intro j
      have hj := hx j (Set.mem_univ j)
      rw [← hθker j] at hj
      exact hj
  have hclosed : IsClosed (finiteExtensionLimitKernel I P : Set (limit I)) := by
    rw [← hker]
    exact isClosed_singleton.preimage (finiteExtensionLimitMap θ).continuous
  refine ⟨hcoord, hsurj, hker, hclosed, ?_, ?_⟩
  · have hn : (finiteExtensionLimitKernel I P).Normal := by
      rw [← hker]
      infer_instance
    let := hn
    let e : (limit I ⧸ finiteExtensionLimitKernel I P) ≃* limit C :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
    have he : Continuous e := by
      apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      exact (finiteExtensionLimitMap θ).continuous
    exact ⟨hn, { e with continuous_toFun := he
                        continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 },
      fun x ↦ rfl⟩
  · intro Q _ _ _ _ f hf
    have hnhds : {x | f x = 1} ∈ 𝓝 (1 : finiteExtensionLimitKernel I P) :=
      ((isOpen_discrete ({1} : Set Q)).preimage f.continuous).mem_nhds (map_one f)
    rw [nhds_subtype, nhds_subtype, Filter.comap_comap] at hnhds
    obtain ⟨V, hV, hVK⟩ := Filter.mem_comap.mp hnhds
    rw [nhds_pi] at hV
    obtain ⟨S, U, hU, hUV⟩ := Filter.mem_pi'.mp hV
    have hbound : ∃ j : Λᵒᵖ, ∀ k ∈ S, Nonempty (j ⟶ k) := by
      clear hUV
      induction S using Finset.induction_on with
      | empty => exact ⟨Classical.arbitrary _, by simp⟩
      | @insert a S ha ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨l, hal, hjl⟩ := exists_ge_ge a.unop j.unop
        refine ⟨Opposite.op l, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact ⟨(homOfLE hal).op⟩
        · obtain ⟨g⟩ := hj k hk
          exact ⟨(homOfLE hjl).op ≫ g⟩
    obtain ⟨j, hj⟩ := hbound
    let π : finiteExtensionLimitKernel I P →* P j :=
      { toFun := fun x ↦ ⟨x.val.val j, x.property j (Set.mem_univ j)⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    have hle : π.ker ≤ f.toMonoidHom.ker := by
      intro x hx
      apply hVK
      apply hUV
      intro k hk
      obtain ⟨g⟩ := hj k hk
      have heq : x.val.val j = 1 := congrArg Subtype.val hx
      have hkone : x.val.val k = 1 := by
        rw [← x.val.property g, heq]
        exact map_one (I.map g).hom
      change x.val.val k ∈ U k
      rw [hkone]
      exact mem_of_mem_nhds (hU k)
    -- Descend through the coordinate image; evaluation itself need not be surjective.
    let φ : π.range →* Q := π.rangeRestrict.liftOfSurjective π.rangeRestrict_surjective
      ⟨f.toMonoidHom, by simpa only [MonoidHom.ker_rangeRestrict] using hle⟩
    have hφ (x : finiteExtensionLimitKernel I P) : φ (π.rangeRestrict x) = f x := by
      exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
    have hφsurj : Function.Surjective φ := by
      intro q
      obtain ⟨x, rfl⟩ := hf q
      exact ⟨π.rangeRestrict x, hφ x⟩
    have hpj : IsPGroup p (P j) := by
      obtain ⟨n, hn⟩ := hPorder j
      exact IsPGroup.of_card hn
    have : Fact p.Prime := ⟨hp⟩
    exact ((hpj.to_subgroup π.range).of_surjective φ hφsurj).exists_card_eq

end ProfiniteGrp

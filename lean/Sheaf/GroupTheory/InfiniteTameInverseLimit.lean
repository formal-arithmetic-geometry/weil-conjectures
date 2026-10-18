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

Proof, following the node's eight steps:
1. Compatibility equations and the coordinate conditions defining the kernel are closed
   in the products of finite discrete groups. They are preserved by group operations.
   The kernel's subspace topology is also the one from the product of the `P j`.
2. The limits are closed subgroups of products of finite groups, hence profinite.
3. Naturality of `θ` gives the coordinatewise homomorphism; finite discrete coordinates
   give continuity. Its kernel is precisely the coordinatewise subgroup, hence normal.
4. For a compatible `c`, the finite nonempty fibres of `θ.app j` form an inverse system.
   Their transitions are onto: adjust a chosen lift by an element of `P j`, lifted along
   the surjective kernel transition. The finite inverse-system nonemptiness theorem
   gives a compatible lift of `c`, proving surjectivity on limits.
5. The induced quotient homomorphism is bijective by the kernel identity and
   surjectivity. Compactness of the source and Hausdorffness of the target show that
   it is a homeomorphism, with the displayed normalization on cosets.
6. Apply finite inverse-system projection surjectivity to the `P j`. Thus every kernel
   coordinate projection is onto.
7. The kernel of any continuous map to a finite discrete group contains a basic
   identity neighbourhood restricting finitely many coordinates. Choose an upper bound
   of those indices (any index if none occur). The corresponding coordinate kernel is
   contained in the map's kernel.
8. Therefore a finite continuous quotient factors surjectively through one `P j`.
   Counting cosets shows that its order divides `|P j| = p^n`; primality of `p` makes
   that order a power of `p`, including the trivial quotient of order `p^0`.
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
  sorry

end ProfiniteGrp

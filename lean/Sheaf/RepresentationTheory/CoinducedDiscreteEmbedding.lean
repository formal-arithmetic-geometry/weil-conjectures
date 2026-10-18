/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Mathlib.Topology.LocallyConstant.Algebra
import Sheaf.Topology.ContinuousOpenNormalStabilizer

/-!
# Coinduced embeddings of discrete continuous modules

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology.
The coinduced embedding is the agent-written comparison ingredient
(blueprint: lem-exc-coinduced-discrete-embedding).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- Discrete continuous modules admit the natural injective orbit-map embedding into
continuous functions with right translation. `LocallyConstant G M.obj.V` is exactly
`Cont(G, M)` with discrete codomain, and its module operations are pointwise.
The linear equivalences identify the coinduced objects with those function modules.

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology
(blueprint: lem-exc-coinduced-discrete-embedding).

Proof: (1) Pointwise operations give the function module, and precomposition by right
multiplication gives a linear left action: translating successively by `k` then `h`
evaluates at `x * h * k`, and translation by one is the identity.
(2) `lem-exc-coinduced-functions-open-stabilizer` supplies an open normal subgroup
under whose right translations any continuous function is invariant. Its stabilizer
contains that subgroup, so is open; hence the coinduced object belongs to
`DiscreteContinuousRep`, the category used in `lem-exc-discrete-modules-abelian`.
(3) The orbit map is locally constant on the open left cosets of each element's
stabilizer. It is linear pointwise and equivariant since `(x * h) m = x (h m)`.
Evaluation at one proves injectivity. Equivariant linear maps commute with the orbit
maps pointwise, giving naturality; on functions the coinduced map is postcomposition. -/
theorem exists_coinduced_discrete_embedding
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ D : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        DiscreteContinuousRep.{v, u, max u w} A G,
      ∃ e : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        (D.obj M).obj.V ≃ₗ[A] LocallyConstant G M.obj.V,
      ∃ ι : 𝟭 (DiscreteContinuousRep.{v, u, max u w} A G) ⟶ D,
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G)
          (h : G) (f : (D.obj M).obj.V) (x : G),
          e M ((D.obj M).obj.ρ h f) x = e M f (x * h)) ∧
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (a : M ⟶ N)
          (f : (D.obj M).obj.V) (x : G),
          e N ((D.map a).hom.hom f) x = a.hom.hom (e M f x)) ∧
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (m : M.obj.V) (x : G),
          e M ((ι.app M).hom.hom m) x = M.obj.ρ x m) ∧
        (∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
          Function.Injective (ι.app M).hom.hom) := by
  let ρ (M : DiscreteContinuousRep.{v, u, max u w} A G) :
      Representation A G (LocallyConstant G M.obj.V) :=
    { toFun := fun h ↦ LocallyConstant.comapₗ A ⟨fun x ↦ x * h, continuous_mul_const h⟩
      map_one' := by ext f x; simp
      map_mul' := by intro h k; ext f x; simp [mul_assoc] }
  have hopen (M : DiscreteContinuousRep.{v, u, max u w} A G)
      (f : LocallyConstant G M.obj.V) : IsOpen {h : G | ρ M h f = f} := by
    let : TopologicalSpace M.obj.V := ⊥
    let : DiscreteTopology M.obj.V := ⟨rfl⟩
    obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
      (ProfiniteGrp.of G) M.obj.V f f.continuous
    let H : Subgroup G :=
      { carrier := {h | ρ M h f = f}
        one_mem' := by simp
        mul_mem' := by
          intro h k hh hk
          change ρ M (h * k) f = f
          rw [map_mul, Module.End.mul_apply, hk, hh]
        inv_mem' := by
          intro h hh
          have he := congrArg (fun z ↦ ρ M h⁻¹ z) hh
          simpa [← Module.End.mul_apply, ← map_mul] using he.symm }
    have hle : (U : Set G) ⊆ H := by
      intro h hh
      change ρ M h f = f
      ext x
      exact hU x h hh
    exact H.isOpen_of_openSubgroup (U := U.toOpenSubgroup) hle
  let dObj (M : DiscreteContinuousRep.{v, u, max u w} A G) :
      DiscreteContinuousRep.{v, u, max u w} A G :=
    ⟨Rep.of (ρ M), hopen M⟩
  let dMap {M N : DiscreteContinuousRep.{v, u, max u w} A G} (a : M ⟶ N) :
      dObj M ⟶ dObj N :=
    ObjectProperty.homMk (Rep.ofHom
      { toLinearMap := LocallyConstant.mapₗ A a.hom.hom.toLinearMap
        isIntertwining' := by intro h; ext f x; rfl })
  let D : DiscreteContinuousRep.{v, u, max u w} A G ⥤
      DiscreteContinuousRep.{v, u, max u w} A G :=
    { obj := dObj
      map := fun a ↦ dMap a
      map_id := by
        intro M
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro f
        apply LocallyConstant.ext
        intro x
        rfl
      map_comp := by
        intro M N P a b
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro f
        apply LocallyConstant.ext
        intro x
        rfl }
  let orbit (M : DiscreteContinuousRep.{v, u, max u w} A G) (m : M.obj.V) :
      LocallyConstant G M.obj.V :=
    { toFun := fun x ↦ M.obj.ρ x m
      isLocallyConstant := by
        rw [IsLocallyConstant.iff_exists_open]
        intro x
        refine ⟨(fun y : G ↦ x⁻¹ * y) ⁻¹' {h | M.obj.ρ h m = m},
          (M.property m).preimage (continuous_const_mul _), ?_, ?_⟩
        · simp
        · intro y hy
          change M.obj.ρ (x⁻¹ * y) m = m at hy
          have he := congrArg (fun z ↦ M.obj.ρ x z) hy
          simpa [← Module.End.mul_apply, ← map_mul] using he }
  let orbitMap (M : DiscreteContinuousRep.{v, u, max u w} A G) : M ⟶ D.obj M :=
    ObjectProperty.homMk (Rep.ofHom
      { toLinearMap :=
          { toFun := orbit M
            map_add' := by
              intro m n
              apply LocallyConstant.ext
              intro x
              exact map_add (M.obj.ρ x) m n
            map_smul' := by
              intro a m
              apply LocallyConstant.ext
              intro x
              exact (M.obj.ρ x).map_smul a m }
        isIntertwining' := by
          intro h
          apply LinearMap.ext
          intro m
          apply LocallyConstant.ext
          intro x
          change M.obj.ρ x (M.obj.ρ h m) = M.obj.ρ (x * h) m
          simp [map_mul, Module.End.mul_apply] })
  let ι : 𝟭 (DiscreteContinuousRep.{v, u, max u w} A G) ⟶ D :=
    { app := orbitMap
      naturality := by
        intro M N a
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro m
        apply LocallyConstant.ext
        intro x
        change N.obj.ρ x (a.hom.hom m) = a.hom.hom (M.obj.ρ x m)
        exact (Rep.hom_comm_apply a.hom x m).symm }
  refine ⟨D, fun M ↦ LinearEquiv.refl A _, ι, ?_, ?_, ?_, ?_⟩
  · intro M h f x
    rfl
  · intro M N a f x
    rfl
  · intro M m x
    rfl
  · intro M m n h
    have he := congrArg (fun f : LocallyConstant G M.obj.V ↦ f (1 : G)) h
    change M.obj.ρ 1 m = M.obj.ρ 1 n at he
    simpa using he

end Rep

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker K1
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
import Sheaf.RepresentationTheory.PrimaryPGroupFiltration
import Mathlib.GroupTheory.Sylow

/-!
# Sylow reduction of finite primary discrete modules

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-sylow-module-filtration`;
Stacks Project, Tags 0A3R, 0GIZ and 0GJ0 (blueprint: lem-sc-sylow-module-filtration).
-/

@[expose] public section

universe u v

namespace Rep

/-- A finite `ℓ`-primary discrete continuous module admits an open subgroup of index
prime to `ℓ` and an invariant finite filtration with trivial `𝔽_ℓ` successive quotients.
The quotient clauses are expressed without choosing scalar structures: `ℓ • x` lies in
the preceding term, so that the quotient is canonically a `ZMod ℓ`-module, and `g x - x`
lies in the preceding term, so that the induced action is trivial. There is no rank
condition on the quotients. Repeated terms, including the zero module's one-term chain,
are allowed.

Proof: (1) The action homomorphism to units in the endomorphism ring has finite
image Q because the module is finite. Its kernel is the finite intersection of
the open stabilizers supplied by `DiscreteContinuousRep`.
(2) Choose an `ℓ`-Sylow subgroup P of Q using
`lem-weil-pbc-sylow-subgroup-prime-index`. Its inverse image H contains the open
kernel, hence is open. Surjectivity onto Q identifies the index of H with the
prime-to-`ℓ` index of P.
(3) Apply `Representation.exists_primary_filtration_of_isPGroup` to the P-action
on M. That theorem enlarges proper stable subgroups using fixed-point counting
and Cauchy's theorem, then obtains a full chain by finite maximality. Pull the
chain's stability and successor conditions back along H → P. The zero module
is included by a chain of length zero.

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-sylow-module-filtration`;
Stacks Project, Tags 0A3R, 0GIZ and 0GJ0 (blueprint: lem-sc-sylow-module-filtration). -/
theorem exists_openSubgroup_primary_module_filtration
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (M : DiscreteContinuousRep.{0, u, v} ℤ G)
    [Finite M.obj.V] (hM : IsPGroup ℓ (Multiplicative M.obj.V)) :
    ∃ H : OpenSubgroup G, H.toSubgroup.index.Coprime ℓ ∧
      ∃ (n : ℕ) (F : Fin (n + 1) → AddSubgroup M.obj.V),
        Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
        (∀ (i : Fin (n + 1)) (g : H) (x : M.obj.V),
          x ∈ F i → M.obj.ρ (g : G) x ∈ F i) ∧
        (∀ (i : Fin n) (x : M.obj.V), x ∈ F i.succ →
          ℓ • x ∈ F i.castSucc ∧
            ∀ g : H, M.obj.ρ (g : G) x - x ∈ F i.castSucc) := by
  classical
  let : Module ℤ M.obj.V := M.obj.hV2
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : Finite (Module.End ℤ M.obj.V) :=
    Finite.of_injective (fun f : Module.End ℤ M.obj.V ↦ (f : M.obj.V → M.obj.V))
      DFunLike.coe_injective
  let f := M.obj.ρ.toHomUnits
  let Q := f.range
  let π : G →* Q := f.rangeRestrict
  let P : Sylow ℓ Q := Classical.choice inferInstance
  let S : Subgroup G := P.toSubgroup.comap π
  have hker : IsOpen (M.obj.ρ.ker : Set G) := by
    have heq : (M.obj.ρ.ker : Set G) =
        ⋂ x : M.obj.V, {g : G | M.obj.ρ g x = x} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hg x
        exact congrArg (fun a : Module.End ℤ M.obj.V ↦ a x) hg
      · intro hg
        ext x
        exact hg x
    rw [heq]
    exact isOpen_iInter_of_finite M.property
  have hle : M.obj.ρ.ker ≤ S := by
    intro g hg
    change π g ∈ P.toSubgroup
    have hfg : f g = 1 := by
      apply Units.ext
      exact hg
    have hπg : π g = 1 := Subtype.ext hfg
    rw [hπg]
    exact P.one_mem
  let H : OpenSubgroup G := ⟨S, Subgroup.isOpen_mono hle hker⟩
  have hindex : H.toSubgroup.index.Coprime ℓ := by
    change (P.toSubgroup.comap π).index.Coprime ℓ
    rw [P.toSubgroup.index_comap_of_surjective f.rangeRestrict_surjective]
    exact (hℓ.coprime_iff_not_dvd.mpr P.not_dvd_index).symm
  let ρP : Representation ℤ P.toSubgroup M.obj.V :=
    (Units.coeHom (Module.End ℤ M.obj.V)).comp (f.range.subtype.comp P.toSubgroup.subtype)
  obtain ⟨n, F, hmono, hzero, htop, hstable, hstep⟩ :=
    Representation.exists_primary_filtration_of_isPGroup P.toSubgroup ℓ hℓ
      P.isPGroup' M.obj.V ρP hM
  refine ⟨H, hindex, n, F, hmono, hzero, htop, ?_, ?_⟩
  · intro i g x hx
    exact hstable i ⟨π g, g.property⟩ x hx
  · intro i x hx
    obtain ⟨hkill, htriv⟩ := hstep i x hx
    exact ⟨hkill, fun g ↦ htriv ⟨π g, g.property⟩⟩

end Rep

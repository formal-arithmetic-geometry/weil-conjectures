/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Metrizable.Basic
import Sheaf.Topology.ProfiniteProductFiniteOscillation
import Sheaf.Topology.CountableFiniteCoordinateImages
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Hausdorff

/-!
# Metrizable profinite quotients for one metric-valued function

Source: main-20261015 blueprint, `sec-six-functors-basics`, direct-images proof,
paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-profinite-metric-function-quotients).
The topological argument is an agent-formulated auxiliary lemma; an exact literature
reference remains WANTED in the DAG source. The blueprint paragraph motivates its application.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Topology

namespace Profinite

/-- A continuous metric-valued function on `S × G^r` descends through simultaneous
metrizable profinite space and group quotients. Completeness of the target is not needed.
Source: main-20261015 blueprint, direct-images proof, paragraph (3), scalar tame-kernel
expansion (blueprint: lem-sfb-profinite-metric-function-quotients); agent-formulated
auxiliary lemma, exact literature reference WANTED.

Proof:
1. The clopen basis of `S` and open normal subgroup basis of `G` supply the hypotheses
   of `lem-sfb-profinite-product-finite-oscillation`.
2. Apply that lemma with epsilon `1 / (n + 1)` for each natural `n`. It gives finite
   discrete spaces `A_n`, finite discrete quotient groups `B_n`, and continuous maps
   whose common fibres have oscillation less than that epsilon. Empty `S` is included.
3. Apply `lem-sfb-countable-finite-coordinate-images` to these coordinate maps. Their
   concrete diagonal images give metrizable profinite `S₀` and `G₀`, with continuous
   surjections `p` and `q`, the latter a homomorphism. Equality in an image is equivalent
   to equality in every finite coordinate.
4. The product map `R = p × q^r` is continuous and onto. Equal `R`-images force distances
   of `f`-values below `1 / (n + 1)` for every `n`. A positive distance would exceed one
   such bound by `exists_nat_one_div_lt`. Thus `f` is constant on every `R`-fibre in `Y`.
5. The domain of `R` is compact by product compactness, including
   `lem-weil-pbc-tychonoff-product-quasi-compact`, and its target is Hausdorff. Hence
   `lem-sfb-compact-hausdorff-surjection-quotient` makes `R` a quotient map.
6. Use `Topology.IsQuotientMap.lift` and its `lift_comp` identity to obtain the continuous
   descended function and the required factorization. No completion of `Y` is involved.
   Countable products and their image subtypes stay in the original universe, as in
   `def-weil-size-convention`.
-/
theorem exists_metrizable_quotients_factorization
    (S : Profinite.{u}) (G : ProfiniteGrp.{u}) (r : ℕ) (hr : 1 ≤ r)
    (Y : Type v) [MetricSpace Y] (f : C(S × (Fin r → G), Y)) :
    ∃ (S₀ : Profinite.{u}) (G₀ : ProfiniteGrp.{u}),
      TopologicalSpace.MetrizableSpace S₀ ∧ TopologicalSpace.MetrizableSpace G₀ ∧
      ∃ (p : C(S, S₀)) (q : G →ₜ* G₀) (f₀ : C(S₀ × (Fin r → G₀), Y)),
        Function.Surjective p ∧ Function.Surjective q ∧
        ∀ x : S × (Fin r → G), f x = f₀ (p x.1, fun i : Fin r => q (x.2 i)) := by
  classical
  have hG : ∀ U ∈ nhds (1 : G), ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U := by
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV, h1⟩
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
    exact ⟨N, hN.trans hVU⟩
  have hfinite := fun n : ℕ ↦
    f.exists_finite_partition_openNormalSubgroup_small_oscillation
      S isTopologicalBasis_isClopen G hG r hr Y (1 / (n + 1 : ℝ)) (by positivity)
  choose P N hP hpart hclopen hfin hdisc hcont hsurj p hmem hpcont hpsurj hosc
    using hfinite
  let A : ℕ → Type u := fun n ↦ P n
  let B : ℕ → Type u := fun n ↦ G ⧸ (N n).toSubgroup
  let tA : ∀ n, TopologicalSpace (A n) := fun _ ↦ ⊥
  let dA : ∀ n, DiscreteTopology (A n) := fun _ ↦ ⟨rfl⟩
  let fA : ∀ n, Finite (A n) := fun n ↦ (hP n).to_subtype
  let fB : ∀ n, Finite (B n) := hfin
  let dB : ∀ n, DiscreteTopology (B n) := hdisc
  let q : ∀ n, G →* B n := fun n ↦ QuotientGroup.mk' (N n).toSubgroup
  obtain ⟨hp, hpon, hSc, hSt, _, hSm, hSd, hq, hqon, hGt, hGc, hG2, hGm, hGd,
    _, _, hpiff, hqiff⟩ :=
    Topology.countable_finite_coordinate_images S G A B p hpcont q hcont
  let S₀ := Profinite.of (Set.range (fun s n ↦ p n s))
  let G₀ := ProfiniteGrp.of (MonoidHom.pi q).range
  let p₀ : C(S, S₀) := ⟨Set.rangeFactorization (fun s n ↦ p n s), hp⟩
  let q₀ : G →ₜ* G₀ := ⟨(MonoidHom.pi q).rangeRestrict, hq⟩
  let R : C(S × (Fin r → G), S₀ × (Fin r → G₀)) :=
    ⟨fun x ↦ (p₀ x.1, fun i ↦ q₀ (x.2 i)),
      (p₀.continuous.comp continuous_fst).prodMk
        (continuous_pi fun i ↦ q₀.continuous.comp ((continuous_apply i).comp continuous_snd))⟩
  have hRon : Function.Surjective R := by
    rintro ⟨s, g⟩
    obtain ⟨s', hs⟩ := hpon s
    choose g' hg using fun i ↦ hqon (g i)
    exact ⟨(s', g'), Prod.ext hs (funext hg)⟩
  have hRf : Function.FactorsThrough f R := by
    intro x x' hxx
    have hs := (hpiff x.1 x'.1).mp (congrArg Prod.fst hxx)
    have hg : ∀ i n, q n (x.2 i) = q n (x'.2 i) := fun i ↦
      (hqiff (x.2 i) (x'.2 i)).mp (congrFun (congrArg Prod.snd hxx) i)
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    by_contra h
    have hd : 0 < dist (f x) (f x') := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
    exact (not_lt_of_ge hn.le) (hosc n x.1 x'.1 x.2 x'.2 (hs n) (fun i ↦ hg i n))
  have hR : Topology.IsQuotientMap R :=
    .of_surjective_continuous hRon R.continuous
  refine ⟨S₀, G₀, hSm, hGm, p₀, q₀, hR.lift f hRf, hpon, hqon, ?_⟩
  intro x
  exact (congrArg (fun k : C(S × (Fin r → G), Y) ↦ k x) (hR.lift_comp f hRf)).symm

end Profinite

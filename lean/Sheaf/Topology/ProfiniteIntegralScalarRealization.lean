/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Topology.ProfiniteIntegralScalarDefinitions
import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.Topology.ProfiniteIntegralModuleTopology
import Sheaf.Topology.ProfiniteIntegralScalarComparison
import Sheaf.Topology.ProfiniteUniversalSectionMorphism

/-! # Integral scalar realization

Source: HRS Example 3.1 and Remark 3.2
(blueprint: lem-sfb-profinite-integral-scalar-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj

namespace Profinite.IntegralScalar

private theorem reduce_transition (O : Type u) [CommRing O] (π : O)
    (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    (f : B →ₗ[O] D) (k : ℕ) (b : residue O π B (k + 1)) :
    transition O π D k (reduce O π f (k + 1) b) =
      reduce O π f k (transition O π B k b) := by
  obtain ⟨b, rfl⟩ := (power O π B (k + 1)).mkQ_surjective b
  rfl

private theorem kernelLimitMap_bijective (P : Profinite.{u}) (O : Type u) [CommRing O]
    (π : O) (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    [TopologicalSpace B] [TopologicalSpace D]
    (hB : IsHomeomorph (limitMap O π B)) (hD : Function.Injective (limitMap O π D))
    (L : P → B →ₗ[O] D) (Q : Over P) :
    Function.Bijective (kernelLimitMap P O π B D L Q) := by
  classical
  constructor
  · intro a b hab
    apply Subtype.ext
    apply ContinuousMap.ext
    intro q
    apply hB.injective
    apply Subtype.ext
    funext k
    exact congrArg (fun z : kernelSequences P O π B D L Q ↦ z.val k q) hab
  · intro a
    let t : Q.left → compatible O π B := fun q ↦
      ⟨fun k ↦ a.val k q, fun k ↦ a.property.1 k q⟩
    have ht : Continuous t :=
      (continuous_pi fun k ↦ (a.val k).continuous).subtype_mk _
    let e := hB.homeomorph
    let b : C(Q.left, B) := ⟨fun q ↦ e.symm (t q), e.symm.continuous.comp ht⟩
    have hb (k : ℕ) (q : Q.left) : (power O π B k).mkQ (b q) = a.val k q := by
      exact congrArg (fun z : compatible O π B ↦ z.val k) (e.apply_symm_apply (t q))
    have hzero (q : Q.left) : L (Q.hom q) (b q) = 0 := by
      apply hD
      apply Subtype.ext
      funext k
      change (power O π D k).mkQ (L (Q.hom q) (b q)) =
        (power O π D k).mkQ 0
      have h := a.property.2 k q
      rw [← hb k q] at h
      exact h.trans (map_zero _).symm
    refine ⟨⟨b, hzero⟩, ?_⟩
    apply Subtype.ext
    funext k
    apply ContinuousMap.ext
    exact hb k

private theorem reduce_locallyConstant (P : Profinite.{u}) (O : Type u) [CommRing O]
    (π : O) (B D : Type u) [AddCommGroup B] [Module O B] [AddCommGroup D] [Module O D]
    [TopologicalSpace B] [TopologicalSpace D] (k : ℕ)
    [Finite (residue O π B k)] [DiscreteTopology (residue O π D k)]
    (g : C(P × B, D)) (L : P → B →ₗ[O] D)
    (hL : ∀ (p : P) (b : B), L p b = g (p, b)) :
    IsLocallyConstant (fun p : P ↦ reduce O π (L p) k) := by
  classical
  let lift : residue O π B k → B := fun b ↦ (power O π B k).mkQ_surjective b |>.choose
  have hlift (b : residue O π B k) : (power O π B k).mkQ (lift b) = b :=
    (power O π B k).mkQ_surjective b |>.choose_spec
  let t : P → (residue O π B k → residue O π D k) :=
    fun p b ↦ (power O π D k).mkQ (g (p, lift b))
  have ht : Continuous t := continuous_pi fun b ↦
    (power O π D k).continuous_mkQ.comp
      (g.continuous.comp (continuous_id.prodMk continuous_const))
  have ht' : IsLocallyConstant t := (IsLocallyConstant.iff_continuous t).2 ht
  apply IsLocallyConstant.iff_eventually_eq _ |>.2
  intro p
  filter_upwards [ht'.eventually_eq p] with q hq
  apply LinearMap.ext
  intro b
  rw [← hlift b]
  change (power O π D k).mkQ (L q (lift b)) =
    (power O π D k).mkQ (L p (lift b))
  simpa only [hL] using congrFun hq b

/-- Continuous realization, finite bundle reductions and the ordinary kernel limit for
finitely presented integral scalar modules, including zero modules and the empty base.

Source: Hemo--Richarz--Scholbach, Example 3.1 and Remark 3.2; agent finite-presentation
supplement and compact-reduction proof in the DAG
(blueprint: lem-sfb-profinite-integral-scalar-realization).

Proof:
1. The DVR theorem and Smith normal form diagonalize a finite presentation, giving a
   finite product of copies of O and O/π^e. Basis changes are homeomorphisms. The integer
   profinite-tower theorem and the compact-Hausdorff quotient-map lemma identify the quotient
   topology with this compact Hausdorff totally disconnected product topology.
2. Lift the finitely many generators of any second presentation to the first one. The
   resulting scalar matrix is continuous. Its factorization through both quotient maps
   proves presentation independence. The same argument makes every scalar linear map
   continuous. This identifies the topology with Mathlib's moduleTopology.
3. On free factors use the integer profinite tower coordinatewise. A torsion factor O/π^e
   has the actual quotient tower O/π^min(e,k), constant from k=e on. Their finite product
   identifies the canonical linear limitMap as a homeomorphism; all levels are finite
   discrete. This also proves separation by reductions.
4. The tensor and extension-restriction adjunction identify ordinary scalar extension
   with sheafification of Q ↦ C(Q,O) tensor over O with B. The comparison sends f tensor b
   to the function q ↦ f(q)b. Continuous functions form a sheaf, also on the slice.
5. For a continuous b:Q→B, pull a finite presentation O^n→B back along b. The resulting
   profinite surjection Q×_B O^n→Q is a cover on which b is a finite linear combination
   of the presentation generators. This proves local surjectivity of the comparison.
6. A tensor relation lifts to a continuous O^n-valued function in the closed relation
   module N. Pull O^m→N back along this function. The resulting profinite cover lifts
   the relation to actual presentation relations, proving local injectivity. The
   locally-bijective sheafification criterion makes the normalized comparison an iso.
7. Evaluate v on the universal section over P×B to obtain g. Pulling it back along the
   graph of every section proves Represents. Point objects give fibrewise O-linearity.
   Evaluation on the universal section also proves uniqueness.
8. For each finite quotient B_k choose finitely many lifts in B. Reduction of their
   g-values gives a continuous map from P to a finite set. Its fibres form the finite
   clopen partition on which the reduced linear map is constant. The quotient formulas
   commute with transitions, including on the kernel bundles.
9. A compatible sequence in the reduction kernels is, by step 3 for B, the reduction of
   a unique continuous B-valued section. Its image is zero by step 3 for the target D.
   This inverts kernelLimitMap on every object. Restrictions and pointwise scalar actions
   commute with these formulas. Sectionwise kernels are sheaves, and compatible families
   glue coordinatewise, giving precisely the ordinary inverse limit of sheaf kernels.
   The internal-module kernel theorem supplies its unique compatible action. No claim
   about surjectivity or stabilization of kernel transitions is used. Empty products and
   sums include the zero modules; on an empty base all section groups are zero.
-/
theorem integral_scalar_realization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Statement l E := by
  let := spectralNorm.normedField (Padic l) E
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have htop : TopologyStatement O π := by
    intro B _ _ _
    let := moduleTopology O B
    obtain ⟨hc, ht, hd, hr, hl⟩ := finite_module_topology l E B
    exact ⟨fun _ _ hq ↦ IsModuleTopology.isQuotientMap_of_surjective hq,
      hc, ht, hd, IsModuleTopology.topologicalAddGroup O B, inferInstance, hr, hl⟩
  refine ⟨htop, fun P ↦ ⟨continuous_scalar_comparison l E htop P, ?_⟩⟩
  intro B D _ _ _ _ _ _
  let := moduleTopology O B
  let := moduleTopology O D
  let := IsModuleTopology.topologicalAddGroup O B
  let := IsModuleTopology.topologicalAddGroup O D
  intro M N c d v
  obtain ⟨hcB, htB, hdB, hrB, hlB⟩ := finite_module_topology l E B
  obtain ⟨hcD, htD, hdD, hrD, hlD⟩ := finite_module_topology l E D
  let := hcB
  let := htB
  let := hdB
  obtain ⟨g, hg⟩ := universal_section_morphism P O B D M N c d v
  refine ⟨g, hg, ?_⟩
  intro L hL
  refine ⟨?_, fun k p b ↦ reduce_transition O π B D (L p) k b, ?_⟩
  · intro k
    let := (hrB k).1
    let := (hrD k).2
    have h := reduce_locallyConstant P O π B D k g L hL
    exact ⟨h, h.range_finite, h.isClopen_fiber⟩
  · intro Q
    exact kernelLimitMap_bijective P O π B D hlB hlD.injective L Q

end Profinite.IntegralScalar

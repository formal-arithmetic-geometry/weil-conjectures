/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.AdicNormalizedFibreData
import Sheaf.Paper.IntrinsicLocalLatticeComparison
import Sheaf.Paper.IntrinsicConstructibleFibreExactness
import Sheaf.Paper.NormalizedLatticeFiniteFree
import Sheaf.Paper.NormalizedHeartRealization
import Sheaf.Paper.ExactFamilyDetection
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology

/-! # Normalized geometric fibres of the rational heart -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalized geometric fibres of the constructible rational heart, including exactness
and simultaneous detection of zero objects, isomorphisms, zero maps and (short) exactness.
The Base data are the noetherianity, dimension and invertibility consequences already
needed to name the recorded category; the finite-type hypotheses below are retained.

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5 and Lemma 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness).

Proof plan:
1. Finite type over a field implies noetherianity and finite dimension. Use the continuous
rational realization J_X, and define the fibre intrinsically as sections at Spec κ after
ordinary module inverse image and the continuous-function coefficient map. The balanced
composition comparisons send b tensor (c tensor m) to bc tensor m; hence restriction to a
stratum and then a chart gives the same intrinsic fibre.
2. Choose an adapted finite stratification and an affine etale lattice chart through the
point, using etale-local lattice existence. The completed-system comparison identifies the
lattice with the inverse limit of its normalized etale reductions. Pull each reduction to
the algebraically closed point first. The etale stalk comparison identifies these with
constant sheaves with values (N_n)_x. Rationalization and point sections therefore give
E tensor_A lim (N_n)_x; no commutation of arbitrary stalks with limits is used.
3. The normalized finite-free stalk tower has finite A-module limit by the adic finite-module
limit theorem, with the prescribed quotients. If ϖm=0, its (n+1)-component is divisible by
ϖ^n, hence has zero n-component for every n. Thus the limit is torsion-free. Over the DVR A,
a finite torsion-free module is finite free, including rank zero.
4. An integral reduction-system map induces its inverse-limit map, and dividing by ϖ^b
multiplies the rational fibre map by ϖ^(-b). The raw localization relation annihilates the
difference of equal fractions by a power of ϖ, proving independence of representatives.
All local identifications are with the single intrinsic fibre. Comparing choices by their
composite through that fibre gives natural comparisons satisfying the cocycle. Etale fibre
products and common refinements compare charts and adapted stratifications.
5. For a short exact constructible continuous-module sequence, choose a common lisse
stratification. Its restriction is exact. A pro-etale cover makes the quotient finite free;
the local splitting lemma splits the epimorphism on a further cover. Additive module
inverse image preserves split sequences. Pulling this cover to Spec κ gives local exactness,
and exact point sections give the claimed short exact fibre sequence.
6. For zero detection use local monodromy presentations on connected qcqs noetherian charts.
Pass to an affine neighbourhood of the geometric base point before using the separated
completed-system comparison. The normalized representation lattice has stalk quotients
B/ϖ^nB, limit B, and rational fibre its representation space V. Zero fibres force V=0.
Cover restriction reflects isomorphisms, and stratum restrictions jointly detect vanishing.
Full faithfulness of J_X then gives F=0. For the empty scheme use the empty covering and
stratification; its module category has only zero objects.
7. Constructible continuous modules are closed under ambient kernels, cokernels and
extensions. Exact fibres compute the kernel, cokernel and image fibres of every morphism.
Zero detection thus detects isomorphisms and zero maps. For a short complex, apply the same
argument to its middle homology, and, for short exactness, also to the first kernel and last
cokernel. Their vanishing proves the two asserted exactness equivalences. -/
theorem adic_normalized_fibre_exactness (X : Base.{u} l)
    (k : Type u) [Field k] [X.scheme.Over (Spec (.of k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of k))]
    [QuasiCompact (X.scheme ↘ Spec (.of k))]
    [IsSeparated (X.scheme ↘ Spec (.of k))] (_hl : IsUnit (l : k))
    (R : Family.{u} l) : Nonempty (Assertions l E X (R.realization E X)) := by
  classical
  let a := R.realization E X
  obtain ⟨hlocal⟩ := intrinsic_local_lattice_comparison l E X k _hl R
  have hgeo := intrinsic_constructible_fibre_exactness l E X k _hl R
  let ha (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) :=
    (hgeo.1 κ x).choose
  let hp (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) :
      Point l E X a κ x :=
    { functor := omega l E X a κ x
      additive := ha κ x
      linear := (hgeo.1 κ x).choose_spec.1
      intrinsic := Iso.refl _
      finite := intrinsic_fiber_finite l E X a hlocal κ x
      exact := (hgeo.1 κ x).choose_spec.2 }
  let W (p : GeometricPoint X.scheme) := (hp p.field p.map).functor
  let : ∀ p, (W p).Additive := fun p ↦ (hp p.field p.map).additive
  have hw (p : GeometricPoint X.scheme) :=
    ((Functor.exact_tfae (W p)).out 0 3).mp
      (fun S hS ↦ (hp p.field p.map).exact S (realize_short_exact l E X a S hS))
  let : ∀ p, PreservesFiniteLimits (W p) := fun p ↦ (hw p).1
  let : ∀ p, PreservesFiniteColimits (W p) := fun p ↦ (hw p).2
  have hz : ∀ F, (∀ p, IsZero ((W p).obj F)) → IsZero F := by
    intro F hF
    apply hgeo.2 F
    intro κ _ _ x
    exact hF ⟨κ, x⟩
  have hd := exact_family_detection W hz
  let : (realize l E X a).Faithful := realize_faithful l E X a
  have hr := ((Functor.exact_tfae (realize l E X a)).out 0 3).mp
    (realize_short_exact l E X a)
  let : PreservesFiniteLimits (realize l E X a) := hr.1
  let : PreservesFiniteColimits (realize l E X a) := hr.2
  refine ⟨{
    point := hp
    local_chart := hlocal.local_chart
    integral_finite_free := fun C N κ _ _ t ↦ lattice_fiber_finite_free l E N κ t
    normalization := hlocal.normalization
    fractions := hlocal.fractions
    detects_zero := hgeo.2
    detects_iso := ?_
    detects_zero_map := ?_
    detects_exact := ?_
    detects_short_exact := ?_ }⟩
  · intro F G f hf
    exact hd.2.1 f (fun p ↦ hf p.field p.map)
  · intro F G f hf
    exact hd.1 f (fun p ↦ hf p.field p.map)
  · intro S
    have he : (S.map (realize l E X a)).Exact ↔ S.Exact :=
      ⟨(realize l E X a).reflects_exact_of_faithful S, fun h ↦ h.map _⟩
    rw [he, hd.2.2.1 S]
    constructor
    · intro h κ _ _ x
      exact h ⟨κ, x⟩
    · intro h p
      exact h p.field p.map
  · intro S
    rw [ShortExact.shortExact_map_iff (realize l E X a), hd.2.2.2 S]
    constructor
    · intro h κ _ _ x
      exact h ⟨κ, x⟩
    · intro h p
      exact h p.field p.map

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre

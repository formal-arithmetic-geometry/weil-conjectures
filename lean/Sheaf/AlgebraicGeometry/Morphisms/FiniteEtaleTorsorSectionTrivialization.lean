/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A section trivializes a finite etale torsor equivariantly

Source: the section-to-trivialization subargument of ILO, Travaux de Gabber,
IX Proposition 2.1(i), expanded using Stacks Tags 024T, 01WN, 01JB, 01JC and 01JJ.
(blueprint: lem-sfb-finite-etale-torsor-section-trivialization)

The action and its geometric-fibre condition are written as the corresponding
fields of `Scheme.GaloisCoverAction`, without its additional quotient data.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Translates of a section give disjoint clopen copies of the base, and their
coproduct is an equivariant isomorphism whose inverse glues the restricted projections.
Source: ILO, Travaux de Gabber, IX Proposition 2.1(i), section-to-trivialization
subargument; Stacks Tags 024T, 01WN, 01JB, 01JC and 01JJ.
(blueprint: lem-sfb-finite-etale-torsor-section-trivialization)

Proof: (1) Each translate is a section by the action-over-base equation. A finite
morphism is separated (lem-weil-pbc-finite-closed-map-finite-fibres). Apply
lem-weil-pbc-etale-section-clopen-immersion to each translate to obtain its clopen
image Q_g, with inverse the restricted projection.
(2) If two images meet, lift an intersection point to an algebraic closure of its
residue field (def-weil-geometric-point, def-weil-algebraic-closure). The two
sections then give the same geometric point, so freeness forces equal indices.
(3) Lift any point of P to such a geometric point. Transitivity writes it as a
translate of the section over its projection. Thus the Q_g cover P. These steps
use only the torsor clause of def-sbc-normal-dominant-galois.
(4) Form theta by `Sigma.desc` from the translated sections. Mathlib's
`isOpenImmersion_sigmaDesc` makes it an open immersion because their images are
disjoint. Its range is all of P by (3), so it is an isomorphism.
(5) Coproduct uniqueness proves the equation over U. Cancelling each e_g proves
that the inverse restricts on Q_g to its projection followed by the g-th
coprojection. Thus it is precisely the map obtained by gluing these restrictions;
its equation over U follows by cancelling theta.
(6) The action law gives h s_g = s_(hg). Checking coprojections proves theta is
equivariant for the left permutation of summands. Cancelling theta and checking
coprojections also proves inverse equivariance. No connectedness or nonemptiness
is used: empty bases and trivial groups are included. -/
theorem finite_etale_torsor_section_trivialization
    {U P : Scheme.{u}} (G : Type v) [Group G] [Finite G]
    (π : P ⟶ U) [IsFinite π] [Etale π]
    (a : G → (P ⟶ P))
    (haπ : ∀ g : G, a g ≫ π = π)
    (ha1 : a 1 = 𝟙 P)
    (hamul : ∀ g h : G, a (g * h) = a h ≫ a g)
    (htorsor : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (.of Ω) ⟶ P), x ≫ π = y ≫ π → ∃! g : G, x ≫ a g = y)
    (s : U ⟶ P) (hs : s ≫ π = 𝟙 U) :
    ∃ (Q : G → P.Opens) (e : ∀ g : G, U ≅ (Q g).toScheme),
      (∀ g : G, IsClosed (Q g : Set P)) ∧
      (∀ g : G, (e g).hom ≫ (Q g).ι = s ≫ a g) ∧
      (∀ g : G, (e g).inv = (Q g).ι ≫ π) ∧
      (Pairwise fun g h : G ↦ Disjoint (Q g) (Q h)) ∧
      (⨆ g : G, Q g) = ⊤ ∧
      ∃ θ : (∐ fun _ : G ↦ U) ≅ P,
        θ.hom = Sigma.desc (fun g : G ↦ s ≫ a g) ∧
        θ.hom ≫ π = Sigma.desc (fun _ : G ↦ 𝟙 U) ∧
        θ.inv ≫ Sigma.desc (fun _ : G ↦ 𝟙 U) = π ∧
        (∀ g : G, (Q g).ι ≫ θ.inv =
          (Q g).ι ≫ π ≫ Sigma.ι (fun _ : G ↦ U) g) ∧
        (∀ h g : G, (s ≫ a g) ≫ a h = s ≫ a (h * g)) ∧
        (∀ h g : G, Sigma.ι (fun _ : G ↦ U) g ≫ θ.hom ≫ a h =
          Sigma.ι (fun _ : G ↦ U) (h * g) ≫ θ.hom) ∧
        (∀ h : G, a h ≫ θ.inv = θ.inv ≫
          Sigma.desc (fun g : G ↦ Sigma.ι (fun _ : G ↦ U) (h * g))) := by
  classical
  let t : G → (U ⟶ P) := fun g ↦ s ≫ a g
  have ht (g : G) : t g ≫ π = 𝟙 U := by
    simp [t, Category.assoc, haπ, hs]
  have hmono (g : G) : Mono (t g) := mono_of_mono_fac (ht g)
  have het (g : G) : Etale (t g) := by
    have : Etale (t g ≫ π) := by rw [ht]; infer_instance
    exact Etale.of_comp (t g) π
  have hopen (g : G) : IsOpenImmersion (t g) :=
    IsOpenImmersion.of_flat_of_mono (t g)
  have hclosed (g : G) : IsClosedImmersion (t g) := by
    have : IsClosedImmersion (t g ≫ π) := by rw [ht]; infer_instance
    exact IsClosedImmersion.of_comp (t g) π
  let Q : G → P.Opens := fun g ↦ (t g).opensRange
  let e (g : G) : U ≅ (Q g).toScheme :=
    IsOpenImmersion.isoOfRangeEq (t g) (Q g).ι (by
      rw [Scheme.Opens.range_ι]; rfl)
  have he (g : G) : (e g).hom ≫ (Q g).ι = t g :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hei (g : G) : (e g).inv = (Q g).ι ≫ π := by
    apply (cancel_epi (e g).hom).mp
    simp only [Iso.hom_inv_id, ← Category.assoc, he, ht]
  have factor {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ P) (g : G)
      (H : Set.range z ⊆ Set.range (t g)) : z ≫ π ≫ t g = z := by
    let l := IsOpenImmersion.lift (t g) z H
    have hl : l ≫ t g = z := IsOpenImmersion.lift_fac _ _ _
    have hlπ : l = z ≫ π := by
      rw [← hl, Category.assoc, ht, Category.comp_id]
    rw [← Category.assoc, ← hlπ, hl]
  have hd : Pairwise fun g h : G ↦ Disjoint (Q g) (Q h) := by
    intro g h hgh
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    let Ω := AlgebraicClosure (P.residueField x)
    let z : Spec (.of Ω) ⟶ P :=
      Spec.map (CommRingCat.ofHom (algebraMap (P.residueField x) Ω)) ≫
        P.fromSpecResidueField x
    have hz (q : Spec (.of Ω)) : z q = x := by
      exact P.fromSpecResidueField_apply x _
    have hzg : z ≫ π ≫ t g = z := factor z g (by
      rintro _ ⟨q, rfl⟩; rw [hz]; exact hx.1)
    have hzh : z ≫ π ≫ t h = z := factor z h (by
      rintro _ ⟨q, rfl⟩; rw [hz]; exact hx.2)
    obtain ⟨k, hk, hkuniq⟩ := htorsor Ω (z ≫ π ≫ s) z (by
      simp [Category.assoc, hs])
    have hg : (z ≫ π ≫ s) ≫ a g = z := by simpa [t, Category.assoc] using hzg
    have hh : (z ≫ π ≫ s) ≫ a h = z := by simpa [t, Category.assoc] using hzh
    exact (hgh ((hkuniq g hg).trans (hkuniq h hh).symm)).elim
  have hcov : (⨆ g : G, Q g) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    let Ω := AlgebraicClosure (P.residueField x)
    let z : Spec (.of Ω) ⟶ P :=
      Spec.map (CommRingCat.ofHom (algebraMap (P.residueField x) Ω)) ≫
        P.fromSpecResidueField x
    obtain ⟨g, hg, _⟩ := htorsor Ω (z ≫ π ≫ (s ≫ a 1)) z (by
      simp [ha1, Category.assoc, hs])
    have hg' : (z ≫ π ≫ s) ≫ a g = z := by
      simpa only [ha1, Category.comp_id] using hg
    apply (le_iSup Q g)
    change x ∈ Set.range (t g)
    refine ⟨(z ≫ π) (IsLocalRing.closedPoint Ω), ?_⟩
    have hp := congrArg (fun f : Spec (.of Ω) ⟶ P ↦ f (IsLocalRing.closedPoint Ω)) hg'
    have hpx : z (IsLocalRing.closedPoint Ω) = x :=
      P.fromSpecResidueField_apply x _
    exact (show t g ((z ≫ π) (IsLocalRing.closedPoint Ω)) =
      z (IsLocalRing.closedPoint Ω) from hp).trans hpx
  have hthetaOpen : IsOpenImmersion (Sigma.desc t) := by
    apply isOpenImmersion_sigmaDesc (fun _ : G ↦ U) t
    intro g h hgh
    exact TopologicalSpace.Opens.coe_disjoint.mpr (hd hgh)
  have hthetaRange : (Sigma.desc t).opensRange = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ ⨆ g : G, Q g := by rw [hcov]; trivial
    obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, rfl⟩ := hg
    refine ⟨Sigma.ι (fun _ : G ↦ U) g y, ?_⟩
    simp [← Scheme.Hom.comp_apply]
  have : IsIso (Sigma.desc t) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ hthetaRange
  let θ : (∐ fun _ : G ↦ U) ≅ P := asIso (Sigma.desc t)
  have hθ (g : G) : Sigma.ι (fun _ : G ↦ U) g ≫ θ.hom = t g := by
    simp [θ]
  have hθinv (g : G) : t g ≫ θ.inv = Sigma.ι (fun _ : G ↦ U) g := by
    rw [← hθ]
    simp
  have hbase : θ.hom ≫ π = Sigma.desc (fun _ : G ↦ 𝟙 U) := by
    apply Sigma.hom_ext
    intro g
    simp [← Category.assoc, hθ, ht]
  have hlocal (g : G) : (Q g).ι ≫ θ.inv =
      (Q g).ι ≫ π ≫ Sigma.ι (fun _ : G ↦ U) g := by
    apply (cancel_epi (e g).hom).mp
    simp only [← Category.assoc, he]
    rw [ht, Category.id_comp, ← hθ]
    simp
  have hact (h g : G) : (s ≫ a g) ≫ a h = s ≫ a (h * g) := by
    rw [hamul, Category.assoc]
  refine ⟨Q, e, ?_, he, hei, hd, hcov, θ, rfl, hbase, ?_, hlocal, hact, ?_, ?_⟩
  · intro g
    exact (t g).isClosedEmbedding.isClosed_range
  · rw [← hbase, ← Category.assoc, θ.inv_hom_id, Category.id_comp]
  · intro h g
    simp only [← Category.assoc, hθ]
    exact hact h g
  · intro h
    apply (cancel_epi θ.hom).mp
    apply Sigma.hom_ext
    intro g
    simp only [← Category.assoc, hθ]
    rw [hact]
    change t (h * g) ≫ θ.inv = (t g ≫ θ.inv) ≫ _
    rw [hθinv, hθinv]
    simp

end AlgebraicGeometry

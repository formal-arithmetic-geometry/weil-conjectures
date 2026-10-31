/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion
import WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent
import WeilConjectures.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered

/-! # Generic extension under affine ind-etale limits

Source: BLR, Neron Models, 10.1, paragraph after Definition 1, p.290, and 6.5,
Corollary 3, p.159; the agent's principal-open generalization using Stacks Project,
Tags 01ZC and 0CAQ (blueprint: lem-sfb-generic-extension-ind-etale-limits).

Restriction is the map of the canonical `Over.pullback` functor along the spectrum
of the localization map. Thus both its source and target are relative Hom sets.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The unique extension property across a principal localization for all smooth test
schemes is preserved by ind-etale base change, without quasi-compactness assumptions.

Source: BLR 10.1 after Definition 1 and 6.5 Corollary 3; agent generalization using
Stacks Tags 01ZC and 0CAQ (blueprint: lem-sfb-generic-extension-ind-etale-limits).

Proof:
1. Present B as a small filtered colimit of finitely presented etale A-algebras and
reindex by a nonempty directed set (lem-weil-pbc-filtered-category-directed-cofinal).
Maps to the base change of N identify with maps to N over A by the pullback property.
Smoothness makes N locally of finite presentation, so the affine Hom continuity
criterion (lem-sfb-scheme-affine-limit-lfp-criterion) applies even for non-qc N.
2. For an affine smooth B-scheme Spec C, descend C to a smooth algebra C_i over one
stage B_i (lem-weil-pbc-smooth-algebra-filtered-colimit-descent and the affine smooth
comparison). At later stages C_j is smooth over B_j by base change, hence smooth over
A by etale smoothness and composition (lem-weil-pbc-etale-smooth-zero-dimensional-fibres
and lem-weil-pbc-smooth-ring-map-base-change-composition).
3. Tensor products and localization commute with the colimit by their universal
properties. Spec converts these colimits to the affine limits of Spec C_j and
Spec C_j[1/t] (lem-weil-pbc-spec-colimit-limit).
4. Affine Hom continuity descends a localized map to some C_j[1/t]. The assumed
bijection extends it at this smooth A-stage; pulling back gives an extension over B.
5. Represent two extensions at a common stage by unlocalized Hom continuity. Their
localized equality holds at a later stage by localized Hom continuity. Injectivity
of the hypothesis there identifies the maps, hence identifies their pullbacks.
No density or regularity of t is used.
6. Cover any smooth B-scheme by affine opens. Extend on each; cover overlaps by
affine opens and apply affine uniqueness. Scheme-morphism gluing gives existence
and uniqueness globally (lem-weil-pbc-smooth-restrict-open-subschemes and
lem-weil-pbc-scheme-morphism-gluing). -/
theorem genericExtension_bijective_of_indEtale
    (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IndEtaleAcrossUniverses) (t : A)
    (N : Over (Spec (CommRingCat.of A))) [Smooth N.hom]
    [IsClosedImmersion (pullback.diagonal N.hom)]
    (hN : ∀ X : Over (Spec (CommRingCat.of A)), Smooth X.hom →
      Function.Bijective
        (fun h : X ⟶ N ↦
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))))).map h)) :
    ∀ Y : Over (Spec (CommRingCat.of B)), Smooth Y.hom →
      Function.Bijective
        (fun h : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj N ↦
          (Over.pullback
            (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away (f t)))))).map h) := by
  sorry

/-- Both structural maps from a strict henselization to its binary tensor square are
ind-etale and preserve the principal-open extension property.

Source: BLR 6.5 Corollary 3 and 10.1 after Definition 1; Stacks Tags 04GW, 097J,
097K (blueprint: lem-sfb-generic-extension-ind-etale-limits).

Proof: The strict henselization presentation is the colimit of pointed etale
R-algebras. This category is filtered and essentially small
(lem-sc-pointed-etale-small-filtered); take a small skeleton to see that R to D is
ind-etale. Each binary structural map is its base change along the other copy of
R to D, so it is ind-etale by lem-weil-pbc-ind-etale-stability. Apply the general
assertion of this node to that map, the element t, and N. Its affine descent,
localized Hom continuity, affine uniqueness and gluing are the six steps in the
docstring of genericExtension_bijective_of_indEtale. -/
theorem genericExtension_strictHenselization_tensorSquare
    (R : Type u) (K D : Type (max u v)) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing D] [Algebra R D]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} R K D)
    (t : D) (N : Over (Spec (CommRingCat.of D))) [Smooth N.hom]
    [IsClosedImmersion (pullback.diagonal N.hom)]
    (hN : ∀ X : Over (Spec (CommRingCat.of D)), Smooth X.hom →
      Function.Bijective
        (fun h : X ⟶ N ↦
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away t))))).map h))
    (f : D →ₐ[R] D ⊗[R] D)
    (hf : f = Algebra.TensorProduct.includeLeft ∨ f = Algebra.TensorProduct.includeRight) :
    f.toRingHom.IndEtaleAcrossUniverses ∧
      ∀ Y : Over (Spec (CommRingCat.of (D ⊗[R] D))), Smooth Y.hom →
        Function.Bijective
          (fun h : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj N ↦
            (Over.pullback
              (Spec.map (CommRingCat.ofHom
                (algebraMap (D ⊗[R] D) (Localization.Away (f t)))))).map h) := by
  sorry

/-- Every specified factor map from a strict henselization into a finite tensor power
is ind-etale and preserves the principal-open extension property.

Source: BLR 6.5 Corollary 3 and 10.1 after Definition 1; Stacks Tags 04GW, 097J,
097K (blueprint: lem-sfb-generic-extension-ind-etale-limits).

Proof: Present R to D as the small filtered colimit of pointed etale algebras using
P and lem-sc-pointed-etale-small-filtered, as for the binary clause. Inserting a
unit in any position of a tensor power is, up to canonical permutations and
associativity, a base change of R to D. The stability theorem
lem-weil-pbc-ind-etale-stability makes each insertion and its composites ind-etale.
The map singleAlgHom k is exactly the composite from the specified D-factor.
Apply genericExtension_bijective_of_indEtale to that composite and the element t.
For n = 1 the factor map is the canonical identification; for n = 0 there is no
specified factor, so the quantification over Fin 0 is empty. -/
theorem genericExtension_strictHenselization_tensorFactor
    (R : Type u) (K D : Type (max u v)) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing D] [Algebra R D]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} R K D)
    (t : D) (N : Over (Spec (CommRingCat.of D))) [Smooth N.hom]
    [IsClosedImmersion (pullback.diagonal N.hom)]
    (hN : ∀ X : Over (Spec (CommRingCat.of D)), Smooth X.hom →
      Function.Bijective
        (fun h : X ⟶ N ↦
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away t))))).map h))
    (n : ℕ) (k : Fin n) :
    RingHom.IndEtaleAcrossUniverses
      (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin n ↦ D) k).toRingHom ∧
      ∀ Y : Over (Spec (CommRingCat.of (⨂[R] _ : Fin n, D))), Smooth Y.hom →
        Function.Bijective
          (fun h : Y ⟶ (Over.pullback
              (Spec.map (CommRingCat.ofHom
                (PiTensorProduct.singleAlgHom (R := R)
                  (A := fun _ : Fin n ↦ D) k).toRingHom))).obj N ↦
            (Over.pullback
              (Spec.map (CommRingCat.ofHom
                (algebraMap (⨂[R] _ : Fin n, D)
                  (Localization.Away
                    (PiTensorProduct.singleAlgHom (R := R)
                      (A := fun _ : Fin n ↦ D) k t)))))).map h) := by
  sorry

end AlgebraicGeometry

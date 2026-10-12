/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart
public import Sheaf.Paper.NonvanishingSectionTrivializes
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Morphism to polynomial Proj from generating sections

Source: literature/stacks-project/constructions.tex, Lemma 01N8
(blueprint: lem-weil-pbc-sections-morphism-to-proj-polynomial-ring).
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections of an invertible module which generate it define a morphism to Proj,
with the twisting module pulled back to the given module.
Source: Constructions, Lemma 01N8 (specialized to `A[x₀,…,xₘ]`).
(blueprint: lem-weil-pbc-sections-morphism-to-proj-polynomial-ring).

Proof:
1. Set `S = A[x₀,…,xₘ]` and `U_k = D₊(x_k)`. The charts cover Proj, are affine
   polynomial A-algebras in the ratios, and have bases `e_k` with transitions
   `e_l = (x_l/x_k)e_k` (lem-weil-pbc-proj-polynomial-twist-chart).
2. Trivialize M by s_k on its nonvanishing locus using
   lem-weil-pbc-nonvanishing-section-trivializes. Uniqueness of quotients gives the
   reciprocal and cocycle identities on overlaps. The intersection with the locus
   of s_l is precisely the unit locus of s_l/s_k.
3. The polynomial universal property gives the A-algebra chart map sending x_l/x_k
   to s_l/s_k. It defines a scheme map by lem-weil-pbc-morphism-into-affine-scheme;
   the intersection description gives its preimages of the other standard charts.
4. On overlaps the maps agree on constants and ratios, hence agree by
   lem-weil-pbc-morphism-into-affine-scheme.
5. Glue the maps by lem-weil-pbc-scheme-morphism-gluing. The intersection description
   proves that the preimage of U_k is exactly the locus of s_k, and the local maps
   give the ratio clause and their A-algebra compatibility.
6. Pull back the bases e_k using def-pc-module-pullback and
   lem-weil-pbc-invertible-pullback-invertible. Send each pulled basis to s_k.
   The transition and quotient identities make these isomorphisms agree on overlaps;
   glue them and their inverses by lem-weil-pbc-glue-sheaves-of-modules. The resulting
   isomorphism satisfies the basis-image clause.
7. The structure map q is characterized by its constant-ring maps on the charts.
   Each composite q ∘ j_k equals g on its domain, by the A-algebra property and
   lem-weil-pbc-morphism-into-affine-scheme. The cover and
   lem-weil-pbc-scheme-morphism-gluing imply q ∘ j = g.

The chart characterization pins down q uniquely; together with j ≫ q = g it also
expresses the A-algebra requirement in clause (iii). The unit of the canonical tensor
pullback adjunction sends e_k to its pullback section, so the last equation is clause (iv).
-/
theorem sections_morphism_to_proj_polynomial_ring (A : Type u) [CommRing A] (m : ℕ)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)) (M : Y.Modules) [M.IsInvertible]
    (s : Fin (m + 1) → Γ(M, ⊤))
    (hcover : ((⊤ : Y.Opens) : Set Y) =
      ⋃ k : Fin (m + 1), Scheme.Modules.nonvanishingLocus M (s k)) :
    ∃ j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A),
      ∃ α : Scheme.Modules.tensorPullbackObj j
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1) ≅ M,
      ∃ q : Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) ⟶ Spec (.of A),
      (∀ k : Fin (m + 1),
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)
            (MvPolynomial.isHomogeneous_X A k) Nat.one_pos ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap A
            (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k))))) ∧
      j ≫ q = g ∧
      (∀ k : Fin (m + 1),
        (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
          (MvPolynomial.X k) : Set Y) = Scheme.Modules.nonvanishingLocus M (s k)) ∧
      (∀ k l : Fin (m + 1),
        ∃! a : Γ(Y, j ⁻¹ᵁ Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)),
          a = (j.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
            (MvPolynomial.X k))).hom
            ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)).hom (MvPolynomial.awayXRatio A k l)) ∧
          (M.presheaf.map (homOfLE (le_top :
            (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)) ≤ ⊤)).op (s l)) =
            a • M.presheaf.map (homOfLE (le_top :
              (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
                (MvPolynomial.X k)) ≤ ⊤)).op (s k)) ∧
      (∀ k : Fin (m + 1),
        α.hom.val.app (op (j ⁻¹ᵁ Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)))
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app
            (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).val.app
              (op (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
                (MvPolynomial.X k)))
              (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k))) =
          M.presheaf.map (homOfLE (le_top :
            (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)) ≤ ⊤)).op (s k)) := by
  sorry

end AlgebraicGeometry

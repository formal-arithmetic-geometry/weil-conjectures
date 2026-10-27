/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections
import Mathlib.CategoryTheory.Extensive
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # An affine parameter family of sections on a smooth integral group

Source: Stacks Project, Groupoids, Tag 0BF7, proof of
`lemma-algebraic-quasi-projective`, smooth irreducible case, before Picard rigidity
(blueprint: lem-sfb-translated-cartier-parameter-family).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- There is an affine-space parameter family of invertible modules whose fibrewise
sections have affine nonvanishing loci covering all rational points of the group.
No identification of the isomorphism classes of the fibre modules is required.

Source: Stacks Project, Groupoids, Tag 0BF7, proof of
`lemma-algebraic-quasi-projective`, through the construction of `M = O(E)` and before
`rational-equivalence-for-Pic`
(blueprint: lem-sfb-translated-cartier-parameter-family).

Proof:
1. Choose a nonempty affine open `U` of the integral scheme `H`. The affine-boundary
   lemma `lem-sfb-smooth-affine-cartier-boundary` gives an effective Cartier divisor
   `D` with complement `U`. The canonical-section lemma
   `lem-sc-canonical-section-zero-scheme` gives `L = O(D)` and `a` with `H_a = U`.
2. By `lem-sfb-smooth-integral-finite-etale-chart`, choose a nonempty affine open
   `V` of affine `d`-space and an open `W` of `H` finite etale of positive degree
   `n` over `V`. Set `Y = H × W`, `Z = H × V`, `p = 1 × q`, and
   `alpha(h,w) = h j(w)` using `def-sc-group-scheme`. By
   `lem-sfb-finite-locally-free-fppf-descent`, `p` is finite locally free of degree
   `n`; its nonzero fibre algebras have maximal ideals, so it is surjective.
   Use `lem-sfb-finite-locally-free-function-norm` and
   `lem-sfb-finite-norm-invertible-sections` on the pullbacks of `L,a` along `alpha`.
   They give an invertible `M` on `Z` and a section `t` whose nonvanishing locus is
   the set of `z` whose whole `p`-fibre lies in `alpha⁻¹(U)`.
3. Pull `t` back along `i_v(h) = (h,v)`. By
   `lem-weil-pbc-invertible-pullback-tensor`, nonvanishing commutes with pullback.
   Each chart fibre consists of `n` rational points `w_i`. The finite coproduct
   base-change lemma `lem-sc-etale-fibre-product-base-change-coproduct` identifies
   the fibre of `p` with `n` copies of `H`. Thus at all points of `H`,
   `H_{s_v} = intersection_i U j(w_i)⁻¹`. Each translated open is affine, since
   translation has inverse translation by the group inverse. The diagonal is a
   closed immersion, hence affine by `lem-weil-pbc-closed-immersion-finite`.
   Repeatedly apply `lem-sc-picard-affine-diagonal-intersections` to the nonempty
   finite family to deduce affineness of `H_{s_v}`.
4. Given `h` rational, the open `W_h = j⁻¹(h⁻¹ U)` is nonempty by irreducibility
   and dense in `W`. Its closed complement is nowhere dense. By
   `lem-sfb-finite-image-nowhere-dense`, its image in `V` is closed nowhere dense.
   The complement has a closed point by `lem-sc-lft-over-field-jacobson-space`,
   rational by `lem-weil-pbc-closed-point-residue-field-base`. Its whole chart
   fibre lies in `W_h`, so Step 3 places `h` in `H_{s_v}`.
-/
theorem exists_translated_cartier_parameter_family
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H]
    [Smooth H.hom] [IsIntegral H.left] [LocallyOfFiniteType H.hom]
    [QuasiCompact H.hom] [IsClosedImmersion (pullback.diagonal H.hom)] :
    ∃ (d : ℕ) (V : Over (Spec (.of k)))
      (j : V.left ⟶ Spec (.of (MvPolynomial (Fin d) k))),
      IsOpenImmersion j ∧ IsAffine V.left ∧ Nonempty V.left ∧
      j ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))) = V.hom ∧
      ∃ M : (pullback H.hom V.hom).Modules, M.IsInvertible ∧
      ∃ s : ∀ v : Over.mk (𝟙 (Spec (.of k))) ⟶ V,
        Γ((Scheme.Modules.tensorPullback
          (pullback.lift (𝟙 H.left) (H.hom ≫ v.left)
            (by simp only [Category.id_comp, Category.assoc, Over.w,
              Over.mk_hom, Category.comp_id]))).obj M, ⊤),
      ∃ U : (Over.mk (𝟙 (Spec (.of k))) ⟶ V) → H.left.Opens,
        (∀ v : Over.mk (𝟙 (Spec (.of k))) ⟶ V,
          IsAffineOpen (U v) ∧ (U v : Set H.left) =
            Scheme.Modules.nonvanishingLocus
              ((Scheme.Modules.tensorPullback
                (pullback.lift (𝟙 H.left) (H.hom ≫ v.left)
                  (by simp only [Category.id_comp, Category.assoc, Over.w,
                    Over.mk_hom, Category.comp_id]))).obj M) (s v)) ∧
        ∀ h : Over.mk (𝟙 (Spec (.of k))) ⟶ H,
          ∃ v : Over.mk (𝟙 (Spec (.of k))) ⟶ V,
            h.left (IsLocalRing.closedPoint k) ∈ U v := by
  sorry

end AlgebraicGeometry

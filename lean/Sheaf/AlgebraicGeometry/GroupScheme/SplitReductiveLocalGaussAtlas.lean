module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts

/-! # A finite Laurent polynomial atlas for a split reductive group over a local ring

Source: Conrad, Reductive group schemes, Definition 5.1.1, Corollary 5.1.11,
and Theorem 5.1.13, printed pp.136, 142--144; Milne, Algebraic Groups (2017),
Theorems 21.73 and 21.84, pp.447, 451. The finite translated-cell cover is the
consequence described in the DAG proof.
(blueprint: lem-sfb-split-reductive-local-gauss-atlas).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reductive group over a nonzero Noetherian local ring, equipped with a split
geometrically maximal torus of rank r, has a nonempty finite open atlas with common
source Spec A[x_1,...,x_d,z_1^±,...,z_r^±]. The Laurent coefficient ring is the
actual group algebra A[ℤ^r]; a chart is a morphism over Spec A.

Source: Conrad, Reductive group schemes, Definition 5.1.1, Corollary 5.1.11,
Theorem 5.1.13, pp.136, 142--144; Milne, Algebraic Groups (2017), Theorems 21.73
and 21.84, pp.447, 451 (blueprint: lem-sfb-split-reductive-local-gauss-atlas).

Proof plan:
1. Apply lem-sfb-local-split-root-data-weyl-lifts to obtain the finite root set,
   a positive system, root parametrizations, the finite Weyl group W and integral
   representatives n_w. Apply lem-sfb-relative-root-product-open-cell to obtain
   U⁻, U⁺, B and the multiplication open immersion j : U⁻ × S × U⁺ → H.
   Local freeness of root lines over the local ring makes them free; neither
   henselianity nor algebraic closedness of the residue field is needed.
2. Enumerate the positive and negative roots. Ordered root products identify the
   source of j with affine N-space times S times affine N-space. Using the given
   torus isomorphism identifies its coordinate ring with the displayed Laurent
   polynomial ring, with d = 2N. Compose this isomorphism, j, and left translation
   by n_w. The inverse translation is by n_w⁻¹, so each resulting chart is open.
3. For every algebraically closed A-field F, lem-sfb-bruhat-longest-cell-charts
   writes each g in H(F) as u n_w b, with u in U⁺(F) and b in B(F).
4. Conjugation carries the roots of U⁺ to w⁻¹Φ⁺. Apply
   lem-sfb-borel-root-product-coordinates to that conjugate Borel, ordering the
   negative roots first. Thus n_w⁻¹ u n_w = v₋ v₊ with v₋ in U⁻ and v₊ in U⁺.
   The semidirect product B = S U⁺ then puts g in n_w j(U⁻ × S × U⁺).
   This uses arbitrary-order root coordinates, not commutativity of root groups.
5. Every underlying point of H lifts to a point over an algebraic closure of its
   residue field. The preceding factorization places it in a chart, hence the
   charts cover H. Take I = W, nonempty because it has an identity. Empty root
   lists and rank-zero tori give empty variable lists and the same construction.
-/
theorem splitReductive_local_gauss_atlas
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (H S : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (i : S ⟶ H) [IsClosedImmersion i.hom.hom.left]
    (r : ℕ) (e : S ≅ RingGroupSchemes.splitTorus A r)
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H))
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i)) :
    ∃ (d : ℕ) (I : Type u) (_ : Finite I) (_ : Nonempty I)
      (θ : I → (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap A (MvPolynomial (Fin d) (AddMonoidAlgebra A (Fin r → ℤ)))))) ⟶ H.X)),
      (∀ j : I, IsOpenImmersion (θ j).left) ∧
        ∀ x : H.X.left, ∃ j : I, x ∈ Set.range (θ j).left := by
  sorry

end AlgebraicGeometry

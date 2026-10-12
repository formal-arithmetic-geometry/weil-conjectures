module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- The canonical projection from the base change over `A` to that over `B`.
Source: Stacks Project, Varieties, Tag 0388.
(blueprint: lem-weil-pbc-descended-qc-neighborhood-core). -/
noncomputable def canonicalProjection (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (B : Subalgebra k A) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f
    (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B))) (by
      change Spec.map (CommRingCat.ofHom (Subalgebra.val B)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k B)) =
        Spec.map (CommRingCat.ofHom (algebraMap k A))
      rw [← Spec.map_comp]
      congr 1) :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))))

/-- Core finite-coefficient construction for one point and one open.
Source: Stacks Project, Varieties, proof of Tag 0388, lines 811--848.
(blueprint: lem-weil-pbc-descended-qc-neighborhood-core).
The proof chooses an affine chart, a principal neighborhood, and finitely many
coefficients, then transports the principal open along the canonical projection. -/
theorem exists_descended_qc_neighborhood_core (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens)
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))))
    (hx : x ∈ V) :
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧ x ∈ (canonicalProjection k X f A B) ⁻¹ᵁ W ∧
          (canonicalProjection k X f A B) ⁻¹ᵁ W ≤ V := by sorry
end AlgebraicGeometry

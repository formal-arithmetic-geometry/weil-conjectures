module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension

/-! Auxiliary reductions for rational point local dimension base change. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The topological local dimensions at compatible rational points are preserved by scalar
extension.

Source: Stacks Project, Lemma 10.116.6, Tag 00P4.
Proof: Write x for the image of the unique point under p, and y for its image under q.
The compatibility hqp implies that the first pullback projection takes y to x. Choose
an affine open U = Spec A containing x. The restriction of f gives a finite type
k-algebra structure on A, since f is locally of finite type and Spec k is affine.
Its inverse image V in the pullback is open, contains y, and is canonically isomorphic
to Spec (A tensor_k K). Under these identifications the first projection is the prime
contraction along a -> a tensor 1, so the prime corresponding to y contracts to the
prime corresponding to x. Apply topologicalKrullDimAt_spec_tensorProduct_field_extension
to this upper prime. Finally, open immersions preserve local topological dimension:
open neighbourhoods contained in an open chart are cofinal among all neighbourhoods,
and the chart isomorphisms give homeomorphisms. Transport the affine equality through
these two charts. Neither maximality nor reducedness nor separatedness is used.
(blueprint: lem-ag-rational-point-topological-local-dimension-base-change)
-/
theorem topologicalKrullDimAt_rationalPoint_field_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K]
    (q : Spec (.of K) ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hq : q ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _)
    (hqp : q ≫ pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p) :
    topologicalKrullDimAt (p (IsLocalRing.closedPoint k)) =
      topologicalKrullDimAt (q (IsLocalRing.closedPoint K)) := by sorry


end AlgebraicGeometry

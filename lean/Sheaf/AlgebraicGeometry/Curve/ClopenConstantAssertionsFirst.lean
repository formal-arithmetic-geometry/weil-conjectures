module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

/-- The first four curve assertions transfer across a finite clopen partition.
Source: the finite disjoint-union argument in the proof of the clopen constant
assertions lemma. The cohomology and stalk comparison maps decompose componentwise,
and vanishing and finiteness are preserved by finite products.
(blueprint: lem-pbc-k2-clopen-constant-assertions-first)
-/
theorem clopen_first_four (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (M : ModuleCat.{u + 1} Λ)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (H : ∀ i, Assertions Λ ((U i).ι ≫ f)
      ((constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    VanishingAboveTwo Λ ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    VanishingAboveOneOfIsAffine Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    VanishingAboveOneOfIsPrimaryTorsionSheaf Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) k ∧
    FiniteOfInvertibleOrder Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) k := by
  sorry
end AlgebraicGeometry.IsCurve

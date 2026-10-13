module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Gluing the thickened charts gives a covering family of open immersions with
compatible local maps and the prescribed source overlaps. This statement constructs
only the ambient scheme and its charts, not the global source or structure morphisms.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraphs beginning "Choose an affine open covering" and "By the general remarks".
(blueprint: lem-weil-pbc-universal-thickening-cartesian-atlas-core)

Proof: Form the source intersections as pullbacks of the open chart maps of `C`.
Each `i k` is a homeomorphism: its kernel has square zero, so its closed image is
all of the target. Thus a source intersection determines a unique open in each
of the two thickened charts. Restrict the universal thickenings to these opens
using the open-pieces theorem with the whole base open. Identify their sources
with the source intersection. Universal uniqueness gives an isomorphism of the
thickened overlaps over `X` inducing the identity on that intersection. On triple
intersections all composites extend the same identity over `X`, so uniqueness
gives the cocycle identity; the same argument gives identity and inverse maps.
These opens and transitions form scheme glue data. Take its glued scheme `W`
and canonical chart maps `e k`, which are open immersions and jointly surjective.
The gluing relation identifies precisely the prescribed thickened overlaps.
Since transitions are over `X`, the two structure maps agree on the pullback of
any two chart maps. Since they fix the source intersection, the maps `i k ≫ e k`
agree on the source pullbacks. Finally a point `i l z` lies in the overlap with
chart `k` exactly when `C.f l z` lies in the image of source chart `k`, by the
choice of the overlap opens and the gluing relation. This proves the last clause.
For an empty index type the source and the glued scheme are empty; all clauses
hold vacuously. Repeated charts cause no difficulty because the identity
transition is fixed by uniqueness. -/
theorem universalFirstOrderThickening_cartesianAtlas_core
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (e : ∀ k, Z' k ⟶ W),
      (∀ k, IsOpenImmersion (e k)) ∧ (∀ w : W, ∃ k z, e k z = w) ∧
      (∀ k l, pullback.fst (e k) (e l) ≫ h' k = pullback.snd _ _ ≫ h' l) ∧
      (∀ k l, pullback.fst (C.f k) (C.f l) ≫ (i k ≫ e k) =
        pullback.snd _ _ ≫ (i l ≫ e l)) ∧
      ∀ k l (z : C.X l),
        e l (i l z) ∈ Set.range (e k) ↔ C.f l z ∈ Set.range (C.f k) := by
  sorry

end AlgebraicGeometry

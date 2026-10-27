module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# H-projective permanence with the same projective dimension

Source: Stacks Project, Morphisms, Tag 0C4Q (lemma-projective-permanence),
specialized to a finite projective-space embedding, and Tag 01WF
(lemma-H-projective-base-change). (blueprint: lem-per-h-projective-permanence)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite projective-space embedding over `B` gives one of the same dimension over `T`
when `g : T ⟶ B` is separated. Source: Stacks Project, Morphisms, Tags 0C4Q and 01WF.
(blueprint: lem-per-h-projective-permanence)

Proof:
1. The separatedness of `g` makes the graph `Z ⟶ Z ×[B] T` a closed immersion:
   apply lem-weil-pbc-fibre-product-change-of-base-closed-immersion to `f`, the identity
   of `T`, and `g`, identifying `Z ×[T] T` with `Z` by def-pc-fibre-product.
2. The map `Z ×[B] T ⟶ ℙ(ULift (Fin (n + 1)); B) ×[B] T` induced by `i` is a
   base change of `i`. It is a closed immersion by lem-weil-pbc-closed-immersion-base-change;
   the pullback identification follows from def-pc-fibre-product and requires no flatness.
3. Compose these maps using lem-weil-pbc-closed-immersion-comp. The resulting closed
   immersion has components `i` and `f`, so its projection to `T` equals `f`.
4. Apply lemma-nagata-projective-space-base-change-pullback with coordinate type
   `ULift (Fin (n + 1))`, and interchange the pullback factors, to identify the target
   with `ℙ(ULift (Fin (n + 1)); T)`. A target isomorphism preserves closed immersions
   by def-weil-closed-immersion. This is def-kun-projective with the original `n`.
-/
theorem isHProjective_of_comp_of_isSeparated {Z T B : Scheme.{u}} (f : Z ⟶ T) (g : T ⟶ B)
    [IsSeparated g] (n : ℕ) (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); B))
    (hi : IsClosedImmersion i)
    (hif : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B) = f ≫ g) :
    ∃ j : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T),
      IsClosedImmersion j ∧ j ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T) = f := by
  sorry

end AlgebraicGeometry

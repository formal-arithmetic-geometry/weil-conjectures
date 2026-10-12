module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Étaleness on all infinitesimal restrictions yields an étale open neighborhood of
 the closed fiber. This packages the closed-immersion and ideal-sheaf identifications
 in the proof of Stacks Project, Tag 0GS2.

Proof: Let j be the projection Y ×_A Spec(A/I) → Y and let J = ker(j).
The quotient map A → A/I is surjective, so its spectrum map and its base change j
are closed immersions. On an affine open Spec R of Y, J corresponds to IR.
Extension of ideals commutes with products, so J^(n+1) corresponds to I^(n+1)R.
Consequently the closed subscheme defined by J^(n+1) is canonically the base change
Y ×_A Spec(A/I^(n+1)). These identifications glue: on overlaps they are the unique
identifications of the same quotient algebra. Pulling back g transports h_etale
to the hypotheses of etale_on_open_of_etale_infinitesimal_neighbourhoods. Apply
that theorem with j and J to obtain W, its containment, and the required étaleness.
If the inverse image of the closed fiber is empty the same theorem permits W empty.
(blueprint: lem-weil-pbc-etale-infinitesimal-restrictions-proper-neighborhood)
-/
theorem etale_open_of_infinitesimal_restrictions
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType g] [QuasiCompact g]
    (h_etale : ∀ n : ℕ, Etale (pullback.snd g (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))) :
    ∃ W : X.Opens,
      (g : X → Y) ⁻¹' Set.range
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : _ → _) ⊆
          (W : Set X) ∧ Etale (W.ι ≫ g) := by
  sorry

end AlgebraicGeometry

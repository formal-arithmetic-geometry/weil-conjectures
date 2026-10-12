module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FiniteUnramifiedOnePointClosed

/-!
# Disjoint refinement of finite unramified neighbourhoods

Source: Stacks Project, Tags 04DG, 04HI and 01W6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 04DG followed by the shrinking argument of Tag 04HI.
(blueprint: lem-weil-pbc-finite-unramified-neighbourhoods-disjoint-refinement)

Proof: apply `finite_unramified_one_point_closed` to each piece, using its unique fibre
point and purely inseparable residue extension. Intersect the finitely many neighbourhoods
of `u`. Replace all pieces by their base changes to this intersection. Their inclusions
into the pullback are proper by `IsProper.of_comp`, since the projection is separated
and each piece is a closed immersion over the base, hence proper. Thus these open pieces
are also closed. Each pairwise intersection is closed in one piece; its image in the
base is closed since that piece is finite. These images avoid `u`: uniqueness of each
piece's fibre would otherwise equate two distinct marked points. Delete the finite union
of these images and base change again. The pieces are now disjoint and still closed
immersions. Open base change identifies them with opens of the new pullback and preserves
their marked points and their exhaustion of all lifts of the listed points. For an empty
family use the whole base open; exhaustion already asserts that there are no such lifts.
No étaleness or local finite type is needed for the ambient morphism. -/
theorem exists_disjoint_closed_immersion_refinement
    {X S U : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (g : U ⟶ S) (u : U)
    (n : ℕ) (x : Fin n → X) (m : Fin n → ℕ)
    (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens)
    (v : (a : Σ i : Fin n, Fin (m i)) → (V a).toScheme)
    (hpieces : ∀ a, IsFinite ((V a).ι ≫ pullback.snd f g) ∧
      (LocallyOfFiniteType ((V a).ι ≫ pullback.snd f g) ∧
        IsOpenImmersion (pullback.diagonal ((V a).ι ≫ pullback.snd f g))) ∧
      ((V a).ι ≫ pullback.snd f g) (v a) = u ∧
      (∀ w : (V a).toScheme, ((V a).ι ≫ pullback.snd f g) w = u → w = v a) ∧
      (letI : Algebra (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
          ((V a).toScheme.residueField (v a)) :=
        (((V a).ι ≫ pullback.snd f g).residueFieldMap (v a)).hom.toAlgebra
       IsPurelyInseparable (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
         ((V a).toScheme.residueField (v a))))
    (hinjective : Function.Injective (fun a ↦ (V a).ι (v a)))
    (hexhaust : ∀ (i : Fin n) (p : ↥(pullback f g)),
      (pullback.snd f g).base p = u → (pullback.fst f g).base p = x i →
        ∃ a, p = (V a).ι (v a)) :
    ∃ (B : U.Opens) (huB : u ∈ B),
      ∃ V' : (Σ i : Fin n, Fin (m i)) → (pullback f (B.ι ≫ g)).Opens,
        (∀ a, IsClosed (V' a : Set ↥(pullback f (B.ι ≫ g)))) ∧
        Pairwise (fun a b ↦ Disjoint (V' a) (V' b)) ∧
        (∀ a, IsClosedImmersion ((V' a).ι ≫ pullback.snd f (B.ι ≫ g)) ∧
          (⟨u, huB⟩ : B.toScheme) ∈
            Set.range (((V' a).ι ≫ pullback.snd f (B.ι ≫ g)).base)) ∧
        (∀ (i : Fin n) (p : ↥(pullback f (B.ι ≫ g))),
          (pullback.snd f (B.ι ≫ g)).base p = (⟨u, huB⟩ : B.toScheme) →
          (pullback.fst f (B.ι ≫ g)).base p = x i → ∃ a, p ∈ V' a) := by
  sorry

end AlgebraicGeometry

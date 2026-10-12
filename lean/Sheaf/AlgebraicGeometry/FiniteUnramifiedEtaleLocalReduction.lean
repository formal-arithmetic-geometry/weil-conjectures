module

public import Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Finite-fibre enumeration and application of the unramified-local decomposition
produce the input required by `finite_coproduct_of_unramified_decomposition`.
(blueprint: lem-weil-pbc-finite-unramified-etale-local-input). -/
theorem finite_decomposition_input
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) :
    ∃ (n : ℕ) (pts : Fin n → Y), (∀ i, f.base (pts i) = x) ∧
      (∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
        Etale g ∧ g.base u = x ∧
        ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
          (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
          IsClosed (W : Set ↥(pullback f g)) ∧
          (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
          Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
          (∀ a, Disjoint W (V a)) ∧ W ⊔ iSup V = ⊤ ∧
          (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
            u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
          (∀ p : ↥(pullback f g), p ∈ W →
            (pullback.snd f g).base p = u →
            ∀ i, (pullback.fst f g).base p ≠ pts i)) := by
  sorry


/-- Shrinking and reindexing a finite clopen decomposition removes its
remainder and yields the finite coproduct presentation used in Lemma 04HJ.
This packages the open shrinking, base change, and coproduct bookkeeping.
(blueprint: lem-weil-pbc-finite-unramified-etale-local-reduction). -/
theorem finite_coproduct_of_unramified_decomposition
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) (n : ℕ) (pts : Fin n → Y)
    (hpts : ∀ i, f.base (pts i) = x)
    (h : ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
        (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
        IsClosed (W : Set ↥(pullback f g)) ∧
        (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
        Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
        (∀ a, Disjoint W (V a)) ∧ W ⊔ iSup V = ⊤ ∧
        (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
          u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
        (∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p = u →
          ∀ i, (pullback.fst f g).base p ≠ pts i) ) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j, IsClosedImmersion (ι j ≫ pullback.snd f g)) := by
  sorry

end AlgebraicGeometry

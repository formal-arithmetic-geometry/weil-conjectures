import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Universal locally closed pullback locus for a finite locally free module

Source: Stacks Project, More on Morphisms, Lemma diagonal-picard-flat-proper, Tag 0BDP
(blueprint: lem-sc-picard-diagonal-locally-closed).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-sc-picard-diagonal-locally-closed) For a flat proper morphism with
  universally trivial structure pushforward, the locus on which a finite locally free module
  comes by pullback is represented by an immersion of finite presentation (locally of finite
  presentation, quasi-compact and quasi-separated, def-sbc-locally-finite-presentation).

  Proof steps from Tag 0BDP: the universal structure-sheaf pushforward makes every fibre
  connected and nonempty, so the rank of `E` is constant on each open-and-closed rank
  component of the base; flatness and properness make these components open and closed.
  Apply the perfect direct-image/base-change theorem to `E` and its dual, and apply the
  locally-closed degree-zero locus construction to both perfect complexes.  On their
  intersection, the two direct images are finite locally free and commute with base change.
  The projection formula shows that an isomorphism `q* E ≅ p* N` forces the cup-product
  pairing between the two direct images to be perfect, and conversely a perfect pairing gives
  such an isomorphism locally on `T`.  Finally, the perfect-pairing locus is the open
  determinant locus; taking it on all rank components yields the required finitely presented
  immersion and the stated universal factorization property. -/
theorem picard_diagonal_locally_closed {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧ LocallyOfFinitePresentation j ∧
      QuasiCompact j ∧ QuasiSeparated j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ (h : T ⟶ Z), h ≫ j = g) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty (((Scheme.Modules.tensorPullback (pullback.fst f g)).obj E) ≅
              ((Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)) := by
  sorry

end AlgebraicGeometry.Scheme

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.Thickening
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Successive infinitesimal fibres are related by a finite order thickening and
universal homeomorphism.
Source: Stacks Project, Tag 0GS2, construction of the infinitesimal fibres; Tags 04EX,
09ZU, and 04DF.
(blueprint: lem-weil-pbc-infinitesimal-transition-thickening).

Proof: the map A/I^(n+2) → A/I^(n+1) is surjective, with kernel the image of I^(n+1).
Its kernel has square zero: I^(2*(n+1)) is contained in I^(n+2), since n+2 ≤ 2*(n+1).
Consequently its spectrum map is a closed immersion defined by a square-zero ideal.
Every prime contains this nilpotent ideal, so the spectrum map is surjective. The
map displayed below is its base change along X_(n+1) → Spec(A/I^(n+2)), by pullback
pasting. Closed immersions, square-zero defining ideals, and surjectivity persist
under base change. Thus it is a first order, hence finite order, thickening and a
surjective closed immersion. The latter is a universal homeomorphism by Tag 04DF. -/
theorem infinitesimal_transition_thickening
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) :
    let j := (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
    IsFiniteOrderThickening j ∧ IsUniversalHomeomorphism j := by
  sorry

end AlgebraicGeometry

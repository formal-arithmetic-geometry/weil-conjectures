module


public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.FinitePresentation


/-!
# Finite local-ring map at a singleton fibre of a finite morphism

Source: literature/stacks-project/more-morphisms.tex, Tag 05B8,
lemma-finite-morphism-single-point-in-fibre, parts (2) and (3)
(blueprint: lem-trf-finite-singleton-fibre-stalk-ring).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a finite morphism with a singleton fibre, the induced local-ring map is finite;
if the morphism is locally of finite presentation, it is finitely presented.

Source: literature/stacks-project/more-morphisms.tex, Tag 05B8,
lemma-finite-morphism-single-point-in-fibre, parts (2) and (3)
(blueprint: lem-trf-finite-singleton-fibre-stalk-ring).

Proof steps:
1. Choose affine neighbourhoods of the image point and its preimage. The finite morphism
   becomes a finite ring map, and the singleton fibre gives a unique prime over the base prime.
   The affine stalk-localization comparison and the unique-prime localization statement identify
   the stalk map with the localized ring map. Localization preserves finite ring maps.
2. Under local finite presentation, the affine ring map is finitely presented. Localization
   preserves finite presentation, and the same stalk identifications give the displayed
   polynomial presentation.
-/
theorem finite_singleton_fibre_stalk_ring
    {T U : Scheme.{u}} (p : T ⟶ U) [IsFinite p] (t : T)
    (h : p.base ⁻¹' ({p.base t} : Set U) = ({t} : Set T)) :
    RingHom.Finite (p.stalkMap t).hom ∧
      (LocallyOfFinitePresentation p →
        ∃ (a b : ℕ) (f : Fin b → MvPolynomial (Fin a) (U.presheaf.stalk (p.base t))),
          Nonempty (@AlgEquiv (U.presheaf.stalk (p.base t))
            (T.presheaf.stalk t)
            (MvPolynomial (Fin a) (U.presheaf.stalk (p.base t)) ⧸
              Ideal.span (Set.range f))
            _ _ _ (RingHom.toAlgebra (p.stalkMap t).hom) inferInstance)) := by
  sorry

end AlgebraicGeometry

end

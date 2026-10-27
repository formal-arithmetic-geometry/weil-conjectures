module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Completion of an ideal and its residue generator space

Source: Stacks Project, Algebra, Tag 00MA, parts (2) and (3), and Tag 05GG, part (2)
(blueprint: lem-trf-completed-ideal-generator-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

open IsLocalRing

/-- The completed inclusion of a finite ideal identifies its completion with its extension
and identifies their residue generator spaces. The residue equivalence `e` is characterized
by its value on the image of every element of the completed ring. Semilinearity along `e`
is precisely linearity over `k = R / maximalIdeal R` after the stated residue identification.

Source: Stacks Project, Algebra, Tag 00MA, parts (2) and (3), and Tag 05GG, part (2)
(blueprint: lem-trf-completed-ideal-generator-fibre).

Proof:
1. Apply exactness of completion on finite modules
   (`lem-weil-pbc-completion-exact-finite-modules`) to `0 → I → R → R/I → 0`.
   The completed inclusion is injective and linear over the completed ring; its coordinate
   formula sends the compatible classes of `a` to the completion map applied to `a`.
2. The finite-module tensor comparison (`lem-weil-pbc-completion-finite-module-tensor`)
   writes every completed ideal element as a finite sum of completed scalars times classes
   of elements of `I`. Thus the image of the completed inclusion is exactly the extended
   ideal. Corestrict this injective map to that image to obtain `α`.
3. By linearity and surjectivity, the image under `α` of the maximal ideal times the
   completed module consists of finite sums `c(b) z`, with `b` in the maximal ideal and
   `z` in the extended ideal. Expanding the extended maximal ideal proves that these are
   exactly its products with the extended ideal.
4. Apply `lem-weil-pbc-module-completion-complete` to `I` at exponent one. Projection
   to the first coordinate identifies the quotient of its completion by the maximal ideal
   with `I / m I`, with inverse given by compatible classes. Combine this with the quotient
   of `α` from step 3. Finally `lem-weil-pbc-adic-completion-mod-ideal` identifies the
   completed residue field with `R / m` by first-coordinate projection. The resulting map
   sends `[a]` to `[c(a)]` and respects these residue scalars, giving `β`.
-/
theorem exists_completedIdeal_generatorFibre
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) (hIfg : I.FG) :
    ∃ α : AdicCompletion (maximalIdeal R) I ≃ₗ[AdicCompletion (maximalIdeal R) R]
        I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)),
      (∀ y : AdicCompletion (maximalIdeal R) I,
        (α y : AdicCompletion (maximalIdeal R) R) = map (maximalIdeal R) I.subtype y) ∧
      (∀ a : I,
        (α (of (maximalIdeal R) I a) : AdicCompletion (maximalIdeal R) R) =
          algebraMap R (AdicCompletion (maximalIdeal R) R) (a : R)) ∧
      α '' (↑(maximalIdeal R •
        (⊤ : Submodule R (AdicCompletion (maximalIdeal R) I)) :
          Submodule R (AdicCompletion (maximalIdeal R) I)) :
            Set (AdicCompletion (maximalIdeal R) I)) =
        (↑((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) •
          (⊤ : Submodule (AdicCompletion (maximalIdeal R) R)
            (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))) :
          Set (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))) ∧
      ∃ e : (R ⧸ maximalIdeal R) ≃+*
          (AdicCompletion (maximalIdeal R) R ⧸
            (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))),
        (∀ s : AdicCompletion (maximalIdeal R) R,
          e.symm (Ideal.Quotient.mk
            ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) s) =
              evalOneₐ (maximalIdeal R) s) ∧
        ∃ β : (I ⧸ (maximalIdeal R • (⊤ : Submodule R I))) →ₛₗ[e.toRingHom]
            ((I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ⧸
              ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) •
                (⊤ : Submodule (AdicCompletion (maximalIdeal R) R)
                  (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))))),
          Function.Bijective β ∧ ∀ a : I, β (Submodule.Quotient.mk a) =
            Submodule.Quotient.mk (α (of (maximalIdeal R) I a)) := by
  sorry

end AdicCompletion

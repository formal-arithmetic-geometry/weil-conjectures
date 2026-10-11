/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FinitePresentation

/-!
# Essential finite presentation over an intermediate algebra

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph; Definition 00QM and
Lemma 00F4 (4) (blueprint: lem-weil-pbc-essentially-finite-presentation-over-intermediate).
-/

universe u v w p

namespace RingHom

/-- Essential finite presentation descends to an essentially finite type intermediate algebra.
The input `P`, `U`, and `f` give a localization presentation of `T` over `R`; `hf` says that
its `R`-algebra structure is the one induced by `ψ.comp φ`. The output gives a localization
presentation over `S` with its original structure map `ψ`.

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph, using Definition 00QM
and the localized analogue of Lemma 00F4 (4)
(blueprint: lem-weil-pbc-essentially-finite-presentation-over-intermediate).

Proof:
1. Choose `S = W⁻¹B` with `B` a finite type `R`-algebra, and generators `b₁, …, bₙ`
   [def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra].
   The given presentation is `T = U⁻¹P` [def-weil-pbc-finitely-presented-algebra].
   Write the image of each `bᵢ` in `T` as `pᵢ/uᵢ` with `uᵢ ∈ U`.
2. Base change `P` to `A = S ⊗[R] P`, adjoin variables `tᵢ`, and quotient by the finitely
   many relations `uᵢtᵢ = 1` and `bᵢ ⊗ 1 = (1 ⊗ pᵢ)tᵢ`, obtaining `Q`.
   Base change and composition preserve finite presentation
   [lem-weil-pbc-finite-presentation-base-change-composition]; adjoining finitely many
   variables does too [def-weil-pbc-finitely-presented-algebra], as does quotienting by
   a finitely generated ideal [lem-weil-pbc-finite-presentation-quotient-fg-ideal].
   Thus `Q` is a finitely presented `S`-algebra.
3. Map `Q` to `T` by the given maps on `S` and `P`, and `tᵢ ↦ 1/uᵢ`. The relations
   hold. The image `V` of `U` in `Q` maps to units, giving `V⁻¹Q → T`
   [lem-weil-pbc-ring-localization-universal-property].
4. Conversely `P → V⁻¹Q` inverts `U`, giving `T → V⁻¹Q` by the same universal property.
   The composite on `T` fixes `P` and its inverted denominators. The other composite
   fixes `P`, each `tᵢ = uᵢ⁻¹`, and each `bᵢ` by the compatibility relation. It therefore
   fixes `B`, the inverses of `W`, all of `S`, then `A`, `Q`, and the inverses of `V`
   [def-weil-pbc-finite-type-algebra, def-weil-pbc-essentially-finite-type-algebra,
   lem-weil-pbc-ring-localization-universal-property]. These are inverse maps over `S`.
-/
theorem essentially_finite_presentation_over_intermediate
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (hS : φ.EssFiniteType)
    (P : Type p) [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P]
    (U : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap R P) = ψ.comp φ)
    (hT : letI := f.toAlgebra; IsLocalization U T) :
    ∃ (Q : Type (max v p)) (_ : CommRing Q) (_ : Algebra S Q),
      Algebra.FinitePresentation S Q ∧
        ∃ (V : Submonoid Q) (g : Q →+* T),
          g.comp (algebraMap S Q) = ψ ∧ (letI := g.toAlgebra; IsLocalization V T) := by
  sorry

end RingHom

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # K-flatness of a Hom complex with bounded finite-projective source

Source: Stacks Project, more-algebra.tex, lemma-base-change-RHom, clause (1).
(blueprint: lem-pc-perfect-ring-hom-kflat)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The Hom complex from a bounded finite-projective complex to a K-flat complex is K-flat.

Source: Stacks Project, more-algebra.tex, lemma-base-change-RHom, clause (1), and
lemma-bounded-above-flat-K-flat (blueprint: lem-pc-perfect-ring-hom-kflat).

Proof: evaluate sheaves on the unique object of the bottom-topology one-object site;
this identifies the sheaf tensor and internal Hom with their module counterparts.
Put `Pᵛ = Hom(P,A)`, with the dual differential and reversed degrees. Finite projectivity
identifies `Hom(P^i,A) ⊗ M` with `Hom(P^i,M)`: the evaluation map is an isomorphism for
finite free modules, and restricting the map and its inverse along a projective splitting
proves the claim for their direct summands. Boundedness of P makes every diagonal finite,
so these identifications give a chain isomorphism `Tot(Pᵛ ⊗ Q) ≅ Hom(P,Q)`;
choose the signs to match `d_Q f - (-1)^n f d_P`. The dual Pᵛ is bounded with finite
projective, hence flat, terms. For acyclic F, `Tot(F ⊗ Pᵛ)` is acyclic by the
bounded-above flat K-flat lemma. Associativity of total tensor products gives
`Tot(F ⊗ Tot(Pᵛ ⊗ Q)) ≅ Tot(Tot(F ⊗ Pᵛ) ⊗ Q)`, with the usual Koszul signs;
Q being K-flat makes the latter acyclic. Transport acyclicity through these chain
isomorphisms and through the one-object evaluation equivalence. This is exactly the
predicate `IsKFlat` for the shared Hom complex. -/
theorem perfectRingHom_isKFlat {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hQ : Q.IsKFlat) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).IsKFlat := by
  sorry

end CategoryTheory

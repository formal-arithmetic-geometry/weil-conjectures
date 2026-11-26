/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.ExtendScalars

/-!
# Naturality of the Jacobi–Zariski connecting map for a quotient

For `R → S → B` and `C = B/I`, the Jacobi–Zariski connecting map of `R → B → C` is compatible
with that of `S → B → C` and with the conormal differential of the quotient presentation.

## Implementation details

The comparison `c` lifts the `S`-linear map sending a differential to `1 ⊗` its image in the
differentials of `B`. The two connecting maps are compared on monomials via
`Generators.H1Cotangent.δAux_monomial` and extended by polynomial induction, without choosing
lifts of elements of `C` or expanding partial derivatives.

## References

* [Stacks, Tag 00S2]
* [Stacks, Tag 07E4]
* [Stacks, Tag 07E5]
-/

@[expose] public section

universe u v w

open TensorProduct KaehlerDifferential

namespace Algebra

/-- Naturality of the Jacobi–Zariski connecting map for a quotient `C = B/I`.

The quotient extension `P` has ring `B` and kernel `I`; its cotangent module is `I/I²`.
The map `P.cotangentComplex` is the conormal differential, and
`P.h1CotangentEquivCotangent` is the canonical quotient isomorphism. The connecting
maps are those of `jacobiZariski_homology_sequence`, with its coefficient formula.
Existence of the linear comparison `c`, with the displayed generator formula, expresses
that this formula is well defined. All four maps are bundled linear maps over the quotient. -/
theorem jacobiZariski_connectingMap_naturality
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    (I : Ideal B) :
    let C := B ⧸ I
    let P := Extension.ofSurjective (IsScalarTower.toAlgHom R B C)
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
    let ι := H1Cotangent.map S B C C
    let θ := P.h1CotangentEquivCotangent
    let partialS := H1Cotangent.δ R S C
    let partialB := H1Cotangent.δ R B C
    let δ := P.cotangentComplex
    ∃ c : C ⊗[S] Ω[S⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R],
      (∀ (x : C) (s : S),
        c (x ⊗ₜ[S] D R S s) = x ⊗ₜ[B] D R B (algebraMap S B s)) ∧
      (δ.comp (θ.toLinearMap.comp ι) = c.comp partialS) ∧
      (δ.comp θ.toLinearMap = partialB) := by
  classical
  dsimp only
  let C := B ⧸ I
  let P := Extension.ofSurjective (IsScalarTower.toAlgHom R B C)
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  let c : C ⊗[S] Ω[S⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R] :=
    (((TensorProduct.mk B C Ω[B⁄R] 1).restrictScalars S).comp
      (KaehlerDifferential.map R R S B)).liftBaseChange C
  have hc (x : C) (s : S) :
      c (x ⊗ₜ[S] D R S s) = x ⊗ₜ[B] D R B (algebraMap S B s) := by
    simp [c, LinearMap.liftBaseChange_tmul, smul_tmul']
  refine ⟨c, hc, ?_, P.cotangentComplex_comp_h1CotangentEquivCotangent⟩
  rw [← LinearMap.comp_assoc, P.cotangentComplex_comp_h1CotangentEquivCotangent]
  let Q := Generators.self S C
  let Q' := Generators.self B C
  let f := Generators.defaultHom Q Q'
  have hf (g : MvPolynomial C S) :
      f.toAlgHom g = MvPolynomial.map (algebraMap S B) g := by
    have he : f.toAlgHom = MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom S S B) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [f, Q, Q', Generators.defaultHom, Generators.self, Generators.σ]
    exact congrArg (fun k => k g) he
  have haux (g : MvPolynomial C S) :
      Generators.H1Cotangent.δAux R Q' (f.toAlgHom g) =
        c (Generators.H1Cotangent.δAux R Q g) := by
    rw [hf]
    induction g using MvPolynomial.induction_on' with
    | monomial n s =>
      rw [MvPolynomial.map_monomial, Generators.H1Cotangent.δAux_monomial,
        Generators.H1Cotangent.δAux_monomial]
      exact (hc _ s).symm
    | add g h hg hh => simp only [map_add, hg, hh]
  ext h
  obtain ⟨x, hx⟩ := h
  obtain ⟨g, rfl⟩ := Extension.Cotangent.mk_surjective x
  change Generators.H1Cotangent.δ Q' (Generators.self R B)
    (Extension.H1Cotangent.map f.toExtensionHom ⟨Extension.Cotangent.mk g, hx⟩) =
      c (Generators.H1Cotangent.δ Q (Generators.self R S)
        ⟨Extension.Cotangent.mk g, hx⟩)
  change Generators.H1Cotangent.δ Q' (Generators.self R B)
    ⟨Extension.Cotangent.map f.toExtensionHom (Extension.Cotangent.mk g), _⟩ = _
  simp only [Extension.Cotangent.map_mk, Generators.H1Cotangent.δ_eq_δAux]
  exact haux g.val

end Algebra

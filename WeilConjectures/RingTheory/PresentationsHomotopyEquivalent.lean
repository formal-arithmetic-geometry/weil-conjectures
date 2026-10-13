/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Homotopy equivalence of naive cotangent complexes of polynomial presentations

Source: Stacks Project, Algebra, Tag 00S1, specialized to identity maps on the base and
quotient rings (blueprint: lem-weil-pbc-nl-presentations-homotopy-equivalent).
-/

@[expose] public section

universe u v w w'

open TensorProduct

namespace Algebra.Extension

/-- Two polynomial presentations of the same algebra have homotopy equivalent naive cotangent
complexes. Source: Stacks Project, Algebra, Tags 00S0 and 00S1
(blueprint: lem-weil-pbc-nl-presentations-homotopy-equivalent).

Writing `P := ofSurjective α hα` and `P' := ofSurjective α' hα'`, `P.Cotangent` is the
conormal module `ker α / (ker α)²`, with its canonical `S`-module structure;
`P.CotangentSpace` is `S ⊗[P.Ring] Ω[P.Ring⁄R]`. The first two clauses specify that the
already defined `S`-linear differentials send the class of `f` to `1 ⊗ df`.
A `P.Hom P'` is precisely an `R`-algebra map between the polynomial rings commuting with
the maps to `S`. `Cotangent.map` and `CotangentSpace.map` are its induced maps on conormal
classes and on tensors of differentials, respectively. The two `Nonempty` clauses assert
that lifts exist; the final clause applies to every pair of lifts, independently chosen, with
`φ₁ = Cotangent.map φ`, `φ₀ = CotangentSpace.map φ`, `ψ₁ = Cotangent.map ψ`,
`ψ₀ = CotangentSpace.map ψ` written out (no `let` binders, so the proof can unfold them).

Proof outline:
1. Lift each variable through the opposite surjection and extend by the polynomial universal
property (def-weil-pbc-mv-polynomial-ring) to obtain maps of presentations in both directions.
2. A lift maps kernels and their squares into the opposite kernels and squares. Hence it
induces an `S`-linear map on conormal modules. The universal property of differentials
(def-weil-pbc-kahler-differentials) induces the degree-zero map. Leibniz makes the differential
vanish on the square of the kernel, and evaluation on conormal classes proves the chain-map
identity. Mathlib supplies these maps and `CotangentSpace.map_comp_cotangentComplex`.
3. For two lifts `a,b`, their difference modulo the opposite kernel square is an `R`-derivation:
expand `a(pq)-b(pq)` and use that both scalar actions factor through `S`. By the universal
property of differentials and extension of scalars this gives the diagonal homotopy
(`Hom.sub`; def-weil-pbc-kahler-differentials).
4. On a conormal class the homotopy followed by the differential is the difference of the
induced degree-one maps; on `s ⊗ dp` the differential followed by the homotopy is the
difference of the degree-zero maps. These generators span, so the equations hold everywhere
(`Cotangent.map_sub_map`, `CotangentSpace.map_sub_map`).
5. Induced maps respect composition and identity on both sorts of generators. Apply steps
3 and 4 to the identity and `ψ.comp φ`, and then to the identity and `φ.comp ψ`. This gives
the four displayed homotopy identities for any lifts `φ,ψ`, while step 2 gives the two
chain-map identities (def-weil-pbc-kahler-differentials). -/
theorem presentations_homotopy_equivalent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {T : Type w} {U : Type w'}
    (α : MvPolynomial T R →ₐ[R] S) (α' : MvPolynomial U R →ₐ[R] S)
    (hα : Function.Surjective α) (hα' : Function.Surjective α') :
    (∀ f : (ofSurjective α hα).ker, (ofSurjective α hα).cotangentComplex (Cotangent.mk f) =
      (1 : S) ⊗ₜ[(ofSurjective α hα).Ring]
        KaehlerDifferential.D R (ofSurjective α hα).Ring f) ∧
    (∀ f' : (ofSurjective α' hα').ker, (ofSurjective α' hα').cotangentComplex (Cotangent.mk f') =
      (1 : S) ⊗ₜ[(ofSurjective α' hα').Ring]
        KaehlerDifferential.D R (ofSurjective α' hα').Ring f') ∧
    Nonempty ((ofSurjective α hα).Hom (ofSurjective α' hα')) ∧
    Nonempty ((ofSurjective α' hα').Hom (ofSurjective α hα)) ∧
    ∀ (φ : (ofSurjective α hα).Hom (ofSurjective α' hα'))
      (ψ : (ofSurjective α' hα').Hom (ofSurjective α hα)),
      ∃ (h : (ofSurjective α hα).CotangentSpace →ₗ[S] (ofSurjective α hα).Cotangent)
        (h' : (ofSurjective α' hα').CotangentSpace →ₗ[S] (ofSurjective α' hα').Cotangent),
        (ofSurjective α' hα').cotangentComplex ∘ₗ Cotangent.map φ =
          CotangentSpace.map φ ∘ₗ (ofSurjective α hα).cotangentComplex ∧
        (ofSurjective α hα).cotangentComplex ∘ₗ Cotangent.map ψ =
          CotangentSpace.map ψ ∘ₗ (ofSurjective α' hα').cotangentComplex ∧
        LinearMap.id - Cotangent.map ψ ∘ₗ Cotangent.map φ =
          h ∘ₗ (ofSurjective α hα).cotangentComplex ∧
        LinearMap.id - CotangentSpace.map ψ ∘ₗ CotangentSpace.map φ =
          (ofSurjective α hα).cotangentComplex ∘ₗ h ∧
        LinearMap.id - Cotangent.map φ ∘ₗ Cotangent.map ψ =
          h' ∘ₗ (ofSurjective α' hα').cotangentComplex ∧
        LinearMap.id - CotangentSpace.map φ ∘ₗ CotangentSpace.map ψ =
          (ofSurjective α' hα').cotangentComplex ∘ₗ h' := by
  sorry

end Algebra.Extension

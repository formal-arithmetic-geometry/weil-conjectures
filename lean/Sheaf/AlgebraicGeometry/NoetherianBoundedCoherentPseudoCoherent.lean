import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Bounded coherent complexes on Noetherian schemes are pseudo-coherent

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.3 (Tag 08E8;
label lemma-identify-pseudo-coherent-noetherian)
(blueprint: lem-pc-noetherian-bounded-coherent-pseudo-coherent).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a Noetherian scheme `S`, an object `E` of `D(𝒪_S)` whose cohomology sheaves vanish
outside a bounded range `[a, b]` and are all coherent is pseudo-coherent. Source: Stacks
Project, Tag 08E8 (blueprint: lem-pc-noetherian-bounded-coherent-pseudo-coherent).

Proof: Choose `a ≤ b` with `H^i(E) = 0` for `i < a` and `i > b`. For each `i ∈ [a, b]` the
sheaf `H^i(E)` is coherent on the Noetherian scheme `S`, so it is pseudo-coherent as a complex
in degree zero (lem-sc-coherent-pseudo-coherent), and so is its shift `H^i(E)[-i]`. For
`m = b, b - 1, …, a` the lower-truncation triangle
`H^m(E)[-m] → τ_{≥ m}E → τ_{≥ m+1}E → H^m(E)[-m+1]`
(lem-pc-derived-lower-truncation-step-triangle) and the two-out-of-three property of
pseudo-coherence for distinguished triangles (lem-pc-pseudo-coherent-distinguished-triangle)
show by descending induction that `τ_{≥ m}E` is pseudo-coherent, starting from
`τ_{≥ b+1}E = 0`. At `m = a` the vanishing below `a` identifies `τ_{≥ a}E` with `E`. -/
theorem isPseudoCoherent_of_bounded_coherent
    (S : Scheme.{u}) [IsNoetherian S]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent S.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj E)) :
    IsPseudoCoherent S E := by
  sorry

end AlgebraicGeometry.Scheme

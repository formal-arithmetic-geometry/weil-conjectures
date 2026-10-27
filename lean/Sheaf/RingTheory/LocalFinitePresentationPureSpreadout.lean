module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.LocalUniversalInjectiveResidue

/-! # Projective pure spreadouts over a finite quotient of a local base

Source: Stacks Project, More on Flatness, Tag 0AT8, `lemma-find-pure-spreadout`,
and `equation-star`. (blueprint: lem-sfb-local-finite-presentation-pure-spreadout)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

namespace Module

/-- A finitely presented localized module has a projective pure spreadout after a
finitely generated quotient of the local base; no base-flatness is assumed.

The ring acting on `P` is exactly `(B / IB)[1/s]`. Its `B`-action is restriction
of scalars, and the displayed equation fixes its `R/I`-action. The other scalar
equation fixes the `B`-action on the actual quotient `N/IN`. The two linear maps
`j` and `jA` are the same function with the two relevant scalar structures.
`IsLocalizedModule S j` says that `j` identifies `N/IN` with the localization of
`P`: the induced equivalence sends `p/1` to `j p`. This equivalence is linear over
the localization of `(B/IB)[1/s]` at the image of `S`, since all these scalar
actions are induced from `B` and the inverted elements act invertibly.

Source: Stacks Project, More on Flatness, Tag 0AT8, `lemma-find-pure-spreadout`
and the definition following `equation-star`.
(blueprint: lem-sfb-local-finite-presentation-pure-spreadout)

Proof:
1. Clear the finitely many denominators in a presentation of `N`, obtaining a
finitely presented `B`-module `M` whose localization is `N`. The common denominator
is a unit after localization, so the cokernel is unchanged. For empty matrices
use denominator one. Uses lem-weil-pbc-tensor-right-exact and
lem-weil-pbc-localization-tensor-over-base.
2. Reduce `M` modulo the maximal ideal. The finite type algebra over the residue
field is Noetherian, and the finite module's localization kernel is finitely
generated. Uses lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-localization-tensor-over-base, lem-weil-pbc-noetherian-submodule-finite.
3. Choose a product `s` of denominators killing those kernel generators. Then
`M_s` modulo the maximal ideal injects into the localization, so every element
of `S` acts injectively there. Both `B_s` and `M_s` are finitely presented.
Uses lem-trf-localization-preserves-finite-presentation and
lem-weil-pbc-localization-tensor-over-base.
4. Descend `B_s, M_s` to a local Noetherian subring `R₀` essentially of finite
type over the integers. Extend its finitely generated maximal ideal to `I` in
`R`. It lies in the maximal ideal of `R`. Quotienting identifies `P=M_s/IM_s`
with `(R/I)` tensored over the residue field of `R₀` with the reduced model.
Finite presentation survives this base change. Uses
lem-sfb-local-algebra-module-noetherian-subring-model and lem-pc-fp-module-base-change.
5. The reduced model is a vector space, hence projective. Base change makes `P`
projective over `R/I`, hence flat. The quotient `R/I` is local. Uses
lem-weil-pbc-vector-space-projective, lem-trf-local-projective-tensor-base-change,
lem-weil-pbc-projective-module-flat.
6. Multiplication by every element of `S` on `P` is residue-injective by step 3.
The projective-source, flat-target residue criterion makes it universally
injective. A tensor element killed by localization is killed by one such
multiplier and is therefore zero. This gives universal injectivity of the
localization map. Uses lem-trf-local-universal-injective-residue and
lem-weil-pbc-localization-tensor-over-base.
7. Localization commutes with quotienting: the equivalence sends `[l]/t` to
`[l/t]` in `N/IN`. It is linear over the localized quotient ring and its composite
with `p ↦ p/1` is precisely `j`. Transporting step 6 along this equivalence gives
the asserted tensor injectivity. Uses lem-weil-pbc-localization-tensor-over-base.
-/
theorem exists_projective_pureSpreadout_of_finitePresentation
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (S : Submonoid B) (N : Type w) [AddCommGroup N]
    [Module (Localization S) N] [Module B N] [IsScalarTower B (Localization S) N]
    [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation (Localization S) N] :
    ∃ I : Ideal R, I.FG ∧ I ≤ IsLocalRing.maximalIdeal R ∧
      ∃ s : S, ∃ (P : Type (max u v w)) (_ : AddCommGroup P)
        (_ : Module (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap R B)) s)) P)
        (_ : Module B P)
        (_ : IsScalarTower B
          (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap R B)) s)) P)
        (_ : Module (R ⧸ I) P)
        (_ : Module B (N ⧸ (I • ⊤ : Submodule R N))),
        (∀ (r : R) (p : P), Ideal.Quotient.mk I r • p =
          algebraMap R
            (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap R B)) s)) r • p) ∧
        (∀ (b : B) (n : N),
          b • (Submodule.Quotient.mk n : N ⧸ (I • ⊤ : Submodule R N)) =
            Submodule.Quotient.mk (b • n)) ∧
        Module.FinitePresentation
          (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap R B)) s)) P ∧
        Module.Projective (R ⧸ I) P ∧
        ∃ (j : P →ₗ[B] (N ⧸ (I • ⊤ : Submodule R N)))
          (jA : P →ₗ[R ⧸ I] (N ⧸ (I • ⊤ : Submodule R N))),
          (∀ p : P, jA p = j p) ∧ IsLocalizedModule S j ∧
          ∀ (T : Type (max u v w z)) [AddCommGroup T] [Module (R ⧸ I) T],
            Function.Injective (jA.rTensor T) := by
  sorry

end Module

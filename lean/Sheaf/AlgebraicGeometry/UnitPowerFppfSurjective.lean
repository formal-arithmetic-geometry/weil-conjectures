module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Positive power maps on units are fppf locally surjective

Source: Stacks Project, etale-cohomology.tex, Tag 040N,
lemma-kummer-sequence-syntomic, positive-integer case and its proof
(blueprint: lem-sfb-unit-power-fppf-surjective).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every global unit on an `S`-scheme has a positive-power root on a jointly surjective
family of flat, locally finitely presented `S`-morphisms. This is the covering-family
formulation of local surjectivity of the power map on the multiplicative fppf sheaf.
No invertibility hypothesis on the exponent is needed.

Source: Stacks Project, etale-cohomology.tex, Tag 040N,
lemma-kummer-sequence-syntomic, positive-integer case
(blueprint: lem-sfb-unit-power-fppf-surjective).

Proof plan:
1. Cover `T` by affine opens `U_i = Spec A_i`, using
   lem-weil-pbc-affine-opens-basis and lem-weil-pbc-affine-open-spec-points. Restrict
   the given unit to `a_i`, and form `B_i = A_i[X]/(X^n - a_i)` and its spectrum
   (def-weil-affine-spectrum), with the composite structure morphism to `S`.
2. Omit empty opens. By lem-weil-pbc-monic-quotient-free, `B_i` is free on
   `1, X, ..., X^(n-1)`; lem-sc-affine-standard-cover-finite-free-local-fp-flat gives
   flatness. Reduction modulo any maximal ideal has the same nonempty basis over
   the residue field, so that ideal does not generate the unit ideal in `B_i`.
   Apply lem-weil-pbc-flat-faithfully-flat-maximal-ideals and then
   lem-weil-pbc-faithfully-flat-surjective-spectrum to obtain surjectivity.
3. Use lem-weil-pbc-flat-ring-map-iff-flat-affine for flatness on spectra. The open
   inclusions are flat, since their stalk maps are isomorphisms
   (def-weil-open-immersion and def-weil-flat-morphism). Compose using lem-pc-flat-compose.
   The displayed one-generator, one-relation presentation gives local finite presentation
   directly by def-sbc-locally-finite-presentation.
4. The class `b_i` of `X` satisfies `b_i^n = a_i` and has explicit inverse
   `a_i⁻¹ X^(n-1)`. Regard it as a global unit on `Spec B_i` by def-weil-affine-spectrum.
5. Every point of `T` belongs to some `U_i` and lifts to `Spec B_i`, giving joint
   surjectivity. For empty `T`, take the empty family. These local roots express exactly
   local surjectivity in the fppf topology; the construction never inverts `n`.
-/
theorem exists_fppf_cover_unit_pow_eq (S : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n)
    (T : Over S) (a : Γ(T.left, ⊤)ˣ) :
    ∃ (I : Type u) (U : I → Over S) (f : ∀ i : I, U i ⟶ T)
      (b : ∀ i : I, Γ((U i).left, ⊤)ˣ),
      (∀ i : I, Flat (f i).left) ∧
      (∀ i : I, LocallyOfFinitePresentation (f i).left) ∧
      (∀ t : T.left, ∃ (i : I) (x : (U i).left), (f i).left x = t) ∧
      (∀ i : I, b i ^ n = Units.map (f i).left.appTop.hom.toMonoidHom a) := by
  sorry

end AlgebraicGeometry.Scheme

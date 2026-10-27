module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Sheaf.TraceFormula.LocalDimensionFormula
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Local dimension inequality with generic components

Source: literature/stacks-project/morphisms.tex, Tag 0BAE,
lemma-dimension-formula-general
(blueprint: lem-sfb-local-dimension-formula-generic-components).

The finite set `G` consists exactly of the generic points of components through `x`.
The natural numbers `tx` and `t ξ` record the residue transcendence degrees at `x`
and at each `ξ ∈ G`. Thus `G.sup t` is their maximum.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Local dimension inequality including all components through the given point.
Source: literature/stacks-project/morphisms.tex, Tag 0BAE,
lemma-dimension-formula-general
(blueprint: lem-sfb-local-dimension-formula-generic-components).

Proof:
1. Choose affine neighbourhoods `Spec B` of `x` mapping into `Spec A` of `f x`.
   The base ring is Noetherian by pqf-lem-affine-open-locnoeth. The induced ring map
   is finite type by lem-weil-pbc-lft-affine-pairs, so B is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Identify the points with primes
   q and p using lem-weil-pbc-affine-open-spec-points.
2. Identify the local rings with B_q and A_p using
   lem-weil-pbc-affine-open-stalk-localization, compatibly with the ring map by
   lem-weil-pbc-spec-map-stalk-localization. Their residue fields are the fraction
   fields of B/q and A/p; the induced field maps send a/u to its image fraction.
3. By lem-weil-pbc-spec-irreducible-components-minimal-primes and
   lem-sc-components-open-injection, the components through x correspond to the
   minimal primes q_i contained in q. For the converse, the closure in X of a
   component of the affine open is a component: any larger irreducible closed set
   restricts to that same component and its nonempty open subset is dense.
   Their generic points form a finite nonempty set by
   lem-weil-pbc-noetherian-finitely-many-minimal-primes and
   lem-weil-pbc-prime-contains-minimal-prime.
4. Apply lem-weil-pbc-finite-type-residue-field-extension-finitely-generated at
   q and each q_i, followed by
   lem-weil-pbc-finitely-generated-field-finite-transcendence-basis. The sizes of
   these finite bases give tx and t on G; extend t by zero off G. Their maximum
   is G.sup t since G is finite and nonempty.
5. Set p_i to the inverse image of q_i. The quotient map A/p_i to B/q_i is
   injective and finite type. Its spectra are integral, and their morphism is
   dominant, locally finite type by lem-weil-pbc-lft-pointwise-criterion, over a
   locally Noetherian base by lem-weil-pbc-finite-type-algebra-noetherian. Use
   lem-weil-pbc-spec-domain-stalks-function-field for the integral spectra.
6. Use lem-weil-pbc-localization-at-prime-of-quotient and
   lem-weil-pbc-spec-domain-stalks-function-field to identify their local rings
   with B_q/q_i B_q and A_p/p_i A_p. Their residue fields are those at x and f x;
   their function fields are the residue fields at the two generic points.
   All identifications commute with the induced maps on fractions.
7. Apply lem-trf-local-dimension-formula to these integral dominant morphisms.
   This bounds dim(B_q/q_i B_q) + tx by dim(A_p/p_i A_p) + t(q_i).
8. Quotient prime chains give dim(A_p/p_i A_p) ≤ dim A_p. Moreover dim B_q is
   the maximum of dim(B_q/q_i B_q): by lem-weil-pbc-primes-of-localization,
   every chain contracts to primes below q, and its first prime contains a q_i
   by lem-weil-pbc-prime-contains-minimal-prime. It therefore descends to that
   quotient with the same length. Conversely quotient chains lift unchanged.
9. Bound each t(q_i) by G.sup t and take the maximum in step 7. Step 8 gives
   the required inequality, and steps 3 and 4 give the remaining clauses.
-/
theorem local_dimension_formula_generic_components
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (x : X) :
    ∃ (G : Finset X) (tx : ℕ) (t : X → ℕ),
      (∀ ξ : X, ξ ∈ G ↔
        ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ IsGenericPoint ξ Z) ∧
      G.Nonempty ∧
      @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _
        (f.residueFieldMap x).hom.toAlgebra = (tx : Cardinal) ∧
      (∀ ξ ∈ G,
        @Algebra.trdeg (S.residueField (f ξ)) (X.residueField ξ) _ _
          (f.residueFieldMap ξ).hom.toAlgebra = (t ξ : Cardinal)) ∧
      ringKrullDim (X.presheaf.stalk x) + (tx : WithBot ℕ∞) ≤
        ringKrullDim (S.presheaf.stalk (f x)) + ((G.sup t : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry

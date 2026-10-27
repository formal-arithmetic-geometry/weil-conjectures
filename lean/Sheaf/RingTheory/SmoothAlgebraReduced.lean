module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Smooth.Flat
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.GRing
import Sheaf.RingTheory.RegularMapReducedTarget
import Mathlib.RingTheory.Smooth.NoetherianDescent
import WeilConjectures.RingTheory.DirectedSubalgebraTensorColimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Smooth algebras over reduced rings

Source: Stacks Project, Algebra, Tag 033B, `lemma-reduced-goes-up`, both paragraphs
(blueprint: lem-sfb-smooth-algebra-over-reduced-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A smooth algebra over an arbitrary reduced commutative ring is reduced.
There is no Noetherian hypothesis on either ring.

Source: Stacks Project, Algebra, Tag 033B, `lemma-reduced-goes-up`, full statement
(blueprint: lem-sfb-smooth-algebra-over-reduced-ring).

Proof:
1. For a smooth map `T → B` with `T` Noetherian, finite presentation from
   `def-weil-pbc-smooth-ring-map` gives finite type, and
   `lem-weil-pbc-finite-type-algebra-noetherian` makes `B` Noetherian. The map is flat by
   `lem-weil-pbc-smooth-ring-map-flat`. For each prime of `T` and finite purely inseparable
   extension of its residue field, `lem-weil-pbc-smooth-ring-map-base-change-composition`
   makes the extended algebra smooth over that field. It is Noetherian by finite type,
   and `lem-weil-pbc-smooth-over-field-regular-local` makes its prime localizations regular.
   Thus it is regular in the ring sense of `def-weil-regular-scheme`.
   By `lem-weil-pbc-tensor-cancel-base-change`, it is the extended fibre. Hence the map
   is regular in the sense of `def-weil-pbc-g-ring`.
2. If `T` is also reduced, `lem-exc-regular-map-reduced-target` applies to these two
   Noetherian rings and their regular map, proving that `B` is reduced.
3. In general, `lem-weil-pbc-smooth-algebra-finite-type-model` gives a finitely generated
   integer subalgebra `R₀` of `R`, a smooth `R₀`-algebra `A₀`, and an isomorphism
   `A ≃ R ⊗[R₀] A₀`. The finitely generated integer subalgebras of `R` containing `R₀`
   form a nonempty directed collection covering `R`: adjoining finite generating sets
   gives upper bounds, and adjoining any one element gives coverage.
4. Each such subalgebra `T` is reduced by its injection into `R`. It is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`, since every ideal of the integers is
   principal. The base change `T ⊗[R₀] A₀` is smooth by
   `lem-weil-pbc-smooth-ring-map-base-change-composition`, and is reduced by steps 1 and 2.
5. By `lem-weil-pbc-directed-subalgebra-tensor-colimit`, these tensor models give a small
   filtered ring diagram with colimit isomorphic to `A`. For a nilpotent `x` of positive
   exponent `n`, clause (1) of `lem-pc-filtered-colimit-commrings-elementwise` gives a
   representative `y`. Clause (2), applied to `y^n` and zero, gives a later stage where
   the image of `y` has nth power zero. The arrows in that clause need not coincide:
   every ring map sends zero to zero. Reducedness of that stage kills the image of `y`,
   so cocone compatibility gives `x = 0`. This proves reducedness for every positive
   exponent without any finiteness hypothesis on `R`.
-/
theorem isReduced_of_smooth (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] [Smooth R A] [IsReduced R] : IsReduced A := by
  sorry

end Algebra

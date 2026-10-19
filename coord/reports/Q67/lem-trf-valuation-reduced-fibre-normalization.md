## Worker report

The module `Sheaf.TraceFormula.ValuationReducedFibreNormalization` states
`valuation_reduced_fibre_normalization` for Temkin, *Stable modification of relative curves*,
Theorem 3.5.5, Steps 2--5, printed pp. 22--24, as recorded by
`lem-trf-valuation-reduced-fibre-normalization`.  It introduces a field `K`, commutative
rings `V` and `A`, a `V`-algebra structure on `K` and `A`, the domain valuation ring `V`,
its fraction-field structure in `K`, and the separably closed hypothesis on `K`.  It assumes
`Module.Flat V A` and `Algebra.FinitePresentation V A`.

The geometric-reduced generic-fibre hypothesis is rendered by
`∀ (E : Type v) [Field E] [Algebra K E], letI : Algebra K (A ⊗[V] K) :=
Algebra.TensorProduct.rightAlgebra; IsReduced (TensorProduct K (A ⊗[V] K) E)`.
Thus every field extension `E/K` has reduced scalar extension of `A_K`, including the
empty/zero algebra case.  The `let AK := A ⊗[V] K` clause is the generic fibre.  The
relative integral closure is the actual Mathlib construction
`let B := integralClosure A AK`, so its elements are exactly those satisfying a monic
polynomial over `A`; no data is postponed by `sorry`.

The canonical generic-fibre map is explicitly rendered as
`let canonical : B ⊗[V] K →ₐ[V] AK :=
Algebra.TensorProduct.lift ((Subalgebra.val B).restrictScalars V)
Algebra.TensorProduct.includeRight (fun _ _ => Commute.all _ _)`.
The theorem requires `Function.Bijective canonical.toRingHom`, which states that this
specified canonical map is an isomorphism.  The finiteness clause is `Module.Finite A B`;
the flatness clause is `RingHom.Flat (algebraMap V B)`; and finite presentation is
`Algebra.FinitePresentation V B`.  Finally, for every algebraically closed field `Ω`
over `V`, the geometric fibre clause is
`IsReduced (TensorProduct V B Ω)`.  The proof is `sorry`, as required for stage 2.

Dependencies used are the recorded Mathlib declarations: `IsSepClosed` from
`Mathlib.FieldTheory.IsSepClosed`, `RingHom.Flat` from `Mathlib.RingTheory.RingHom.Flat`,
`Algebra.FinitePresentation` from `Mathlib.RingTheory.FinitePresentation`, and
`Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs` (imported by the preceding
module).  The relative integral closure is Mathlib's `integralClosure` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; tensor products and their canonical
maps are from `Mathlib.RingTheory.TensorProduct.Maps`; `IsReduced` and the geometric
reducedness vocabulary are from `Mathlib.RingTheory.Nilpotent.GeometricallyReduced`.
The node's other statement dependencies are definitions represented by these Mathlib
interfaces, so no private duplicate definitions were added.

Edge cases checked against the source statement and its proof route: `A = 0` (the zero
algebra is permitted), `V = K` (height-zero valuation), arbitrary valuation height,
and the possibility that a geometric fibre is zero.  No nonemptiness, finite-height, or
Noetherian hypothesis was added.  The `Ω` quantifier permits every homomorphism
`V → Ω` through its `Algebra V Ω` instance, including characteristic changes.

Searches for an existing declaration were made before writing the module:

* `msearch.py Q67 ... leanfinder` for relative integral closure over a separably closed
  valuation ring: only generic geometric-reducedness and integral-closure results;
  no theorem with the item's hypotheses and conclusions.
* `msearch.py Q67 ... loogle '"integralClosure", "finite"'`: only
  `IsIntegralClosure.finite` and related finite-extension results, requiring Noetherian
  hypotheses absent here.
* `msearch.py Q67 ... grep 'IsIntegralClosure.finite|integralClosure.*finite|valuation.*reduced|ZariskisMainProperty' RingTheory`:
  hits in localization, normal-closure, étale, and Dedekind-domain files, with no exact
  relative valuation theorem.
* `rg` over `WeilConjectures` and `lean/Sheaf` for valuation normalization,
  geometrically reduced fibres, and integral closure: no declaration matching this
  statement.  Existing nearby valuation modules concern different scheme or module
  statements.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q67

I reread the node statement beside the module.  The hypotheses match one-for-one: field
and valuation-ring data, fraction field, separable closedness, flatness, finite
presentation, and geometric reducedness of the generic fibre.  The module uses exactly
`A ⊗[V] K` for `A_K` and Mathlib's relative integral closure of `A` in that ring.  Its
canonical map is built from the inclusion of the integral closure and the right tensor
factor, rather than an arbitrary map; bijectivity is asserted on that map.  The four
conclusion clauses match the node in order: finite `A`-module, canonical generic-fibre
isomorphism, flat finitely presented `V`-algebra, and reduced fibres after every map to
an algebraically closed field.  The zero algebra and all valuation heights remain
allowed.  No statement correction or dependency-module repair was needed.

## Maintainer review fix (2026-10-18)

H3 (universe too small): the delivered `hgeom` quantified over `E : Type v` with the same free
universe `v` as the conclusion's `Ω`. At `u = 1, v = 0` with `K : Type 1` larger than every
`Type 0` type, no `Type 0` field is a `K`-algebra (field maps are injective), so `hgeom` was
vacuous and the instance claimed finiteness for, e.g., `A = V[x]/(x^2)`, where
`B = V ⊕ Kx` is not finite over `A`. The fix quantifies `E : Type u` (the universe of `K`,
containing `AlgebraicClosure K`, enough by the algebraic-closure test); `Ω : Type v` stays
universe-polymorphic. H8: the statement docstring now carries the node's eleven proof steps.

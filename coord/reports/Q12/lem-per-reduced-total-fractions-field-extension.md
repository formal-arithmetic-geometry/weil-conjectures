## Worker report

The module `Sheaf.RingTheory.ReducedTotalFractionsFieldExtension` states
`Algebra.reduced_total_fractions_field_extension`, with one `sorry` and no other
postponed proofs. The three conjuncts give the comparison, field towers, and principal
localization. No node statement or dependency changed. The original node has empty
`proof` and `proof_deps`; its theorem docstring supplies a natural-language proof
following Stacks 0C3N and the localization universal property.

Hypotheses and objects, clause by clause:

- The field `k` is `[Field k]`, the commutative integral domain `A` is
  `[CommRing A] [IsDomain A]`, its scalar structure is `[Algebra k A]`, and finite
  type is exactly `hA : RingHom.FiniteType (algebraMap k A)`.
- The fraction field `F` is Mathlib `FractionRing A`, the localization at
  `nonZeroDivisors A`, which in a domain are precisely the nonzero elements.
- Every field extension is quantified by `(L : Type w) [Field L] [Algebra k L]`.
  The tensor algebra is `A ⊗[k] L`. `ReducedScalarExtension` transparently abbreviates
  its quotient by Mathlib `nilradical`. `FractionRing (ReducedScalarExtension k A L)`
  is its total quotient ring, without any domain assumption on that reduction.
- The first conjunct gives `∃! theta`, with the stated source and target, its
  fraction formula, and `RingHom.ker theta = nilradical (FractionRing A ⊗[k] L)`.
  `TensorFractionFormula` multiplies the displayed fraction identity by its
  denominator. That denominator is a unit: already the case `b = 1, l = 1`
  supplies its inverse, and geometrically it is the image of a regular element.
  Thus this is exactly the fraction identity, including arbitrary `s ≠ 0`.
- Towers have `[Algebra L M] [IsScalarTower k L M]`. The unique reduction map `r`
  is characterized on every quotient representative by `TensorProduct.map` with
  identity on `A` and the tower homomorphism on `L`. It is injective and preserves
  `nonZeroDivisors`, exactly as asserted.
- The unique total-fraction map `q` extends `r`, is injective, and explicitly sends
  `Localization.mk x s` to the numerator image times the inverse denominator image.
  `Ring.inverse` here agrees with inverse of a unit; preservation of regularity
  ensures these denominator images are units in the target total quotient ring.
- The last part of the tower conjunct is the ring-hom equality
  `q.comp thetaL = thetaM.comp (TensorProduct.map ...).toRingHom` for comparison
  maps satisfying their defining formulas. Their existence is the first conjunct.
  The formulas determine all maps uniquely, so identities and composites in longer
  towers are also canonical; these are not arbitrary existential maps.
- Principal localization quantifies every `a : A` with `ha : a ≠ 0`.
  `Localization.Away a` is exactly `A[1/a]`. The unique ring equivalence `e`
  between total quotient rings is specified on all `b ⊗ l` by the canonical
  localization map. This fixes its direction and its canonical normalization.
  `thetaLocal` uses `Frac(A)` as source, under the canonical identification with
  `Frac(A[1/a])`; its formula is specified using the actual tensor map of
  `A → A[1/a]`. Its kernel is the nilradical, and `e.comp theta = thetaLocal`
  states principal-localization compatibility. No arbitrary identification is used.

The four helpers only abbreviate standard objects, compose the quotient and
localization maps, or name the displayed formula. They contain full real data;
none chooses a map from a `sorry` existence proof. They belong to this node's
construction and are listed in `lean.declarations`.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`, definition at line 217, using
  `Algebra.FiniteType` at line 39.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, line 95;
  with fields its algebra map is the required injective field homomorphism.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.tmul`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, lines 81 and 107; the ring structure
  and canonical tensor maps are from `Mathlib.RingTheory.TensorProduct.Maps`.
- `def-weil-pbc-module-localization`: `LocalizedModule`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, line 89, is the same underlying
  Ore localization as `Localization`. For rings the statement uses Mathlib
  `FractionRing`, the abbreviation `Localization (nonZeroDivisors R)` at line 716
  of `Mathlib.RingTheory.Localization.FractionRing`, and `Localization.Away`.
- Quotient maps are Mathlib `Ideal.Quotient.mk`; `nilradical` is the ideal of
  nilpotent elements (`Mathlib.RingTheory.Nilpotent.Lemmas`, lines 48–52).

Edge cases checked: `A = k`, `L = k`, identity field towers, `a = 1`, zero
numerators and tensor coefficient zero all give their usual canonical maps.
The zero ring is excluded exactly by the domain hypothesis; a zero denominator
and localization at zero are excluded exactly as in the node. Purely inseparable
extensions are allowed: the tensor ring may have nilpotents, so the kernel is
the nilradical rather than zero. Reducible scalar extensions are allowed:
the reduction is never assumed to be a domain, and total fractions are not
mistaken for a field. No finite/separable/algebraic hypothesis on L or M is added.
Universes u, v, w, t are explicitly bound and independent.

Searches (msearch.py Q12, 2026-10-19):

- LeanFinder: “The map from a fraction field tensor a field extension to the total
  fraction ring of the reduced tensor algebra has nilpotent kernel”: eight hits,
  including `Algebra.kerTensorProductMapIdToAlgHomEquiv` and geometrically reduced
  tensor products; none state the result or provide all these canonical maps.
- Loogle: `IsLocalization, nonZeroDivisors, TensorProduct`: three rank/base-change
  hits (`IsBaseChange.finrank_eq_of_le_nonZeroDivisors`, its rank variants), no match.
- Mathlib grep: `(totalQuotient|TotalQuotient|FractionRing).*(baseChange|tensor|Tensor)|
  nilradical.*[Tt]ensor`: zero hits.
- LeanSearch: “The map from total fractions tensor a field extension to total
  fractions of the reduced scalar extension has nilpotent kernel”: eight hits,
  including tensor kernel linear equivalences and geometric reducedness, no match.
- Direct rg of upstream WeilConjectures and lean/Sheaf for total-fraction/reduced
  tensor comparisons and the node id found no existing statement. Existing reduced
  Noetherian total-fraction decompositions concern component fields, not this map.
  Direct rg of Mathlib, upstream, lean/Sheaf and dag/lean_names_upstream.json found
  none of the five proposed declaration names already declared.

No statement dispute or correction is needed. Compilation is through scompile.py
only; no global build or edits to either read-only checkout were made.

## Second reading by Q12

This is a separate rereading by the dispatched worker; the dispatcher explicitly
forbids starting another agent, and the maintainer supplies independent review.
With the node and final module open, the rereading checked the three conjuncts
against every clause: reduction and regularity, injective total-fraction map and
its formula, the nilpotent kernel, the tower square, and every nonzero principal
localization. The tower map is the identity tensor the supplied field map;
the localization equivalence is tied to the supplied localization algebra map.
The fraction formula uses nonzero elements of A, while the total-fraction formula
uses nonzerodivisors of the possibly reducible reduction. The localized comparison
uses the original fraction field under its canonical identification, not a fresh
unconstrained field. Two redundant draft theorems were removed so that the final
single postponed theorem matches the single DAG statement. The proof docstring
was expanded to cover the tower and localization clauses as well as the kernel.

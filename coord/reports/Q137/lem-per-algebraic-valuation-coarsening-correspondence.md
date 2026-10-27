## Worker report

The module `Sheaf.RingTheory.AlgebraicValuationCoarsening` states
`ValuationSubring.algebraic_coarsening_correspondence`, with one postponed proof
and no new definitions. The accepted statement and split are unchanged.

Clause-by-clause reading:

- The fields are `K : Type u`, `L : Type v`, `[Field K]`, `[Field L]`.
  `[Algebra K L]` gives the specified embedding `algebraMap K L` (injective
  because its domain is a field). The two universes are independent.
- The finite algebraic extension is `[FiniteDimensional K L]`. A finite
  field extension is algebraic, so a separate algebraicity hypothesis would
  be redundant. No separability, henselianity, rank or nontriviality is assumed.
- `W : ValuationSubring L` is a subring with the inverse alternative.
  Mathlib supplies both `ValuationRing W` and `IsFractionRing W L`.
- `V = W ∩ K` is `W.comap (algebraMap K L)`, which already has type
  `ValuationSubring K` and fraction field `K`. This uses the existing
  restriction construction, not a separate definition of valuation rings.
- The additive value group is `Additive (OrderDual W.ValueGroupˣ)`.
  Mathlib's `ValueGroup` is the quotient of `L` by multiplication by `Wˣ`,
  with an additional zero class. Taking units removes precisely that class.
  `OrderDual` gives the Stacks additive valuation order, and `Additive`
  changes multiplication to addition. The quotient map is the existing
  `W.valuation`, restricted to units by `Units.map`.
- The image subgroup denoted by Γ_V is the image of `Kˣ` under
  `Additive.ofMul (OrderDual.toDual (Units.map
  W.valuation.toMonoidWithZeroHom.toMonoidHom
  (Units.map (algebraMap K L).toMonoidHom a)))`.
  An element of `Kˣ` is in the kernel precisely when both it and its inverse
  lie in `V`; thus this is the asserted ordered identification with
  `Kˣ/Vˣ`. The field embedding and quotient maps are the canonical ones.
- The first conjunct quantifies over every `δ` in that additive value group
  and supplies `n : ℕ`, `0 < n`, and `a : Kˣ` with `n • δ` equal to its
  displayed image. Positive naturals are exactly the positive integers of
  the statement. This states the quotient torsion condition directly.
- The second conjunct provides an order isomorphism between
  `{U : ValuationSubring L // W ≤ U}` and
  `{R : ValuationSubring K // W.comap (algebraMap K L) ≤ R}`.
  Its forward map is pinned by `(e U).1 = U.1.comap (algebraMap K L)`.
  Hence it is the canonical restriction bijection, preserving inclusion.
  The inverse also preserves inclusion, as the accepted proof's Step 6 says;
  equivalently, the overring types are linearly ordered and the prescribed
  inclusion-preserving bijection necessarily reflects order.
- The third conjunct says for every `U` containing `W` that
  `U = ⊤ ↔ U.comap (algebraMap K L) = ⊤`. The two top valuation subrings
  are the ambient fields `L` and `K` respectively.
- The fourth conjunct explicitly states the requested proper lift: every
  `R` containing `V` with `R ≠ ⊤` has `U` containing `W`, with `U ≠ ⊤`
  and restriction `R`. Equality with the starting ring is allowed, as in
  the node's definition of an overring. If a strict overring is desired,
  the prescribed order isomorphism also preserves strict containment.

Dependency declarations read and used:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and
  its `algebraMap`, exactly the dependency's recorded field-extension API.
- `def-trf-valuation-ring`: `Mathlib.RingTheory.Valuation.ValuationRing`,
  `ValuationRing` and `ValuationRing.TFAE` (the node's `mathlib_match`).
  `Mathlib.RingTheory.Valuation.ValuationSubring` bundles the subring
  version of that same inverse-alternative definition; its valuation-ring
  and fraction-field instances, `ValueGroup`, `valuation`, and `comap`
  were read in full. This is an existing usable specialization, so no
  dependency repair or duplicate valuation-ring definition is needed.
- Proof dependency `lem-trf-valuation-value-group-torsion`:
  `Sheaf.RingTheory.ValuationValueGroupTorsion`,
  `WeilConjectures.algebraic_extension_value_group_torsion`, imported
  without `public`. Its full signature and proof docstring were read.
- Existing Mathlib `FiniteDimensional` renders finiteness; existing
  `Additive`, `OrderDual`, ordered units, and order isomorphisms render
  the value-group convention and the inclusion-preserving correspondence.

The docstring contains all six accepted proof steps: restrict the inverse
alternative; apply the algebraic power-times-unit theorem; construct the
inverse correspondence by fractions; check its restriction; check uniqueness
using `s = a⁻¹`; and check inclusion and the whole-field/proper cases.
Nothing is proved at stage 2.

Edge cases checked mathematically before writing: `K = L` gives the identity
restriction correspondence; `W = L` gives trivial value groups and singleton
overring types; a trivial restriction forces the upper valuation trivial
(by the torsion condition in an ordered group), consistent with Stacks 0AAV.
The identity value-group element uses `n = 1`, `a = 1`; the zero class of the
field is excluded by taking units. Purely inseparable finite extensions are
included, in every characteristic. `n = 0` is excluded explicitly; no bound
on valuation rank is imposed. A transcendental extension with a nontrivial
valuation trivial on the base illustrates why the extension hypothesis matters.

Sources inspected: the current node, both statement dependencies and the
power-times-unit proof dependency; the resolved stage-1 repair note (no withdrawn
Lean attachment was reused); Stacks algebra.tex Tags 00IB, 00ID and 0AAV and
more-algebra.tex Tag 0ASJ; ILO XX 4.4 printed pp. 373–374 (PDF pages 379–380);
and the latest blueprint's `lem-per-artin-gabber-affine-curve.proof.md`.
Bourbaki remains marked WANTED in the existing source record; the statement
and proof plan here use the accepted reconstructed split and available sources.
No statement correction or unresolved statement dispute was found.

Searches before writing (full service responses are in sandbox searches.jsonl):

- LeanFinder: “For an algebraic extension of valued fields restriction is an
  order preserving bijection between valuation overrings and the quotient of
  value groups is torsion”: eight hits about valuation extensions, equivalent
  valuations and value groups; none has this correspondence and torsion statement.
- Loogle: `ValuationSubring.comap, ValuationSubring.valueGroup`: zero hits;
  the lower-case `valueGroup` identifier is unknown to the service.
- LeanSearch: “restriction induces a bijection on valuation overrings in a
  finite algebraic field extension”: eight hits on valuation extensions,
  `bijective_rangeRestrict_comp_of_valuationRing`, and maps for overrings in
  one field; none states this algebraic restriction bijection.
- msearch grep: `coarsen|overring|def comap|ValueGroup`, restricted to
  `RingTheory/Valuation`: found the existing `ValueGroup`, `ofLE`, `mapOfLE`
  and `comap` APIs, not the theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `coarsen|overring|valuation.*torsion|valuation.*correspondence` found the
  existing torsion theorem and the algebraic prime-spectrum/height theorem,
  but no identical statement. The latter is an order correspondence for
  prime ideals, not the present prescribed restriction on valuation overrings.
- Direct search of both roots, Mathlib and `dag/lean_names_upstream.json`
  for `algebraic_coarsening_correspondence|AlgebraicValuationCoarsening`,
  and of `lean/WeilConjectures` for the node id, found no declaration.

## Second reading by Q137

I reopened the node and the completed module and matched every clause above.
The finite-dimensional hypothesis retains the finite extension condition;
units in the value group avoid the erroneous zero-class torsion condition;
the additive order dual agrees with Stacks 00ID. The restriction formula pins
the existential isomorphism to the map in the statement, and both the top
criterion and proper lifting clause are explicit. No additional hypotheses,
new notions, node changes, or mismatches were found. This is the worker's own
second pass; the maintainer supplies the independent delivery review.

Validation: `scompile.py Q137 lem-per-algebraic-valuation-coarsening-correspondence`
compiled the module successfully both as the sandbox probe and under its library
module name, with no errors or unexpected warnings. The Lean file has no lines
over 100 characters, and the sole changed field of the existing node is `lean`.

## What changed

The statement of `AlgebraicGeometry.Etale.supported_kummer_scalar_derived_units`
is unchanged. Its proof now assembles three applications of a flat-source scalar-unit
lemma. The original module has no remaining `sorry`.

The four private helpers in that module are proved in Lean:

- `constant_flat`: the constant coefficient sheaf is the monoidal unit.
- `ring_hom_eval_one_bijective`: evaluation at 1 identifies maps out of the free
  rank-one module with elements of the target module.
- `constant_ordinary_scalar_unit`: combine that bijection with the
  constant-sheaf/global-sections adjunction. The prescribed generator equation,
  evaluated at the terminal etale object and at 1, identifies the actual map.
- `finite_constant_flat`: use the finite-stalk formula, the generic constant-stalk
  isomorphism, and the geometric-stalk flatness criterion. Each stalk is a finite
  product of copies of R, hence a finite free module. This works for every finite
  morphism, so the closed-immersion special case requires no separate support test.

The two new modules are `Sheaf.CategoryTheory.FlatScalarUnit` and
`Sheaf.AlgebraicGeometry.FiniteOrdinaryScalarUnit`. Their public statements isolate
respectively the passage from ordinary to derived universality with flat source,
and preservation of ordinary scalar universality by finite direct image. Both
are imported privately by the item. The other added private imports are the
existing etale flat-stalk criterion, finite stalk formula, categorical/module
flatness comparison, and module product API.
No existing public import, definition, or declaration signature changes.

## Proved and sorry left

One existing hole is closed by a complete Lean proof:
`AlgebraicGeometry.Etale.supported_kummer_scalar_derived_units`.
Two new holes are added:

- `SheafExactDegreeZero.scalarUniversal_of_flat`, node
  `lem-asd-flat-ordinary-scalar-unit-derived`.
- `AlgebraicGeometry.Etale.finite_ordinary_scalar_unit`, node
  `lem-asd-finite-ordinary-scalar-unit`.

This is a decomposition, not a sorry-free proof of the original mathematical
obligation: one hole closed, two added, packet net minus one. The ordinary
constant units and all three required source-flatness facts are proved, and the
remaining obligations are independent ordinary and derived steps. Neither new
statement is the three-clause supported theorem under another name.

The flat-source statement is tested mathematically for identity coefficient maps,
F=0, the zero ring, and nonflat coefficient extensions such as Z to Z/2. Flatness
of the source, rather than the coefficient map, is precisely what makes its
single complex compute derived extension. The finite-image statement includes an
empty geometric fibre, repeated lifts, identity morphisms, arbitrary nonflat
coefficient maps, and zero coefficients. Extension of scalars commutes with its
finite product of stalks because that product is a finite direct sum. No global
Noetherian or coefficient-finiteness assumption enters either statement.

All three sandbox modules compiled cleanly through the prescribed server compiler:
FiniteOrdinaryScalarUnit in 3.0 seconds, FlatScalarUnit in 2.7 seconds, and the
assigned module in 7.5 seconds. Delivery runs the required compilation and
preflight checks on the final packet.

## No longer needed

No original Lean import is removed, and no module is withdrawn. In particular,
this packet makes no claim that an upstream declaration may be removed.

The item no longer needs the following as direct proof dependencies:

- `sk-lem-pbc-finite` and
  `lem-weil-pbc-exact-functor-derived-functor`: the proof works with ordinary
  sheaves and their singles; it does not identify a derived direct image.
- `def-kun-derived-tensor` and `def-pur-sheaf-tensor-product`: the concrete
  flatness argument uses the existing monoidal flatness API and the finite free
  stalk module instead of constructing a new tensor or acyclicity proof.
- `prop-weil-pbc-geometric-stalks-exact`: encapsulated by the existing flat-stalk
  criterion; it is not separately invoked.
- `def-pc-kflat-complex` and `lem-pur-derived-change-of-rings`: used only in the
  remaining general flat-source lemma, not directly in the item.
- `lem-pod-etale-stalk-tensor-scalar` and
  `lemma-weil-pbc-geometric-stalk-conservative`: used only in the remaining
  ordinary finite-image lemma, not directly in the item.

The last two pairs are still transitive mathematical dependencies. No claim of
whole-library pruning is made. The item's DAG copy records the actual route.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface repair is needed. The plan's support-by-support
K-flat proof is longer than necessary: finite direct image of the constant ring
already has finite free geometric stalks, even without a monomorphism hypothesis.
The ordinary constant normalization is proved using its global-sections
adjunction rather than checking every stalk.

The existing derived-change-of-rings attachment presents ordinary modules and
ringed-site module sheaves, while this item uses raw ModuleCat-valued sheaves and
its named exact-single unit. It does not directly provide the required
flat-source universal-arrow computation in that presentation. Likewise the
available proper coefficient comparison theorems assume finite coefficients
(and some assume Noetherian schemes); the item has arbitrary commutative rings.
They cannot close the stated item by specialization.

Source reading used Stacks `etale-cohomology.tex`, Tag 03QP,
`proposition-finite-higher-direct-image-zero`; `sites-modules.tex`, Tag 03EL,
`lemma-tensor-product-pullback`; and `sites-cohomology.tex`, Tags 06YQ, 06YY,
07A6 (`lemma-bounded-flat-K-flat`, `lemma-derived-base-change`, `lemma-adjoint`).
The original source label `lemma-change-of-rings` is not the label for Tag 06YY
in the current Stacks source; the new lemma cites the actual K-flat computation
and adjunction labels. The existing node
`lem-pc-bounded-above-flat-kflat-site` also labels bounded-above flat K-flatness
as 06YS; the current tags table identifies `lemma-bounded-flat-K-flat` as 06YQ.
This packet uses its bounded-flat mathematical content and records the current
label in the new node, without editing the other node. The current blueprint's Cartier coefficient paragraph
and the unit `sk-prop-sf-cbc` are retained.

## New nodes

`lem-asd-flat-ordinary-scalar-unit-derived` is the general flat-source computation
needed after the concrete source-flatness and ordinary-unit proofs. Its module
contains one public theorem with its complete natural-language argument.

`lem-asd-finite-ordinary-scalar-unit` is the ordinary finite direct-image scalar
mate calculation. Its conclusion stops at sheaf Hom bijections and contains no
derived universal property or flatness claim. Its module contains one public
theorem with its complete natural-language argument.

Both nodes inherit the item's chapter and unit and link through the item to its
blueprint ancestor. Searches covered the full DAG and blueprint, source library,
LeanSearch, Loogle, and Mathlib source grep. The recorded queries are the queries
actually run. Nearby results concerning ringed module objects, proper maps with
finite coefficients, and scalarUniversal-to-DerivedUnit transport are not these
statements. No definition repair, forced adaptation, or change record is needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the hole in
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionOrientationInputComparison`
by a construction and proof. A primitive root exists because the coefficient prime
is nonzero in the algebraically closed field. Its prescribed power is primitive
at the smaller level. The shifted `finiteReductionUnitComparison` is invertible
by the existing theorem, so conjugation by the two root charts constructs the
required isomorphism. Chart-change scalar compatibility proves its normalization
in every compatible pair, and cancellation of a single target chart proves
uniqueness. Existing signatures are unchanged. A private
generic categorical helper proves conjugation and cancellation once before
substitution of the coefficient categories. Scoped transparency settings prevent
unfolding the two different finite coefficient rings while elaborating this proof.

Local category-instance priorities match the proofs cached by
`Etale.DerivedCategoryModule`, as in the existing supported-Kummer modules.
The new module factors the transported chart into the real data definition
`finiteReductionLineChart` for an arbitrary k-scheme. The existing
`finiteReductionOrientationInputChart` calls it at the affine line. Unfolding the
new definition recovers the original chart body, including the same shift maps;
no data are chosen. The scalar lemma uses the same chart directly. This addresses
the expensive conversion of two separately elaborated chart expressions. The
shared-chart packet compiled without diagnostics through lcompile.py; the sibling
retains transparency during backward elaboration.

Added the public import `Sheaf.Paper.FiniteReductionLineChartScalars`, needed by
the existing chart definition, and the proof-only
Mathlib algebraically closed roots-of-unity import. The new module states only
the scalar compatibility of two changes of the degree-one chart, for a supplied
map between shifted units. It constructs no comparison of Tate-line objects.

## Proved and sorry left

One of the item's three original holes is closed by decomposition:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionOrientationInputComparison`
(node `def-pur-finite-affine-orientation-comparison`). Its combining proof has
no holes. This is not a net hole reduction: one lower hole is added.

Two original holes remain, unchanged, in node
`def-pur-finite-affine-orientation-comparison`:

- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionOrientationExceptionalComparison`.
- `WeilConjectures.PurityFiniteSetting.finiteReductionOrientationExceptionalComparison_isIso`.

One added hole remains:
`WeilConjectures.PurityFiniteSetting.finiteReductionLineChart_scalars`, in new
node `lem-pur-finite-reduction-line-chart-scalars`. Its whole proof is `by sorry`;
its docstring and node give the integer-scalar argument and edge cases. Thus the
item has two holes after the change, and the whole delivery has three. No hole
was added inside a definition. The existing unit-comparison invertibility theorem
is reused as stated, although it is itself unfinished in its own module.

## No longer needed

None: no existing import, module or declared dependency is removed. The affine
Cartier and supported Kummer steps remain as previously proved. The source-chart
independence lemma for shifted pullback tensor powers was examined; it is not a
one-line specialization to the direct degree-one orientation-input charts, which
have different endpoints and normalization factors. The new lemma isolates only
the scalar calculation needed for these charts. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current DAG's last step recorded three unfinished obligations without named
steps for their missing arguments. It now records the input comparison's actual
construction and its scalar-chart dependency, and explicitly retains the two
closed exceptional obligations. The existing smooth exceptional-comparison
statement cannot be specialized to the zero section: that map is a closed
immersion and is not smooth. This delivery does not alter that statement or the
zero-section hypotheses.

The scalar statement was checked on identity reduction, ramified positive
levels, and the empty scheme: the same integer chart-change factors cancel in
all cases. It assumes no quotient flatness or finite type of its arbitrary
scheme. Search results and the source are recorded in the new node.

## New nodes

`lem-pur-finite-reduction-line-chart-scalars`, module
`Sheaf.Paper.FiniteReductionLineChartScalars`, states that a supplied map between
reduced shifted coefficient units commutes with compatible root-chart changes.
This is strictly the chart-independence step: it gives neither existence nor
uniqueness of a Tate-line reduction isomorphism, and it requires two actual
compatible primitive-root pairs as inputs. The item separately proves root
existence, constructs an isomorphism using the existing unit comparison, proves
all chart equations, and proves uniqueness.

Change record: `coord/changes/A4-affine-orientation-input-proof-context.md`.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finitePerfectAdic_stalk_models` by an
explicit finite-level local-constancy and covering-sieve argument. Its signature and
`FinitePerfectAdicLevelMarkings` are unchanged. The added imports of the item are
proof imports of `Sheaf.Paper.FinitePerfectAdicEtaleStalkData` and
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`.

The proof constructs its normalized tower explicitly. It uses the existing derived
module scalar adjunctions for level and consecutive quotient maps, and defines
each transition as the adjoint transpose of a supplied scalar-extension
isomorphism. The inverse law of the hom-equivalence proves normalization.

On each extracted connected chart and for each quotient level, the proof installs
finiteness of the coefficient ring from `d.quotientFinite`, then applies the existing
`AlgebraicGeometry.Etale.finiteRing_derived_local_constancy` at the actual derived
geometric stalk specified in the data. It composes the resulting etale cover maps
with the original chart map and forms `Sieve.ofArrows`. Joint surjectivity proves
that this sieve is covering. An arbitrary arrow in the sieve factors through a
covering object; the conditional coefficient comparison transports that object's
stalk isomorphism to the required isomorphism on the arbitrary arrow's domain.
There is no choice of compatible markings between quotient levels.

One new module isolates the earlier, different operation: descending the finite
quotient diagram and extracting its algebraic stalk levels and consecutive
scalar-extension isomorphisms. It does not construct the normalized tower. Its data
record a connected chart, a point, bounded finite-lisse etale levels, and a
coefficient comparison **conditional on a supplied etale stalk-trivialization**.
They contain no normalized tower, stalk-trivializing cover or marking sieve.
The existing finite-ring local-constancy theorem is therefore an essential remaining input to the proved
assembly, rather than a new hole or a renamed assumption.

The new derived stalk functor is the actual exact geometric fibre functor induced
on derived categories. The data are an ordinary structure, with no construction by
choice from the remaining existence theorem. No existing definition, statement,
attribute, instance or public import changes, and no importer adaptation is needed.

Both modules compiled through `lcompile.py --all`: the new extraction module in
13.3 seconds and the assigned module in 9.9 seconds. The sole style warning
(`letI` for a proposition) was corrected to `let` before delivery. The assigned
module's declaration signatures and public imports are unchanged; all DAG
references exist and their recorded signatures match the Lean declarations.

## Proved and sorry left

Original holes closed in the item's text: one,
`AlgebraicGeometry.Scheme.finitePerfectAdic_stalk_models`
(node `lem-weil-pbc-finite-perfect-adic-stalk-models`). Zero holes remain in the item.

One hole is added, as the entire proof of the public theorem
`AlgebraicGeometry.Scheme.finitePerfectAdic_etale_stalk_data`, in
`Sheaf.Paper.FinitePerfectAdicEtaleStalkData`
(node `lem-weil-pbc-finite-perfect-adic-etale-stalk-data`).

This is a decomposition, not a complete proof of the existence theorem: one upper
hole is replaced by one narrower obligation. The adjoint tower construction,
connected-chart derived local constancy and generated-sieve assembly are now implemented using the existing
finite-ring theorem and real Lean code. Net direct hole change is zero.

## No longer needed

No original Lean import is removed and no module is withdrawn. The item's direct
proof dependencies are now the new etale stalk-data extraction node,
`lem-weil-pbc-finite-ring-derived-local-constancy`, the existing module scalar
adjunction theorem `lem-sfb-constant-realization-derived-scalar-extension`, and
the coefficient datum's quotient-finiteness assertion. The other original proof dependencies move into the
new node's descent, stalk and coefficient-transport construction:

- `def-pc-perfect-ring-complex`;
- `def-weil-pbc-ringed-derived-restriction`;
- `lem-weil-pbc-completed-constant-sheaf-reduction`;
- `lem-weil-pbc-constant-sheaf-geometric-stalk`;
- `lem-weil-pbc-finite-ring-constructible-derived-origin`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`;
- `lem-weil-proetale-weakly-etale-localization`;
- `prop-weil-pbc-geometric-stalks-exact`;
- `thm-weil-pbc-site-comparison`.

They remain mathematically needed below that new node. No global pruning or net
closure-progress claim is made. The unit's statement and realized steps stay.

## Where the brief, the DAG or earlier work was wrong

The existing plan was mathematically suitable, but it did not provide a Lean
interface for the descended finite etale levels, their chosen geometric stalk,
and the conditional coefficient comparison. The new structure specifies this
interface. In particular its comparison does not assert existence of the local
isomorphism it consumes; that existence is proved in the parent by the existing
connected-chart local-constancy theorem.

I read the finite-ring comparison and local-constancy signatures and the source
proofs in `proetale.tex` (the normalized diagram paragraph of
`lemma-connected-adic-lisse`, Tag 09C6, and finite coefficient derived comparison),
`etale-cohomology.tex` (`lemma-connected-ctf-locally-constant`), and
`sites-cohomology.tex` (`lemma-locally-constant-map`). Search found no exact extraction
API for this interface in Mathlib or the source library. I also inspected
`AdicResidueStalkTowerFamily` and `AdicEtaleStalkLevels`: they use the separate
coefficient-sized site model and completeness/constructibility data not supplied
by the present interface. Their scalar-adjunction construction does apply and is
reused in the assigned proof. The existing project local-constancy theorem
is reused directly.

Edge cases checked: the empty base is covered by an empty etale cover, so no point
of it is selected; each data-carrying chart is connected and has a chosen point.
The zero ring and zero complexes satisfy the same geometric-stalk and transport
constructions. Coverings are chosen separately for each n. The generated sieve
includes arbitrary domains and their factorization arrows, rather than only the
listed covering objects. Neither completeness nor a perfect model over A is added.

## New nodes

`lem-weil-pbc-finite-perfect-adic-etale-stalk-data` isolates the descent and
algebraic stalk-level reduction isomorphisms before finite-level local trivialization.
Its module also defines the actual derived geometric stalk functor and its concrete data
structure. It is sourced to the first paragraph of Stacks Tag 09C6 and the finite
coefficient descent and tensor/stalk comparisons already listed in the parent DAG.
Its Lean statement contains no marking sieve and no common pro-etale cover. The
parent implements the separate local-constancy step from the existing theorem.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

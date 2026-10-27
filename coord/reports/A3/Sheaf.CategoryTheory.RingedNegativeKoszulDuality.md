## What changed

Replaced the hole in `CategoryTheory.ringedNegativeKoszulSuccDuality` by induction on
list length, using the already proved zero-factor case and a one-factor tensor-Hom
comparison. The induction constructs the successor isomorphism by tensoring the tail
isomorphism and composing with that comparison. It proves the transition square by
bifunctor naturality and contravariant functoriality, and proves the empty-subset unit
by naturality of the actual total-tensor inclusion. The latter calculation uses a
proved private helper `tensor_inclusion_map`; no subset-coordinate identification is
assumed in the induction.

Added the proof-only import `Sheaf.CategoryTheory.RingedNegativeKoszulFactorHomTensor`
and its one public statement. Updated the item's node to the induction actually
written in Lean. No existing public signature, public import, definition, source-library
module, target statement or unit route changes.

Validation: remote `lcompile.py --all` compiled both modules without warnings or
errors. The main module took 35.5 seconds; the single-factor statement took 1.9
seconds. Both are below the 60-second delivery limit.

## Proved and sorry left

Original holes: one, `CategoryTheory.ringedNegativeKoszulSuccDuality`
(node `lem-weil-pbc-ringed-negative-koszul-duality`). Its body now has no hole.
The private induction and total-tensor inclusion helper also have no holes.

Added holes: one, `CategoryTheory.ringedNegativeKoszulFactorHomTensor`
(node `lem-weil-pbc-ringed-negative-koszul-factor-hom-tensor`). This is the only
`sorry` left in the delivery. The theorem treats one positive two-term factor
against an arbitrary tail complex. It contains neither a list of negative factors
nor an induction on generator count. Its docstring and node give the two-summand
map, the sign `(-1)^(n+1)`, inverse, differential calculation, naturality and
projection normalization.

This is a decomposition, with one original hole closed and one strictly smaller
hole added, hence net zero holes. It is not claimed as a proof with no remaining
assumptions. The recursive assembly, including both required compatibilities, is
proved in the original module.

## No longer needed

None. The original public import and all three original definition dependencies
remain necessary. No module is withdrawn. The argument does not require separate
all-length subset-basis duality, finite-degree inverse, or transition/unit lemmas:
these are obtained by the explicit induction from the single-factor comparison.
The searched general dualizable-complex and finite-evaluation modules were not
imported, since they do not identify the specified negative two-term factor.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The three original dependency
nodes provide the constructions but no normalized dual comparison. The nontrivial
first step of the original proof therefore could not simply be applied as an
existing theorem. The missing local two-summand calculation is now stated precisely,
and the whole finite-list induction has been written rather than split off again.

Checked the proposed local statement on the zero coefficient complex, zero ring
sheaf, empty site, b=0 and invertible b. The signed two-summand formula uses no
scalar inverses and still gives inverse maps in those cases. In degree -1 with
coefficient O[0] its sign is one; in the empty-subset degree-zero summand its sign
is also one. Thus it preserves exactly the units required by the original item.

## New nodes

`lem-weil-pbc-ringed-negative-koszul-factor-hom-tensor`, in
`dag/nodes/sec-proper-base-change/`, states the rank-one tensor-Hom comparison
with arbitrary tail complex, tail naturality, the explicit adjacent transition and
the degree-zero projection equation. It is sourced to Stacks Tag 0A0E and Tag
0A90. Its proof explains the two-summand calculation and then the existing
componentwise currying statements (degreewise characterization, differential and
naturality), and uses the rank-one specialization of finite-free internal Hom
for basis evaluation. These are generic closed tools from the Picard unit; no
node of the proper-base-change route supplies these general APIs. It is strictly
the local successor step used by the proved induction, rather than the all-length
conclusion under another name.
No change record is needed: no existing statement or definition changes.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

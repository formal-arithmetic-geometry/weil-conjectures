## What changed

Added two named intermediate declarations splitting the categorical equivalence from the
ring-identification formulas. The target theorem now introduces its let-bound context and
combines these declarations; all construction work remains isolated in the two named
intermediate sorries.

## Proved and sorry left

`etale_chart_residue_triples_equivalence` is proved by combining the two intermediate
statements. Sorries remain in `etale_chart_residue_triples_equivalence_functor`
(node `split-etale-chart-functor`) and
`etale_chart_residue_triples_equivalence_ring_iso` (node `split-etale-chart-ring-iso`).

## No longer needed

None; all original imports are retained for the public target signature and intermediate
statements.

## Where the brief, the DAG or earlier work was wrong

The previous attempt abandoned before encoding the planned route. The let-bound target can
be reduced cleanly by introducing its local definitions explicitly; the categorical and
compatibility portions are independent intermediate obligations.

## New nodes

`split-etale-chart-functor` and `split-etale-chart-ring-iso` record the two deferred
construction obligations.

## Second reading by R1

1. The delivered module preserves the original target signature byte for byte; only the
proof and two explicitly split intermediate declarations were added.
2. The module compiles locally with no errors, and the only remaining `sorry`s are the two
named split theorems, each represented by a DAG node; no forbidden declarations occur.
3. Both split statements are now recorded verbatim in their nodes, are strictly smaller
obligations than the target, and their docstrings state the deferred constructions and
source argument. No duplicate library declaration was found.
4. The target proof uses the shortest available reduction: introducing the let-bound
context and applying the two intermediate results. No imports were removable.
5. The parent node and unit route remain unchanged; the new node proof dependencies match
the declarations and imports used by the module.

Changed the first split comment into a complete theorem docstring, shortened the long
line in the ring-isomorphism statement, and replaced the vague node statements with the
verbatim Lean signatures. The ring-isomorphism node's proof description was corrected to
match its actual obligation.

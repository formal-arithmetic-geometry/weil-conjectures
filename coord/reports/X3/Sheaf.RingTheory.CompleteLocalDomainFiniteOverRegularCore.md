## What changed

Proved `IsLocalRing.complete_local_domain_finite_over_regular_core` with its original
signature unchanged. Added one proof-only import of the new parameter-map module and
proof-only imports of the existing power-series regularity and finite-over-complete-ring
modules, plus Mathlib tools for incomparability, kernel dimension drop, finite algebras,
and transport of adic completeness along a ring equivalence.

The new parameter-map assertion covers precisely the coefficient/parameter construction
of Stacks Tag 032D, up to the finite reduction. The original module supplies the subsequent
argument: finite reduction and Hausdorffness give module finiteness by Tag 031D;
incomparability gives the dimension bound for the image; a nonzero kernel forces a
one-dimensional drop, contradicting the equal finite dimensions; the range equivalence
transports regularity and completeness. No data definition or declaration signature changed. The unused public CohenRing import is removed;
the sole direct importer already imports CohenRing itself.

Validation: both delivered modules compile without warnings through lcompile.py.
Read the Stacks Tag 032D webpage and upstream stacks-project algebra.tex, label
`lemma-complete-local-Noetherian-domain-finite-over-regular`. Searched the repository and
Mathlib by concept and declaration; LeanFinder and Loogle returned dimension and
Hausdorff tools, but no exact construction. LeanSearch returned Internal Server Error,
recorded as unavailable. The unit sk-thm-p1 realized list does not name this helper;
its route remains unchanged.

## Proved and sorry left

Closed the original hole in
`IsLocalRing.complete_local_domain_finite_over_regular_core`
(node `split-complete-local-domain-finite-over-regular-core`). The original module has
no remaining sorry.

Added one hole in `IsLocalRing.complete_local_domain_parameter_map`
(node `split-complete-local-domain-parameter-map`), in its own new module. Its proof is
exactly `:= by sorry`, with its source and six-step natural-language proof in the docstring.
This is a decomposition: one upper hole closed and one strictly smaller construction hole
added, for net zero holes before any dependency-closure accounting. Existing imported
holes in `MvPowerSeries.power_series_field_cohen_regular_complete` and
`Module.finite_and_span_eq_top_of_adicComplete` are unchanged, not added by this delivery.

The construction statement assumes neither finiteness of R over the power-series source
nor injectivity of its map. Those are proved in the original module. Witnesses are
eliminated inside a theorem, not chosen into definitions.

Edge cases checked mathematically: a field R permits n=0 and coefficients R, the zero
maximal ideal, and the cyclic quotient R; a mixed-characteristic complete DVR permits
n=0 and Cohen coefficients, with reduction R/pR; equal positive characteristic uses
field coefficients, while in mixed characteristic p is nonzero in the domain and reduces
dimension by one. In the mixed case p acts by zero on R/I, so the source residue field
really acts on the finite reduction. The zero ring is excluded by IsDomain.

## No longer needed

Removed the original unused public import `Sheaf.RingTheory.CohenRing`: the core's public
statement only needs adic completeness and regular local rings. The new parameter-map
statement still needs CohenRing, so this is import pruning, not a global module-pruning claim.
The sole direct importer, CompleteLocalDomainFiniteOverRegular, already imports CohenRing
publicly itself and compiles unchanged against the new core. The old core DAG proof dependency
`lem-weil-pbc-complete-local-domain-finite-over-regular` is removed: it is the parent
which already imports the core, so this was a circular proof edge. Its module is never
imported here; it remains needed above this item and is not globally pruned.

`Sheaf.RingTheory.IntegralExtensionDimension`
(node `lem-weil-pbc-integral-extension-dimension`) is not needed by this proof; the dimension
bound is proved directly using Mathlib's `Ideal.IsIntegral.comap_lt_comap` and
`Order.krullDim_le_of_strictMono`. This was a temporary exploration import and is absent
from the delivered module. No global pruning claim is made: other consumers may need it.

`Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue` is not needed for the core;
it remains used by the parent theorem. The parameter-map construction uses the existing
power-series universal-property node instead of the larger surjection-to-completion node
`lem-weil-pbc-power-series-onto-completion`; no proof of that surjectivity is needed here.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The core node's old sole proof dependency was its own parent theorem, whose Lean proof
already calls the core. It supplied no usable independent proof route. Replaced this edge
with the actual coefficient/parameter construction and the finite-module and power-series
lemmas of Tag 032D. The original statement is true and is unchanged.

The local literature directory contained no Stacks algebra.tex. Read the primary Stacks
page and downloaded the upstream source into the sandbox scratchpad (not delivered),
confirming the exact label and both cases. The helper's residue quotient is finite over
the source residue field even in mixed characteristic: p is included in I. No statement,
definition, or target correction was needed; no forced adaptations. The preflight requires
a change record for removal of a public import; the import-pruning record documents the
unchanged direct importer and its successful compile.

## New nodes

`split-complete-local-domain-parameter-map`, module
`Sheaf.RingTheory.CompleteLocalDomainParameterMap`: existence of field/Cohen power-series
parameter algebra of equal dimension, with Hausdorff target module and finite reduction.
It realizes the initial construction of Tag 032D and excludes its subsequent finiteness,
injectivity, and range identification. The proof steps cite existing coefficient-ring,
parameter, change-ideal, universal-property, dimension and Artinian-finiteness nodes.
Blueprint searches for parameter and complete-local-domain-finite-over-regular found no
matching imported blueprint assertion; the ancestor is the finite-etale-lifting branch
recorded on the parent node. Import-pruning change record: `coord/changes/complete-local-domain-core-cohen-import.md`.

## Second reading by X3

1. I compared the delivered core module with the repository version. The theorem signature is byte-for-byte unchanged; only proof-only imports and the proof body changed. The added parameter-map module is a new split-off declaration with its own node, and the CohenRing import removal is recorded in the change record.

2. I compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The core theorem has no remaining `sorry`; the only added hole is the named `complete_local_domain_parameter_map`, whose docstring gives its source and a complete construction argument. No forbidden declarations or hollow definitions occur.

3. The split-off parameter-map statement is strictly smaller than the core theorem: it provides the coefficient/parameter algebra, equal dimension, Hausdorffness, and finite residue reduction, while leaving finiteness and injectivity to the core proof. Its edge cases include equal and mixed characteristic, and the statement does not assume the conclusion it is used to establish. Repository and Mathlib searches found no existing declaration duplicating it.

4. Reading downward from the target, the core proof uses the parameter-map construction, finite-over-complete-ring theorem, power-series regularity/completeness, and Mathlib dimension/integrality tools. The old circular parent dependency is removed, and unused IntegralExtensionDimension and public CohenRing dependencies are pruned. The unit route remains the parameter construction followed by finite reduction, dimension/injectivity, and transport to the image.

5. The DAG nodes agree with the Lean declarations and proof dependencies: the core node records the four proof steps and the new parameter-map node records the five construction steps and its source. The unit `sk-thm-p1` is unchanged. No target or existing declaration signature was altered.

Changes made during this reading: added this second-reading section only; no Lean code or DAG content required repair.

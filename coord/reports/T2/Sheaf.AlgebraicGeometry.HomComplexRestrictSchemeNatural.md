## What changed
Proved `homComplex_restrict_scheme_natural` by assembling componentwise isomorphisms into a natural isomorphism. Added `HomComplexRestrictSchemeNaturalComponents.lean`, whose componentwise naturality theorem remains a named sorry.

## Proved and sorry left
Closed `homComplex_restrict_scheme_natural`. The new theorem `homComplex_restrict_scheme_natural_components` remains `sorry`, with node `lem-sc-hom-complex-restrict-scheme-natural-components`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The target requires a natural isomorphism of functors, while the existing open-restriction result only gives objectwise isomorphisms; the missing naturality was split into a separate theorem.

## New nodes
`lem-sc-hom-complex-restrict-scheme-natural-components` in `dag/nodes/sec-picard-framework/lem-sc-hom-complex-restrict-scheme-natural-components.json`.

## Earlier second reading (a previous round; superseded)
The componentwise theorem is a strict decomposition of the target naturality claim; the main proof assembles it with `NatIso.ofComponents`, preserving the target statement.

## Second reading by T2

1. Compared both delivered modules with the repository versions. Existing declaration signatures are unchanged; the only interface addition is the explicitly recorded componentwise split theorem.

2. Compiled both modules with `lcompile.py --all`. There are no errors, forbidden declarations, or sorries in the main theorem. The remaining `sorry` is only `homComplex_restrict_scheme_natural_components`, and is named in its node and docstring; probing the target shows only the expected `sorryAx` from that dependency together with standard axioms.

3. The componentwise statement is a strict reduction: it constructs each chain isomorphism and separately states the naturality equation for every coefficient map. The target proof then assembles these data with `NatIso.ofComponents`; no hypothesis is added and the target conclusion is unchanged.

4. The proof follows the existing route through the componentwise construction and uses no shorter existing declaration. The added import is proof-only. No imports or proof dependencies can be pruned, and the unit route remains unchanged.

5. The DAG Lean records match the declarations and proof dependencies. The split node cites the open-subscheme Hom comparison and records the Stacks source and its componentwise/product-projection proof route.

Changed during second reading: no source or DAG changes; added this review record only.

## What changed

Proved `WeilConjectures.compactSupportOpenRestrictionModel_scalar` with its original
signature and comparisons. The proof transposes along the native tensor adjunction
and compares the resulting section maps using the published unit normalizations.

The private calculations establish coefficient compatibility of canonical
realization and direct image, the explicit transported literal-restriction unit,
and preservation of that unit by the tensor-to-literal comparison. The only added
import is the private `import all` of `SfIntrinsicRealizationTransport`, which
provides the already proved realization-unit isomorphism on sections. No existing
public definition, declaration signature, attribute, or public import changes.

Updated the item's node proof and dependencies to record the actual calculations,
including the canonical intrinsic direct-adjunction node. No other existing module
or node is changed.

Validation: the complete proof compiled through `lcompile.py` in 34.0 seconds.
The profiler options used during debugging have been removed; delivery repeats
the compilation and mechanical checks on the final file.

## Proved and sorry left

Closed 1 of the original 1 holes:
`WeilConjectures.compactSupportOpenRestrictionModel_scalar`
(node `lem-weil-compact-support-open-restriction-scalar`).

Added 0 holes and split off 0 statements. Every new private theorem has a complete
proof. The delivered module contains 0 `sorry` occurrences. This is a proof from
existing library declarations, not a claim that all imported dependencies are
independently axiom-free.

## No longer needed

None. All original imports remain necessary for the existing definitions and
private proofs. The original declared dependencies remain used. No module or DAG
node is withdrawn, and no blueprint unit route is bypassed.

Mathlib search found the general adjunction mate and uniqueness identities, but
no existing theorem for this particular normalized scalar square. The proof uses
those general identities directly and introduces no new unproved dependency.

## Where the brief, the DAG or earlier work was wrong

No statement correction was required. The DAG's sectionwise argument was valid
but omitted the explicit realization/direct-image compatibility calculation and
the transported literal-restriction unit formula. These steps are now proved
inside the assigned module and recorded in its node. The proof uses no flatness,
surjectivity, nonzero-ring, or nonempty-open hypothesis; it covers the stated edge
cases without a case split.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

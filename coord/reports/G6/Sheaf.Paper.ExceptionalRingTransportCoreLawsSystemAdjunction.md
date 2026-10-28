## What changed

Added a constructive normalization of the right comparison in
`Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction`, using the existing
source-library theorem `Adjunction.ofNatIsoRight_eq_iff` and Mathlib's
`Adjunction.rightAdjointUniq`. No new Lean module or unproved statement is added.

`normalizedRealizeG` is the inverse of the unique isomorphism comparing the two
right adjoints of the integral operation's left functor. The new results prove its
adjunction equality, characterize every comparison satisfying that equality, give
a concrete `TransportCoreData.normalizeRealizeG` update, and prove existence and
uniqueness of the whole compatible family.

The obstruction results prove that any noncanonical supplied comparison fails the
law, and that a family of automorphisms nonidentity at one stage contradicts laws
for every datum. The sign version uses negative identity natural isomorphisms and
requires an explicit component where minus identity differs from identity.

The original signature is preserved. Its unsupported universal claim is marked
`STATEMENT-DISPUTED`. The original DAG node records the defect and points to two
new, completely proved construction/obstruction nodes. The unit route is unchanged.
I read Zheng, pp. 35-37, especially Construction 5.25, Lemma 5.22 and Propositions
5.24 and 5.26, and the current blueprint compatibility unit and uniqueness node.
Searches were run through `msearch.py` (LeanSearch, LeanFinder, Loogle and grep).

Change record: `coord/changes/exceptional-system-adjunction-right-comparison.md`.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split-off holes: **0**.
This is a proved canonical construction and diagnosis, not a proof or decomposition
of the original universal claim.

The sole remaining hole is
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_system_adjunction_law`
(node `lem-sf-exceptional-ring-transport-core-system-adjunction-law`).

Seven new theorems are proved, all in `WeilConjectures.ExceptionalIntegralScalar`:

- `normalizedRealizeG_adjunction`;
- `adjunction_law_iff_realizeG_eq`;
- `TransportCoreData.normalizeRealizeG_adjunction`;
- `existsUnique_system_adjunction_right_comparison`;
- `not_adjunction_law_of_realizeG_ne`;
- `not_forall_adjunction_law_of_realizeG_twist`;
- `not_forall_adjunction_law_of_neg_id_ne`.

Validation: the complete item compiled through `lcompile.py` without warnings.
An explicit two-file check then compiled the item in **9.8 seconds** and its sole
direct importer, `Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem`, unchanged
in **7.4 seconds**, against the submitted item and current unpublished sibling
dependencies. The temporary unchanged importer copy was then removed.

The two new definitions `normalizedRealizeG` and
`TransportCoreData.normalizeRealizeG` have complete bodies. Every new proof uses
provided data and the proved adjunction API, with no law-existence theorem and no
selection from a holed existence theorem. The inherited category and transport-data
definitions already rest on unfinished mathematics; this delivery does not claim
that their import closure is axiom-free.

## No longer needed

No tracked import, module or node is pruned. The existing public import of
`ExceptionalRingTransportCoreData` remains required. An experimental generic
helper module was removed from the sandbox when the source-library characterization
was found; it was never delivered. The proof directly uses that existing theorem.
The original universal law is not moved to another hole.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: `TransportCoreData.realizeG` has no compatibility constraint
with its freely specified system adjunction and left comparison. Conjugation alone
does not identify an arbitrary adjunction comparison. The proved iff states the
exact missing condition. The source constructs induced functors and specified
comparisons; it does not say every independently chosen comparison preserves the
specified units and counits.

A small mathematical example is the identity adjunction on modules over a
characteristic-zero coefficient ring. Replacing its right comparison by minus
identity changes its unit and counit. On a rank-one module this differs from the
original adjunction, although the functors and all data-field types are unchanged.
In the geometric setting the same test applies to the identity map of a nonempty
geometric point with integral coefficients. This delivery proves the twist argument
inside the actual integral categories, conditional on an explicit nonidentity
component; it does not formalize the geometric-point instantiation or claim an
unconditional Lean refutation. On a zero category the nonidentity hypothesis fails;
for the identity twist the canonical equation holds, as proved here.

The construction-level repair is to use the specified right-adjoint uniqueness
comparison while constructing the data and its reduction/evaluation comparisons,
rather than assert laws for arbitrary independently chosen data. The new explicit
normalization supplies this adjunction step. Changing the datum also requires
checking the reduction and evaluation equations, so their arbitrary versions were
not silently invoked or weakened. No other worker's module or signature changes.

## New nodes

`lem-sf-exceptional-system-adjunction-normalized-comparison` records the explicit
canonical family, its equation and uniqueness, the iff for a supplied comparison,
and the concrete datum update. All its declarations are proved or fully defined.
It uses the existing Mathlib leaf `det-sp-unique-right-adjoint`; it does not restate
that generic lemma as a new open obligation.

`lem-sf-exceptional-system-adjunction-comparison-obstruction` records the pointwise
obstruction and the universal twist and sign obstructions. All three are proved.
Neither new node adds a pending obligation. The unchanged original node remains
disputed and unproved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction": "de89a18f5dbf23db6b91b6d8b9ade1bfffeb5e4c"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem": {"hash": "4165610bc155c7566a70f987503df48599e484ad", "status": "OK"}}, "seconds": 139, "time": "2026-10-28T10:27:00+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

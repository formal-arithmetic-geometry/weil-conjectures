## What changed

Filled `WeilConjectures.SmoothPurityFieldExtension.fieldExtension` using the existing
simultaneous integral purity family and its normalized rational comparison theorem.
The source-localization normalization, localization of integral purity, canonical
pullback/twist scalar comparison, and right-comparison unit and cocycle laws all
come from `rationalScalarComparisonIdentification`.

The public `leftComparison` definition names the original three-factor coordinate
construction. Proved private categorical calculations transport a left adjunction comparison,
its identity equation, and its associator equation along the specified compact
realization. The existing purity-conjugation theorem supplies the smooth unit and
counit equations. Its comparison is identified with the canonical comparison by
the normalized purity square, and its adjunction with the specified adjunction by
equality of units. The statement, public imports, and source-library files are unchanged. Added two
proof imports. Changed `compactSupport` from an abbreviation to a definition with
exactly the same type and body, allowing a local irreducibility annotation to
avoid unfolding its large functor construction. The consumer check found zero
downstream modules; there are no forced adaptations. The change records are
`coord/changes/U4-smooth-purity-compact-support-transparency.md` and
`coord/changes/U4-smooth-purity-comparison-constructor.md`. The latter records the
definitionally identical shared constructor now used by `compactComparison`.
The new construction is attached to the existing item node. All additional
transparency annotations are local to the item; no shared dependency is changed.

Validation: the final module compiled cleanly with `lcompile.py` in 48.4 seconds (including the delivery axiom probe),
with no errors or warnings. All profiling and diagnostic options are removed.
The theorem signature is unchanged; the module contains zero `sorry` tokens.

## Proved and sorry left

Closed one hole: `WeilConjectures.SmoothPurityFieldExtension.fieldExtension`
(node `sk-lem-sp-field-extension`). Added zero holes. No `sorry` remains in the
item module, and no other Lean module is delivered. The imported comparison
lemmas retain their existing proof obligations; those are not new holes.

## No longer needed

No existing import is removed, no module is withdrawn, and no global pruning is
claimed. The proof reuses the more specifically normalized comparison assembly
rather than invoking `det-sp-field-extension-towers`,
`lem-pur-integral-coefficient-model-comparison`, and
`lem-pur-rationalized-smooth-adjunction-diagrams` directly. Their finite-tower,
completed-coefficient, and raw-localization arguments are already represented in
the normalized integral/rational comparison interfaces being reused. The generic
purity-conjugation dependency is used directly. The statement's integral-adjunction
and scalar-composition conventions remain unchanged. Removed the obsolete direct
tool approvals for `prop-coef-integral-exceptional-adjoint`,
`lem-weil-scalar-extension-composition`,
`lem-weil-compact-support-reduction-tower-functor`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and
`lem-weil-finite-free-completed-scalar-comparison`: the assembly does not invoke
these lemmas directly. This does not withdraw any declaration or claim that those
lemmas are unnecessary to the reused comparison modules.

## Where the brief, the DAG or earlier work was wrong

The planned three-step assembly has already been specialized in the library's
normalized adic and rational comparison modules. The rational specialization also
provides the source-localization and canonical-component normalizations required
by this item's actual Lean statement. The remaining work is transport of the
compact-support coordinates and identification of the prescribed adjunction.
The unit statement and its finite-reduction, integral-reconstruction, and
raw-localization argument are retained; no alternative duality or base-change
argument replaces them. No mathematical statement correction is needed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

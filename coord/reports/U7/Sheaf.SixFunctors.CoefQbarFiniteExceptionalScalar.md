## What changed

Repaired the disputed universal scalar assertion by requiring the existing trace
normalization of its finite dual-formula adjunctions. Proved the finite exceptional
comparison scalar equation by transporting the system's counit square and applying
injectivity of the normalized target adjunction transpose.

Added the proved `finite_exceptional_normalized_core`: from any old core, replace its
finite comparisons by right-adjoint uniqueness against trace-normalized adjunctions and
conjugate its common-stage comparisons accordingly. Adapted the sole caller,
`finite_exceptional_formula`, to construct this normalization; its public statement and
all target statements remain unchanged. The core module held by X3 is untouched.

The repaired scalar theorem combines the finite equation with a separate component
pasting identity for duality-pullback-duality. The full proof compiles from these named
steps; the remaining component identity is split into its own module and node.

Validation: all four packet modules compiled together in import order, each within
60 seconds (maximum 45.3 seconds). The unchanged direct consumer
`Sheaf.SixFunctors.CoefQbarVerdierExceptional` compiled against the updated artifacts
in 25.2 seconds; its temporary unchanged sandbox copy was removed.

## Proved and sorry left

Closed the hole of the **repaired**
`WeilConjectures.CoefQbarVerdier.finite_exceptional_formula_scalar`.
This does not prove the old false arbitrary-core statement.

Also proved the new
`WeilConjectures.CoefQbarVerdier.finite_exceptional_normalized_core`, including the
adjunction transport equality and the normalized component formula.

Added one hole, the entire named theorem
`WeilConjectures.CoefQbarVerdier.dual_formula_inclusion_scalar`.
It has no exceptional functor or exceptional comparison in its statement. Its docstring
and node give the complete substitution/naturality/cancellation argument, including zero
objects and repeated fields. There are no other holes in delivered files.

This is a normalization repair and a decomposition (one old hole closed, one strictly
smaller hole added), not a net proof-completion gain. The existing core-existence hole
remains in an unchanged dependency, outside this packet.

## No longer needed

No modules are withdrawn or globally pruned, and no old Lean import is removed.
The scalar theorem no longer uses the existential pairwise theorem
`RationalOperations.rationalExceptional_identifications`: its chosen pair cannot relate
arbitrary independently selected core identifications. The finite scalar equation instead
uses `rationalDualFormulaScalarCounit` for the supplied normalized adjunctions.

Removed its old direct proof dependencies
`lem-sf-rational-exceptional-identifications`,
`lem-pur-integral-operations-scalar-extension`, and
`def-weil-derived-pullback-tensor-hom`, replacing them with the precise scalar-counit,
coefficient-system and component-pasting steps. This is only a direct-edge change:
the exceptional-identification module is still used by the new normalized construction,
and derived pullback remains used by the component-pasting lemma. The parent's original
core-existence dependency remains required through normalized-core existence.

## Where the brief, the DAG or earlier work was wrong

T2's dispute is correct. A core records independently selected exceptional
identifications with their transported adjunctions. The same-field `normalized` equation
only transports the selected map; it does not fix its trace normalization or relate
choices at different coefficient fields. Replacing an identification at one stage by an
automorphism, together with its transported adjunction, preserves the old hypotheses.
For the identity map of a point, one can scale the comparison by 2 at one of two
distinct finite coefficient stages and leave the other unchanged, transporting the
adjunction and common-stage comparison along it. The demanded scalar square then
compares the factors 2 and 1 in a nonzero characteristic-zero coefficient category.
The previous proof plan wrongly applied an existential pairwise scalar theorem to these
arbitrary choices.

The repair uses precisely the already defined trace normalization of dual-formula
adjunctions. Its existence is constructed using the existing one-field theorem, so this
requirement does not become a new hypothesis of the finite formula or any target.

## New nodes

- `lem-coef-qbar-finite-exceptional-normalized-core`: proved construction of a core with
  trace-normalized finite adjunctions, without any scalar-square conclusion.
- `lem-coef-qbar-dual-formula-inclusion-scalar`: the sole new hole, for the independent
  duality/pullback component-pasting step. It omits the exceptional operations entirely.

Change record: `coord/changes/U7-finite-exceptional-scalar-normalization.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarDualFormulaInclusionScalar": "c42288396b928afcf43a3caf0c1195a35e34b9e4", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula": "9147acf8598287e307043f6e0f020c5fc96e1a1a", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalNormalizedCore": "04c4dbe07487567a6cf12efe37386fbcd8f8f12e", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar": "62eeeed01680a64aba8c0034e58be775718b4d11"}, "results": {}, "time": "2026-10-28T10:44:47+0800", "transitive": 0, "version": 1}
```

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the whole proof hole in
`WeilConjectures.rationalPullbackScalar_rightMate_isIso` by a complete Lean
argument implementing the node's third step. Its signature and existing public
imports are unchanged. Two private proof imports supply the coefficient steps.

The proof obtains left adjoints to the two scalar functors, applies the explicit
restriction/pullback unit equation, and uses injectivity of `bX.homEquiv` together
with `unit_mateEquiv_symm` to identify the inverse coefficient mate with the hom
of the supplied isomorphism. `iterated_mateEquiv_conjugateEquiv` then identifies
the prescribed geometric right mate with conjugation of that very map.
Conjugation preserves its invertibility. The argument works with the supplied
geometric adjunctions throughout; it asserts no existence of geometric right
adjoints. No arbitrary isomorphism between endpoints substitutes for the
normalized comparison.

Added two modules, each with one genuinely smaller coefficient statement and a
complete source-based proof plan in its docstring and node:
`Sheaf.Paper.RationalScalarExtensionRightAdjoint` and
`Sheaf.Paper.RationalRestrictionPullbackUnit`. The first concerns one scheme and
has no geometric map or right adjoints. The second states a componentwise unit
equation for restriction/pullback, has no geometric right adjoints, and is
conditional on supplied coefficient adjunctions. In particular it is not the
item theorem with its geometric right adjoints renamed or repackaged. The real
Lean proof combines these two separate steps. No new definition chooses data
from a mere existence statement: the only local choices are Mathlib left
adjoints, specified by their adjunction universal property, and an isomorphism
used directly in a proof.

Updated the item's proof, proof_deps and proof_origin to match the Lean proof.
No other existing module or node is changed. Checked the new statements for
identity field extensions, zero complexes, empty schemes and ramified
extensions. Trace denominators are inverted; a perfect integral trace pairing
is not assumed. All three files compile individually through lcompile.py in
import order; the first run took 6.5 s, 3.3 s and 6.4 s respectively. The final
run removes the three style warnings from the initial main proof.

## Proved and sorry left

This is a decomposition, not a complete proof of the coefficient mathematics:
one original hole closed, two lower holes added; net holes closed minus added
is -1. The item itself has zero holes.

Closed: `WeilConjectures.rationalPullbackScalar_rightMate_isIso`
(node `lem-sf-rational-pullback-scalar-right-mate`). Its new proof has no `sorry`.

Added and still open:

- `WeilConjectures.rationalScalarExtension_isRightAdjoint`
  (`lem-sf-rational-scalar-extension-right-adjoint`), one whole theorem hole.
- `WeilConjectures.rationalRestrictionPullback_unit`
  (`lem-sf-rational-restriction-pullback-unit`), one whole theorem hole.

There are no holes in definitions or private declarations. The new coefficient
holes are the original plan's trace-adjunction step and its explicit normalized
restriction/pullback step; the categorical combination is now proved.

## No longer needed

None globally. No existing public or proof import is removed, and no module or
node is withdrawn. The item's direct proof dependencies are now the two new
nodes. Its previous mathematical ingredients
`lem-weil-finite-free-completed-scalar-comparison`,
`def-weil-rationalization-karoubi`,
`lem-pur-integral-operations-scalar-extension`, and
`def-sf-finite-rational-derived-operations` remain needed in the statements or
plans of the two coefficient lemmas. They are not claimed as pruned.

Mathlib supplies the categorical final step directly, so there is no new
categorical sorry, generic double-mate node, stage-system construction,
algebraic-closure choice or family of geometric adjunctions.

## Where the brief, the DAG or earlier work was wrong

The listed declarations do not supply either a rational coefficient restriction
trace adjunction or its unit-normalized pullback square. Inspection of
`FiniteFreeCompletedScalarComparison`, `IntegralOperationsScalarComparisons`,
`SfRationalizationKaroubi` and `FiniteRationalDerivedOperations` confirmed that
the finite-free comparison and normalized scalar isomorphisms exist, but those
two additional steps are not their stated conclusions. The completed-coefficient
finite-free direct-image API concerns ambient categories and does not apply
directly to these raw rational constructible categories and arbitrary supplied
geometric right adjoints.

The rational realization/continuous-scalar APIs found in the project impose
Noetherian and finite-dimensional scheme hypotheses, which the item does not
have. They cannot be applied here by adding those hypotheses. No target or
other statement was changed.

The Bhatt--Scholze text was read at 6.7.2, 6.8.14(2) and 6.8.15. These passages
give the direct-image and rationalization context, rather than a separately
numbered theorem with the two trace formulas. The coefficient proofs in the new
nodes are explicitly marked as agent elaborations of the parent's detailed
trace argument. In particular 6.7.2 is not used to assert geometric
right-adjoint existence for an arbitrary scheme map.

Mathlib searches were run through msearch.py (LeanSearch, LeanFinder, Loogle
and grep, recorded in searches.jsonl). They found the ordinary module
restriction/coextension adjunction, trace nondegeneracy, and the iterated-mates
identity, but no statement for the recorded raw rational categories. Blueprint
searches for trace pairing and restriction/comap pullback likewise found no
exact trace-unit statement. The general condensed/derived restriction-pullback
blueprint nodes do not include this rational trace normalization.

`blueprint_refs.py ancestor` could not follow the module-valued created.item
chain and reported a null ancestor. The new nodes retain the explicit ancestor
`def-weil-derived-direct-image` already recorded in the item's blueprint.from,
with the precise step and intervening nodes. No tool was modified or bypassed.

## New nodes

`lem-sf-rational-scalar-extension-right-adjoint` is the finite coefficient
trace-adjunction existence step at one scheme. Its module is
`Sheaf.Paper.RationalScalarExtensionRightAdjoint`; its conclusion is only that
the fixed scalar functor has a left adjoint. Its proof plan constructs actual
restriction, the trace-dual-basis unit and counit, rationalizes them, and
transports through the normalized finite-free completed scalar comparison.

`lem-sf-rational-restriction-pullback-unit` is the restriction/pullback
isomorphism with the literal componentwise trace-unit equation. Its module is
`Sheaf.Paper.RationalRestrictionPullbackUnit`. The plan first uses actual
restriction, checks the finite dual-basis sum on representatives against the
normalized scalar comparison, and then transports by left-adjoint uniqueness
to the supplied coefficient adjunctions. No geometric right adjoints occur.

No change records are needed: no existing signature, definition, instance,
attribute or public import was changed, and no other existing file was adapted.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalPullbackScalarRightMate": "d2c25df5292497e9fffa4e6c07e5b622215baa5c", "Sheaf.Paper.RationalRestrictionPullbackUnit": "9589c05a628edaede06e03b29c1a05568b920631", "Sheaf.Paper.RationalScalarExtensionRightAdjoint": "8403715b4c26c704cae1d715b5a65a91124112df"}, "results": {}, "time": "2026-10-28T14:13:18+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

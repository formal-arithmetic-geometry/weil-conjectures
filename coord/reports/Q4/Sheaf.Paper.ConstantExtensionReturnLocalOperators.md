## What changed

Filled three of the four original theorem holes in
`lean/Sheaf/Paper/ConstantExtensionReturnLocalOperators.lean` without changing any
signature, definition, public import or docstring.

- `WeilConjectures.SheetReturn.powerEquality`: commute the natural-number summands,
  apply `pow_add`, and use the definition of automorphism multiplication.
- `WeilConjectures.sheetReturnPointFibre_eq`: the two point-fibre constructions are
  definitionally equal, since the constant extension retains the same closure field.
- `WeilConjectures.sheetReturnStalkIso_existsUnique`: construct the isomorphism as the
  composite of the point-fibre equality, pullback of the given carrier isomorphism,
  and the inverse specified pullback compositor. Its hom is definitionally the
  required formula. Any other such isomorphism has the same hom by HEq transitivity,
  and `Iso.ext` proves uniqueness.

The remote single-file compile passed for these proofs and again after removing
unused private proof imports (30.9 seconds, exit code 0). The main theorem and its eleven-step
proof plan are unchanged; this is a partial proof delivery under the brief's
multiple-hole rule, not a decomposition.

## Proved and sorry left

Closed 3 original holes:

- `WeilConjectures.SheetReturn.powerEquality`.
- `WeilConjectures.sheetReturnPointFibre_eq`.
- `WeilConjectures.sheetReturnStalkIso_existsUnique`.

One original hole remains, unchanged:

- `WeilConjectures.constantExtensionReturnLocalOperators`, node
  `lem-zl-constant-extension-return-local-operators`. Its complete source and
  eleven-step natural-language proof remain in its docstring and DAG node.

Added zero holes and zero split statements. The module has one actual `sorry`.
All three proved declarations already belong to the item's existing node.

## No longer needed

Removed unused private imports:

- `Sheaf.Paper.IteratedReturnTransportScalarCalculus`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`.
- `Sheaf.Paper.LocalFrobeniusConjugacyClass`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.AlgebraicGeometry.ClosedPointField`.

These imports are unnecessary for the definitions and three completed proofs.
The public imports are preserved verbatim. No node or module is withdrawn:
the unchanged main theorem's remaining proof plan still needs its stated
mathematical dependencies. In particular redundant direct imports of the integral
comparison modules do not make those modules globally unnecessary. No unit route
or main-theorem dependency is pruned by this partial delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The point-fibre equality needs no scalar
localization extensionality argument in this presentation: reflexivity suffices.
The stalk uniqueness proof requires no new transport lemma or arbitrary witness;
its formula is already a composite of the existing specified isomorphisms.
There is no current rework row or item-specific return for this module.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

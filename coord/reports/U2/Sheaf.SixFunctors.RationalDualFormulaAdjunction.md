## What changed

`Sheaf.SixFunctors.RationalDualFormulaAdjunction` now proves
`WeilConjectures.RationalOperations.rationalDualFormulaAdjunction_exists` with its
original signature and normalization definition. All original public imports,
definitions and declarations are retained.

The private proof constructs the full integral adjunction from the supplied
system: integral_residue_tor makes each finite-Tor inclusion an equivalence,
and integralLeft identifies the transported compact-support functor. It chooses
the ordinary tensor presentation on c.Z using IntegralHom.models_exist.

The remaining geometric comparison is stated in the new module
`Sheaf.SixFunctors.IntegralDualFormulaComparison`. After transporting the integral
adjunction along this comparison, the item proves rational descent directly.
Functor extensionality and the supplied object/pure-map equations identify the
integral duals and pullback after rationalization. The support equality follows
from baseChange_tmul. Mathlib Adjunction.localization constructs the rational
adjunction; localization_counit_app and equality-transport identities prove the
required HEq with the localized integral counit.

New proof imports are IntegralResidueTor, IntegralHomModelsExist,
IntegralDualFormulaComparison, SemilinearScalarLocalization (with import all for
its existing proved private localization helpers), and Mathlib's
CategoryTheory.Localization.Adjunction. The lower module publicly imports
CoefDualFormulaScalarTranspose for the normalization predicate and
RationalVerdierModels for the prescribed prime-unit witnesses in its pullback.
No other existing module is changed, and no forced adaptation is required.

The two delivered modules compiled cleanly in import order: 6.9 seconds for the
integral comparison and 9.2 seconds for the item before removal of an unused
private helper. The final item, with both public definitions retained verbatim, compiled cleanly
in 13.4 seconds. Delivery preflight validates the final packet.

## Proved and sorry left

Closed the original syntactic hole in
`WeilConjectures.RationalOperations.rationalDualFormulaAdjunction_exists`
(node `lem-sf-rational-dual-formula-adjunction`). Its proof now combines the
constructed integral adjunction, the integral comparison, and the proved
rational-localization argument. There are zero sorry declarations in the item.

Added one sorry declaration:
`WeilConjectures.RationalOperations.integralDualFormulaComparison`
(node `lem-sf-integral-dual-formula-comparison`). It supplies the natural integral
comparison and the normalization after transport. Its docstring records the
source, complete argument in words, and edge cases.

Thus this is a decomposition: one original hole closed, one strictly smaller
hole added, net zero holes closed. It is not a claim that the geometric argument
or all ancestors are sorry-free. The new statement has no rational adjunction,
no localized counit equation, no coefficient system S, and no task of extending
an adjunction from finite-Tor to full integral categories. Those parts are
proved in the item, rather than repackaged as assumptions of a renamed copy.

## No longer needed

The planned proof dependency `prop-weil-pbc-rational-transport` is not needed by
this proof. The exact generic Mathlib localization-of-adjunctions theorem gives
the rational adjunction and its counit formula directly. No import of that
proposition's module is added. Its other consumers are unaffected; this is a
removal from this node's proof dependencies, not a global module withdrawal.

No original import or declaration is removed. No module is withdrawn, no source
library declaration is deleted, and the blueprint unit's route is preserved.
The original scalar-transpose node remains needed through FormulaNormalized
and the pointwise comparisons used by the new integral comparison.

`lem-pur-semilinear-scalar-localization` is used only as a generic category-theory
tool: its proved private helpers provide integer-shift linearity and the
IsLocalization instance for the existing raw scalar-localization functor. It
does not replace a geometric unit argument. No tool_uses approval is added here.

## Where the brief, the DAG or earlier work was wrong

The current queue describes an ordinary proof-route item; the stale rework row
does not describe a present missing import or build error. The current server
queue and build-error location were checked before working. The starting item
has one hole, not a zero-hole repair.

The DAG's former step 2 combines a pointwise evaluation characterization with
naturality and normalization after adjunction transport. The existing
formula_existsUnique supplies objectwise normalized isomorphisms; it does not
state the naturality or transport equation required to use them as a natural
isomorphism. The new node records exactly this integral assembly step, while the
other original proof steps are made into Lean.

The item's inherited source names a historical lem-coef-rational-operations
location. In the current latest blueprint, the natural Hom calculation and
unit/counit discussion are in
`sec-six-functors/sk-thm-sf-package/lem-coef-finite-exceptional.proof.md`; its
integral realization uses
`sec-smooth-purity/sk-lem-sp-tower/thm-coef-integral-verdier.proof.md`.
These current sources were read. The new node records that source and inherits
the parent's explicit blueprint ancestor. The ancestor tool returned no node
through created.item because that field is a module name; the parent's explicit
blueprint.from provides the inherited node chain instead.

Searches of the source library, Sheaf modules and Mathlib found the existing
pointwise comparison and generic adjunction/localization tools, but no supplied
natural integral comparison theorem with the same normalization. Logged
LeanSearch, Loogle, LeanFinder and grep searches were used; the new node records
three actual searches. The whole-blueprint search for integral dual formula
found no duplicate imported blueprint node.

Small cases checked for the new statement: empty schemes and zero objects
reduce to the same functorial tensor/adjunction identities; torsion integral
objects are retained, with no inversion or faithful-finite-reduction assumption
in its assertion. Both signed symmetries and tensor presentations remain the
supplied ones. No arbitrary witness from an unproved existence theorem is
installed as a new definition.

## New nodes

`lem-sf-integral-dual-formula-comparison`, in
`dag/nodes/sec-six-functors/lem-sf-integral-dual-formula-comparison.json`, is the
integral assembly and transport-normalization step of the original argument.
Its Lean theorem is in the new IntegralDualFormulaComparison module. Its source,
three logged Mathlib searches, inherited blueprint reference, statement
dependencies and proof plan are recorded. It is strictly below the original
single-field rational adjunction statement. No change record is needed because
only the assigned module, its proof-route fields, and this new module/node are
changed; existing public interfaces are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualFormulaComparison": "b195eee5c90763ce5380a962bd99db29f3379dc1", "Sheaf.SixFunctors.RationalDualFormulaAdjunction": "fa718e0a302c6ed7933bd5616dfabe953aed0dd0"}, "results": {"Sheaf.SixFunctors.RationalDualFormulaScalarCounit": {"hash": "d01de62cfa12860103b2a29f0307f6d1b9e1f463", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T09:47:24+0800", "transitive": 0, "version": 1}
```

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

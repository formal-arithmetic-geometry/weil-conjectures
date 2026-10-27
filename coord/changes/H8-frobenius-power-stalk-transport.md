# AlgebraicGeometry.WeilSheaf.frobeniusPowerTranslateSheafIso

## Reason

Construct the translated carrier comparison explicitly and separate its one-return
coherence square from the now-proved induction and stalk evaluation. The item statement
and all existing definitions stay unchanged. Repair the returned packet's synthetic
holes by moving the one-return hypothesis from the public section-variable command into
the private helper signatures. Explicit coefficient categories and compositor arguments
are used in both modules; the importer is compiled against the new module in the same set.

## Old

No declarations existed at `Sheaf.DeligneLaumon.FrobeniusPowerTranslateStructure`.
The item theorem `nonempty_stalk_equiv_of_equivariant_power_translate` had proof `by sorry`.

## New

New additive API in `Sheaf.DeligneLaumon.FrobeniusPowerTranslateStructure`:

- `frobeniusPowerTranslateAut`: the conjugate theta^-1 ; Fr_X^j ; theta.
- `frobeniusPowerTranslateSheafIso`: the explicit isomorphism beta^* A -> B obtained
  from the supplied `e` and the canonical inverse-pushforward comparisons.
- `frobeniusStr_powerTranslate`: its one-return compatibility square, still `by sorry`.

The exact signatures and concrete bodies are in the attached new module and its node.
No existing public declaration, definition, signature, attribute, instance or public import
is changed. The item gains proved private helpers and proof imports.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.FrobeniusPowerStalkTransport | H8 | uses the new carrier construction and one-return square; repaired helper binders |
| Sheaf.DeligneLaumon.FrobeniusPowerTranslateStructure | new | constructs the explicit comparison and states its square |

Existing direct consumers of the item retain its identical public interface. The new
module is imported privately; no target statement or existing definition changes meaning.
The only consumer of the new module is the item, and both are delivered together.
The item's existing public signature is unchanged, so its existing consumers require no edits.

## Status

landed 20261026T235906-L-1466375 2026-10-26 (merge of deliver/H8/Sheaf.DeligneLaumon.FrobeniusPowerStalkTransport)

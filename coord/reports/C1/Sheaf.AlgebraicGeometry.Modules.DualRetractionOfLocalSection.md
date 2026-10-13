## What changed

Added an explicit split-mono construction for the restricted dual map. The retraction is conjugated through the internal-Hom restriction isomorphisms and is precomposition by the given local section. The remaining categorical cancellation is isolated in `dual_retraction_key`.

## Proved and sorry left

`isSplitMono_restrict_dualMap_of_local_section` is proved from `dual_retraction_key` and `internalHom_restrict_scheme`.

`dual_retraction_key` remains as one named intermediate sorry for the reassociation and internal-Hom functoriality calculation.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the whole target hole. The final reassociation can be isolated as a strictly smaller intermediate theorem, allowing the target split-mono construction to compile.

## New nodes

`new-sbc-dual-retraction-key`, implemented by `Sheaf.AlgebraicGeometry.Modules.DualRetractionKey.dual_retraction_key`.

## Earlier second reading (a previous round; superseded)

Pending second reader.

## Second reading by C1

1. The delivered item theorem has the same signature as the repository version; only
   proof imports and proof terms changed. The new `dual_retraction_key` statement is a
   strict intermediate cancellation statement and does not alter the target.
2. Both files compile with `lcompile.py`; the only remaining `sorry` is the named
   `dual_retraction_key` theorem. No definitions contain `sorry`, and no forbidden
   declarations were introduced. Its remaining `sorry` is recorded by node
   `new-sbc-dual-retraction-key`.
3. The split-off cancellation statement is true by internal-Hom naturality and
   contravariant composition, and is strictly smaller than the target split-mono
   assertion. It is not duplicated by an existing declaration found by repository
   search.
4. The target proof follows the unit route through `internalHom_restrict_scheme`
   and the conjugated precomposition map; no proof dependency can be removed.
5. The DAG node for the new theorem records its statement, source, proof decomposition,
   Lean declaration, and C1 provenance. No existing target statement was changed.

Changed during second reading: added this review record; no Lean proof changes were
needed.

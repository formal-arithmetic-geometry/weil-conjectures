## What changed

Completed the zero-hole retirement repair listed in `coord/retire-items.tsv`.
Withdrew `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafMapExists` through
`deleted.txt` and redirected its only direct consumer,
`Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt`, to the
unchanged upstream twin. Updated the map node's Lean attachment and the
consumer node's proof description.

The consumer contains an explicit identity-on-sections presheaf isomorphism.
Its naturality follows from uniqueness of the retained exterior restrictions
and the upstream restriction formula. Sheafifying and applying naturality of
the unit proves preservation of wedges in both directions. Conjugation then
transfers the upstream map theorem to the retained exteriorSheaf construction.
All helper declarations are private and fully proved. All existing public
consumer signatures, definitions and target statements remain unchanged.

Validation: the original zero-hole module compiled; the adapted sole direct
consumer compiled cleanly in 10.5 seconds initially and 14.7 seconds after
tightening the scalar-structure comparison options. The required delivery checks also
compile and probe the delivered consumer. Search used Loogle for
`exteriorPower.map`, LeanFinder for exterior-power maps of sheaves, and source
search for both constructions and all uses of the retired module/theorem.

Change record: `coord/changes/retire-exterior-sheaf-map-exists.md`.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0.
No `sorry` remains in any delivered Lean file.
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_map_exists` is already proved
in the upstream twin and is used unchanged (node
`lem-sc-exterior-sheaf-map-exists`).
`determinant_wedgeMorphism_local_data_at` remains proved from the same wedge
and quotient-factor declarations, now using the upstream map through five
proved private comparison helpers. This delivery counts as a retirement,
not as closing a proof hole.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafMapExists`.
Removed its private import from
`Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt` and replaced
it with the upstream twin. The retired local `restriction_wedge` helper and
local proof of the map theorem are no longer needed. The map DAG node remains
needed and points at the upstream theorem. The retained ExteriorSheaf module
and its definition node remain needed for the explicit comparison and the
consumer's unchanged public statement. No other nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open hole, but the assigned queue row is
`retire`, and the original module has zero holes. The upstream theorem has a
different Lean type because it uses `exteriorPower`/`wedge` in place of
`exteriorSheaf`/`exteriorSheafSection`. Directly replacing the import does not
supply the old consumer's type. The proved comparison repairs precisely this
API difference, without changing statements or adding holes. The source-library
boundary is respected: no `WeilConjectures` file is edited.

The submission rerun exposed a slow scalar-structure comparison in the new
helper: profiling isolated 34 seconds in its upstream restriction formula.
Using the backward definitional-equality rules (already used by the original
map theorem) for the new helper declarations avoids that expensive unfolding.
No timeout limit was changed and no module was split.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

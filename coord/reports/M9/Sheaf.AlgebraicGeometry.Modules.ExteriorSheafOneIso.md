## What changed

Repair of returned head 11c4487cdd, reviewer C-11c44, using option A.
Restored lean/Sheaf/AlgebraicGeometry/Modules/ExteriorSheafOneIso.lean and the
sheaf-dag node lem-sc-smooth-proper-curve-dualizing-exterior-one, including its
original Sheaf module attachment, existing=false, exteriorSheaf statement, and
proof step using exteriorSheafRestriction_existsUnique. Removed deleted.txt and
coord/changes/M9-retire-ExteriorSheafOneIso.md from the packet. No withdrawal is
requested. The naturality proof now checks pure wedges directly with
exteriorPower.linearMap_ext rather than choosing a preimage under oneEquiv.symm.
The sole public import remains Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf.
Single-file lcompile.py compilation passed without warnings in 17.6 seconds.

Retirement decision: KEPT. Close retire:Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso
as kept: the twin restates the theorem on upstream exteriorPower, while
def-sc-sheaf-exterior-power still defines Sheaf.exteriorSheaf. The existing
coord/changes/retire-sheaf-twins-kept-20261020.tsv already records this distinction.
The delivery transport accepts Lean, node and Markdown change files, not the
maintainer's retirement inventory; this report records the requested row closure
for the maintainer at review/landing.

## Proved and sorry left

The restored theorem AlgebraicGeometry.Scheme.Modules.exteriorSheaf_one_iso has a
complete proof of Nonempty (exteriorSheaf M 1 ≅ M) for every scheme and module
sheaf. Zero original holes in the current source; zero holes closed; zero holes
added or split off; zero holes left. This is a repair of the rejected retirement,
not a new hole closure. The naturality argument uses the actual restriction
characterization in def-sc-sheaf-exterior-power, followed by sheafification and
its invertible counit.

## No longer needed

None. No module, node, declaration or import is pruned. The item and
def-sc-sheaf-exterior-power remain needed by the planned curve-dualizing
argument, even while its parent is absent or quarantined. No comparison with
upstream exteriorPower is asserted or used.

## Where the brief, the DAG or earlier work was wrong

The returned packet identified two constructions without a proved comparison.
It attached the node to a theorem on exteriorPower, although its statement,
definition dependency and parent proof use exteriorSheaf. It also incorrectly
attributed the exteriorSheaf restriction law to
PresheafOfModules.exteriorPower_map_ιMulti. Restoring the original attachment and
proof resolves each H3/E4 point: exteriorSheafRestriction_existsUnique is the
restriction law actually used, and proof_deps matches it. The parent
lem-sc-smooth-proper-curve-dualizing step 2 already has its original sheaf-dag
text and needs no edit. No upstream source or target statement is changed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

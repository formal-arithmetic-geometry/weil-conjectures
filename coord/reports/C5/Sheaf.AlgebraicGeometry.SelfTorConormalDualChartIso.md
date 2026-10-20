## What changed

Reapplied the build repair to the current archived source of
`Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso`, after the landing tools
returned delivery `ef6fad854b5` because the item changed after its old base
`e0d550965`. At repair time the live Lean path is absent, and the current
`quarantine/Sheaf/AlgebraicGeometry/SelfTorConormalDualChartIso.lean` matches
the shared archive byte for byte. The restored module preserves that source's
public declarations, definition body, imports, and existing gluing argument.
It reapplies the missing exterior-power compatibility proof to this source.

The proved private helper `exteriorSheaf_eq_exteriorPower` identifies the two
sectionwise exterior-power constructions. The section modules agree by
definition; uniqueness on pure wedges identifies their restriction maps.
Applying their common sheafification gives equality of the sheaves. Rewriting
the whole existential affine-map family before unpacking it transports the
local maps, their coordinate squares, and their overlap compatibility together.
The existing covering, gluing, and chart dualization proof then applies.
The node's first proof step records this argument.

This repair also narrows the retained delivery's transparency settings to a
local proof section after `selfTorAffineComparisonFunctor`. Thus the public
functor definition is elaborated in the original environment, and the settings
end with the proof section. The conservative delivery check requires a change
record for the attribute command:
`coord/changes/C5-selfTor-exterior-comparison-proof-transparency.md`.

The final single-file compile through `lcompile.py` passed without warnings
in 20.4 seconds, within the unchanged 60-second limit. Both proof imports are
used. No consumer adaptation is required: the downstream tool reports no live
consumers, and source search identifies the quarantined direct consumer
`Sheaf.AlgebraicGeometry.SelfTorConormalDualChart`, whose interface is preserved.

The retained searches found standard gluing APIs through Lean Finder,
`PresheafOfModules.isoMk` through Loogle, and no existing equality between the
two exterior constructions through project/Mathlib grep. Reading their
definitions gives the direct equality proof used here, with no new dependency.

## Proved and sorry left

This is a zero-hole build repair: 0 holes before, 0 holes after, 0 holes closed,
and 0 holes added. No theorem is split off. The private equality helper is
fully proved. `AlgebraicGeometry.selfTor_conormal_dual_chart_iso` retains a
complete proof from the existing named dependencies. There is no `sorry` in
the delivered module, and no other Lean module is changed.

## No longer needed

None. No import, node, or module is pruned. The argument still uses compatible
affine maps, `SheafOfModules.existsUnique_hom_of_cover`, and affine chart square
dualization. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The current item source is archived in `quarantine/`, as recorded in
`coord/rework.tsv`. It is restored, not withdrawn. The affine-map theorem now
uses upstream `exteriorPower`, while the assigned theorem uses
`exteriorSheaf`. These constructions are mathematically equal but are not
definitionally equal to Lean. The private helper supplies the required
equality for arbitrary schemes, modules, and natural degrees, including
degree zero and empty schemes, without a regularity hypothesis.

The current return requests reconciliation with the changed main-branch
source, rather than a new mathematical reduction. The repair was reconstructed
from the current archive, its proof-only settings were narrowed as described
above, and it was compiled anew. No target, statement, definition, or upstream
source file is changed.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Retired `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData` in favour
of its proved `WeilConjectures` twin (retirement row 532). Its sole direct consumer,
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`, imports the twin.
The private equality bridge for the presheaves moves verbatim into the consumer;
a proved private lemma carries that equality through sheafification. The consumer
rewrites the official hom-data theorem to its existing exteriorSheaf API.
Its public signature and public imports stay byte-identical. Updated both DAG
proof descriptions and pointed the hom-data attachment at the official theorem.

The adapted consumer compiled cleanly through lcompile.py in 7.2 seconds.
Source read: blueprint master, lem-sc-riemann-roch.md, determinant paragraph,
lines 140–147. The argument preserves that local exterior-power/gluing route.
The equalities apply to every natural degree and every open, including zero degree,
empty opens and empty schemes. No definition or target statement changes.

Change record: coord/changes/retire-exterior-sheaf-restrict-hom-data-f1.md.

## Proved and sorry left

This is a zero-hole retirement repair: 0 of 0 sorries closed, 0 added, 0 split off.
The original item, official twin and adapted consumer contain no sorry.
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_hom_data` remains proved
in the official module. The consumer proves its presheaf equality bridge and new
sheaf equality lemma, then proves `exteriorSheaf_restrict_iso` from the official
hom-data theorem. No new unproved statements remain.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData`.
Removed its private import from `ExteriorSheafRestrictIso`; replaced it with
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData`.
The hom-data node remains needed by the parent and now points at the official twin.
The presheaf-open-pullback and exterior-power definition nodes remain used by the
official proof. No mathematical node or unit proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a hole, but the current item has zero local
sorries: this assignment is the retirement repair listed in coord/retire-items.tsv.
The earlier M2 report concerns an old reduction already fully proved upstream.
The official hom-data theorem uses exteriorPower; its consumer uses exteriorSheaf.
The two constructions agree by the proved equality bridge, so no signature change
or new split-off statement is needed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

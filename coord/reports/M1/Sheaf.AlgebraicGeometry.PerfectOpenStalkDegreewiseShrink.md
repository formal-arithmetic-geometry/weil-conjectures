## What changed

Retired Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink in favor of the complete
source theorem. Reattached its node to the source declaration. Adapted the sole direct
consumer, Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift, without changing its
signature: call the canonical shrinking theorem, then set eV = cV ≪≫ cW.symm ≪≫ eW.
The final component equality follows by expanding the composed natural isomorphism.
Both node proof records describe this route. Change record:
coord/changes/retire-perfect-open-stalk-degreewise-shrink.md.

## Proved and sorry left

Zero textual holes before and after: proved 0 of 0 sorries; added 0; split off 0.
The existing source exists_affine_perfect_open_stalk_degreewise_shrink is used with
its complete proof. The adapted exists_affine_perfect_open_stalk_chainMap_lift has a
complete proof and unchanged statement. No remaining sorry declarations in the packet.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink.
Its private restriction_comp_iso, restrict_eq_of_le, and conjugate_map helpers are
superseded by the source proof's helpers. The parent removes the private Sheaf shrink
import, replacing it with the source import. It also removes its unused private import
Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation. The finite-presentation,
retract-equality and restriction-comparison nodes remain needed by the source route;
none is claimed globally pruned. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes holes, but the current assigned retirement has zero
holes (coord/queue.tsv and coord/retire-items.tsv). The old node still attached to the
Sheaf twin. Its arbitrary initial comparison cannot simply be passed to the source
version, which fixes canonical comparisons. The explicit coordinate composition in the
consumer resolves that mismatch for arbitrary eW, including nonidentity automorphisms.
Zero complexes and empty degree support add no cases: the source theorem already
handles them, and coordinate composition imposes no rank or support hypotheses.
LeanFinder found no closer shrinking lemma; Loogle located Iso.trans_hom; library search
identified the complete source theorem. No new nodes, definitions or assumptions.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

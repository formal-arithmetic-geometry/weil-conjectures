## What changed

Filled both theorem proofs in Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource without changing
any public signature or public import. The private proved helper smooth_on_range_of_etale
factors an etale map through its open image, proves the factor etale and surjective, and applies
Smooth.of_comp_of_flat_of_surjective. The global theorem glues these open images by
IsZariskiLocalAtSource.of_iSup_eq_top. The pointwise theorem restricts to the inverse-image
neighbourhood in one direction and uses the helper on W.ι ≫ h in the other.

The node proof and proof dependencies now record the Mathlib Etale.instSmooth instance instead
of the stronger fibre-dimension theorem. The unit statement and route are unchanged. Search
used msearch leanfinder, loogle and grep, together with direct source searches in both roots.
The final single-file lcompile completed cleanly in 5.6 seconds.

## Proved and sorry left

Closed 2 of 2 original holes:
- AlgebraicGeometry.smooth_iff_of_jointly_surjective_etale.
- AlgebraicGeometry.smooth_at_iff_of_etale.

Both realize lem-trf-etale-source-smoothness. No sorry remains in the item; no holes added and
no statements split off. The private helper AlgebraicGeometry.smooth_on_range_of_etale is proved.
The empty-index case needs no inhabitant of I: hcover supplies an index only after a source
point is given. Empty source opens and non-surjective individual etale maps are allowed.

## No longer needed

Removed the private import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres and the
proof dependency and obsolete tool_uses entry lem-weil-pbc-etale-smooth-zero-dimensional-fibres.
Only its smoothness consequence was needed; Mathlib Etale.instSmooth supplies that directly,
without the fibre-dimension calculation. This removes that direct edge, without asserting
that the module has no other consumers. All other declared dependencies remain used.
No source-library declaration or module was removed; no new public import was added.

## Where the brief, the DAG or earlier work was wrong

No mathematical error. The planned fibre-dimension dependency was stronger than necessary.
The general smoothness-descent theorem needed for the open-image argument is already proved
in WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth. No definition repair, consumer
adaptation, new node, or change record is needed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

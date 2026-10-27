## What changed

Proved `WeilConjectures.PurityFiniteSetting.existsUnique_generalDivisorEtaleClasses`
from `Etale.ordinary_supported_kummer_uniqueBoundary`. For every Cartier immersion,
choose its uniquely normalized Ext class and record its canonical Hom realization.
A proved private extensionality lemma shows that the Ext fields determine the whole
family, because the realization equations also determine the Hom fields.

Added the private proof import
`Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`. All original public
signatures, definitions, attributes, public imports and docstrings are retained.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.PurityFiniteSetting.existsUnique_generalDivisorEtaleClasses`.
Its proof is complete from the existing named unique-boundary theorem.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.divisor_class`
(node `lem-pur-divisor-class`). No holes were added or split off. There are no
sorry-filled definitions or private lemmas in this packet.

The compatibility proof was explored through normalized Cartier Ext addition,
ordinary Chern comparison and the local signed boundary formula. The full assembly
was not validated within the compiler's per-file limit. These experiments and their
proposed API changes are excluded from the delivery; this packet retains only the
validated existence-and-uniqueness proof.

## No longer needed

Removed unused private proof imports:

- `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns`
- `Sheaf.AlgebraicGeometry.PurityRelativeCone`
- `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`
- `Sheaf.Paper.PurityFrameIndependence`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`

No node or module is withdrawn. The full framed-line realization
package is unnecessary for the general family's existence and uniqueness: the
existing unique supported Kummer boundary theorem already gives precisely the
required normalized Ext classes. The unfinished `divisor_class` still retains its
original DAG route and dependencies.

No experimental Ext realization model, local-equation split or addition module is
included or imported by this delivery.

## Where the brief, the DAG or earlier work was wrong

The current blueprint distinguishes the positive frame class from the normalized
Cartier class with positive ordinary Chern image. The existing Lean statement uses
the latter convention and its negative local boundary; this delivery preserves it.

No statement or definition repair is claimed. Existence needs no smoothness and
follows directly from the previously stated unique-boundary theorem. The family is
chosen only from a uniqueness statement, so its recorded data are determined by the
normalization, rather than chosen from mere existence.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

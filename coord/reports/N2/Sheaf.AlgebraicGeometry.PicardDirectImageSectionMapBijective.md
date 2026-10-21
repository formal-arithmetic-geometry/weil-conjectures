## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardDirectImageSectionMapBijective.lean
byte for byte from the quarantine path in coord/rework.tsv. The archived proof
compiles unchanged against the current library in 26.8 seconds with no errors
or warnings. This is a restoration of an absent module, not a compiling no-op.

AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective retains its exact
signature, full proof, five public imports and four private proof imports.
The proof uses the stated flat-invertible base-change theorem, the canonical
single-pullback comparison, the proved source degree-zero homology bijection,
and unitHomAddEquiv. Restriction along the equal top opens is a bijection, and
Functor.map_comp with associativity recovers the fixed map's defining formula.
The proof also covers empty schemes without extra assumptions.

Updated only the existing node's Lean restoration metadata. Its statement,
attachment, proof plan, proof dependencies and unit route remain unchanged.
The parent naturality node still needs this theorem. The combined live and
quarantined import graph has one direct and fourteen transitive consumers;
no consumer requires adaptation because the interface is identical.

Change record: coord/changes/N2-picard-direct-image-section-map-bijective-restoration.md.
The prescribed delivery tool supplies the independent review.

## Proved and sorry left

The archived item contains zero sorries. The restored theorem
AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective has a complete
proof, with node lem-sc-picard-direct-image-section-map-bijective.
Holes closed: zero. Holes added: zero. Holes left in this packet: zero.
No new theorem, definition, axiom or split-off result is introduced.
This restores existing proved mathematics and claims no net hole reduction.

## No longer needed

None. All nine imports are retained and serve the theorem statement or proof:
the section-map definition, properness, flatness, local finite presentation,
invertibility, flat-invertible base change, transport to sheaf invertibility
from ProjectionFormula, evaluation from Ext, and the degree-zero homology
bijection from DerivedCategory.TStructure. No node or module is withdrawn.

The required shorter-route search found only ingredients: Lean Finder returned
pushforward-section bijectivity and scheme-map section isomorphisms; Loogle
returned unitHomEquiv and its compatibility formulas; Mathlib grep returned
bijective_pushforwardSections. None replaces the fixed derived section map's
base-change and homology comparison. The already compiled archived route uses
the needed library declarations directly and introduces no new intermediates.

## Where the brief, the DAG or earlier work was wrong

The ordinary live module path in step 1 is absent. coord/rework.tsv identifies
its exact quarantine archive and records a cluster-restore rollback. This is a
zero-hole restoration assignment, not a fresh sorry and not a withdrawal.
The old N2 return is a general upstream-sync notice, not a request to remove
the attachment or replace the archived proof. No mathematical error in the
statement, proof plan or retained implementation was found.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

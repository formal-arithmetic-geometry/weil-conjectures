## What changed

Restored lean/Sheaf/AlgebraicGeometry/AffineKoszulSectionRoof.lean from the
quarantined rework assignment as a public re-export of the complete upstream
proof in WeilConjectures.AlgebraicGeometry.AffineKoszulSectionRoof. This removes
the mixed duplicate import environment that caused the recorded sync failure.
The restored import path and theorem name remain available; the archive is
preserved and no deletion is requested. The existing node's Lean attachment
points to the upstream theorem; its mathematical statement and route stay intact.
Change record: coord/changes/affine-koszul-section-roof-upstream-restoration.md.
No upstream source or target is edited.

## Proved and sorry left

Assigned repair with zero holes before and zero after. Holes closed: none.
Holes added: none. Sorries left in the delivery: none. No split-off statements.
The existing upstream AlgebraicGeometry.Scheme.affine_koszul_section_roof is
fully proved; #print axioms reports only propext, Classical.choice, Quot.sound.
Its private chain-realization proof is likewise preserved upstream.

Validation: the restored module compiles through lcompile.py. An independent
sandbox check copied the exact archived K-flat predicate under a private fresh
name and proved the entire archived roof signature by applying the upstream
theorem. This validates the renamed predicate definitionally, including the
universe binders and restriction instances. A second sandbox check redirects
the upstream AffinePerfectTensorRoof's roof import through the restored Sheaf
module and compiles its entire consumer proof. These temporary checks are not
included as library declarations.

## No longer needed

The duplicate local section-roof declaration and private chain-realization helper
are replaced by the already proved upstream declarations. Their proof route is
not pruned: all three proof dependencies and all statement dependencies remain.
The restored module replaces its three public imports and five proof imports
with one public import of WeilConjectures.AlgebraicGeometry.AffineKoszulSectionRoof.
Removed direct imports (their required declarations remain available through
the canonical module):

- WeilConjectures.AlgebraicGeometry.PerfectComplex (public).
- Sheaf.AlgebraicGeometry.DerivedTensorAugmentation (public; upstream version used).
- Mathlib.AlgebraicGeometry.AffineScheme (public).
- WeilConjectures.AlgebraicGeometry.AffineKoszulSectionColimit (proof).
- Sheaf.Algebra.Homology.KFlatResolution (proof; upstream version used).
- Mathlib.Algebra.Homology.DerivedCategory.Fractions (proof).
- Mathlib.CategoryTheory.Limits.Types.Colimits (proof).
- WeilConjectures.AlgebraicGeometry.KoszulOpenSystem (proof).

The corresponding upstream modules remain used by the canonical proof. No mathematical node or whole module is
claimed pruned; the restored Sheaf path remains as a compatibility import.

## Where the brief, the DAG or earlier work was wrong

The item has no proof holes: its actual assignment is the quarantined import
repair in coord/rework.tsv. The upstream sync introduced a canonical copy of the
same complete proof, with IsKFlatTensor replacing the identically defined
IsAcyclicTensorKFlat. Reinstating the archived mixed imports would reproduce the
reported duplicate declaration. Re-exporting the canonical proof repairs that
collision without bypassing the parent or the unit route. The old automated
kept-twin inventory warned about transitive duplicate imports; the restoration
uses only the upstream closure and its consumer check verifies that environment.

Mathlib searches: leanfinder returned affine-limit section results, with no
roof theorem; loogle returned no exact-name match; msearch grep returned no
matches. Direct rg of the source library located the complete upstream roof
proof. The existing node and all its declared dependencies were read before
choosing this reuse route. No new mathematical statement is needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Retired Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel, the zero-hole
retirement item in coord/retire-items.tsv row 1205, in favour of its existing
proved official twin. The sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue, now imports that
twin and ExteriorSheafPowerComparison privately. A fully proved private bridge
conjugates the supplied quotient morphism, applies the official kernel theorem,
transfers annihilation with kernel.lift and kernel.lift_ι, and verifies the old
pure-wedge formula through the tensor and exterior comparison formulas. The
consumer's public imports, theorem signature and existing docstring are unchanged.

Updated new-determinant-lift-wedge-kernel to point at the official theorem with
its verbatim signature and actual proof steps. Updated new-wedge-glue-family
to record the comparison transport. The unit's determinant route is preserved.
Change record: coord/changes/U4-retire-determinant-lift-wedge-kernel.md.

Validation: lcompile.py compiled the adapted glue module (8.1 s), followed by the
unchanged DeterminantWedgeMorphismLocal (3.9 s) and DeterminantWedgeMorphism
(2.8 s), as one import-ordered set, all clean with no warnings. The import-direction
check allows the new official import. The official and legacy statements were
compared clause by clause: exactness, rank assumption, all three degrees and
rank equality, the quotient formula, annihilation and the wedge formula agree
under the canonical isomorphisms. Rank zero, degree zero, empty opens/schemes
and zero section rings need no extra assumption.

## Proved and sorry left

Original item: zero sorries. Holes closed: zero. Holes added: zero.
Sorries left in delivered Lean files: none. Split off: zero.
The existing official determinant_liftWedge_kernel_exists remains fully proved.
The consumer's private determinant_liftWedge_kernel_exists_compat and
exteriorSheafPowerIso_hom_wedge are fully proved. The consumer's public
determinant_wedgeMorphism_glue_family remains proved with exactly its old signature.
This is a completed retirement repair, not a claim of net hole reduction.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/Modules/DeterminantLiftWedgeKernel.lean
through deleted.txt. Its only direct importer has been adapted; a DAG parent scan
finds new-wedge-glue-family, whose kernel step is preserved using the official
attachment. No DAG node is deleted. The public theorem remains in the official
source library.

Remove the consumer's private import of the retired module. The duplicate's
private presheaf comparison, wedge-map bridge and factorization bridge are no
longer needed. Its separate direct proof imports of ExteriorSheafWedgeMapExists
and DeterminantWedgeQuotientFactor are absorbed by the official theorem, which
still uses both results: neither dependency node is claimed globally pruned.
The redirected node's proof no longer directly needs
lem-sc-exterior-sheaf-power-comparison or def-sc-sheaf-exterior-power; the former
is now explicitly used by the consumer transport, and the latter remains a
statement dependency. The comparison definitions are retained unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes, but this current item
has zero holes and is explicitly listed for retirement. Its copied theorem and
bridges duplicate the official theorem plus the already available canonical
comparison. The original DAG attachment names the copy and is redirected to the
proved twin. No mathematical statement is disputed or weakened.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

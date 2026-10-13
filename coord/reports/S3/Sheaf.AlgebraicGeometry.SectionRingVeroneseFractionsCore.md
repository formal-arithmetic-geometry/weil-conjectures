## What changed

Simplified the bijectivity proof in sectionRing_veronese_fraction_core to use
QuotientAddGroup.liftEquiv.bijective, constructed from the same numerator-map
surjectivity and kernel equality. Signatures, definitions, imports, and the
generator computation remain unchanged. Updated the DAG proof to record this.
The assigned repair is already complete: sectionRing_veronese_fraction_core states
bijectivity of the canonical map and its explicit value on homogeneous generators.
The canonical map descends the explicit numerator map through the relation subgroup.
The proof uses the kernel equality, numerator-map surjectivity, and numerator
cancellation exactly as its current DAG node records.

## Proved and sorry left

Holes closed by this delivery: none (0 of 0). Holes added: none.
No declaration in the item's module contains sorry. AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core compiles with
the simplified bijectivity argument. This is proof simplification, not hole closure.
The canonical-map definition contains no sorry and constructs a quotient lift.

## No longer needed

None newly pruned. The latest source already bypasses
Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula and node
lem-sc-section-ring-veronese-fractions-formula by direct quotient descent.
All current imports provide data used in the public signatures, map definition,
or its direct proof; no import is removed by this delivery.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains sorry, but the current module contains none.
The coord/repairs.txt entry refers to an old Nonempty conclusion; the current source
already includes repaired bijectivity and the generator formula with a complete proof.
The first dry run refreshed the clone and revealed an even newer direct quotient
construction. The sandbox now matches that latest source, avoiding any reversion.
The current DAG statement and proof agree with the module. This delivery simplifies
an already completed repair and claims no new hole-closure progress.

## Second reading by S3

1. Compared the delivered module with the repository version. The declaration
   signatures and definitions are byte-for-byte unchanged; only the proof body of
   `sectionRing_veronese_fraction_core` differs.
2. Compiled the module with `lcompile.py`, checked for forbidden constructs and
   `sorry`, and inspected `#print axioms`; compilation succeeds and the theorem uses
   only `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the existing DAG statement and proof dependencies against the code.
   The bijectivity and generator formula are unchanged, and no new statement or
   split-off node was added.
4. Reviewed the proof route and imports. `QuotientAddGroup.liftEquiv.bijective`
   is a shorter direct route from the recorded kernel equality and numerator-map
   surjectivity; all public imports are needed by signatures or definitions, and
   no old proof dependency is newly unused.
5. Checked the unit record route and the node metadata. The realized unit route is
   preserved and the node's `proof`, `proof_deps`, and `proof_origin` match the
   delivered proof.

Changed only the bijectivity proof to use `QuotientAddGroup.liftEquiv`; no holes
were closed or added, no modules were pruned, and no statements or definitions
were changed.

## What changed

Decomposed `diagonalOrientationReduction` in
`Sheaf.Paper.FiniteDiagonalOrientationReduction` along its existing proof plan.
Three new modules state the separate inverse-base-change, DNC, and vector-factor
coefficient squares. A fourth states the coefficient-independent global assembly
of the actual diagonal orientation. The item proves the composite square from
these four statements, using a proved private categorical composition and equality-transport lemma.
Local irreducibility attributes keep large affine-orientation definitions folded.
All original public signatures and public imports are preserved. The four new
imports are private proof imports. The existing node's proof dependencies follow
the new reduction; each new statement has its own node, source and proof in words.

## Proved and sorry left

One of the four original holes is reduced:
`WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.diagonalOrientationReduction`.
This is a decomposition, not a complete proof: four strictly smaller holes are added.
The already-proved `supportedKummerReduction` remains proved.

Three original holes remain in the item, all attached to
`lem-pur-finite-diagonal-orientation-reduction`:

- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.affineOrientationReduction`;
- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.supportedProductsReduction`;
- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.supportedProductsUnit`.

The four added holes are, in the same namespace:

- `diagonalBaseChangeReduction`, node `lem-pur-finite-diagonal-base-change-reduction`;
- `diagonalDncReduction`, node `lem-pur-finite-diagonal-dnc-reduction`;
- `diagonalVectorReduction`, node `lem-pur-finite-diagonal-vector-reduction`;
- `diagonalOrientationAssembly`, node `lem-pur-finite-diagonal-orientation-assembly`.

The packet has seven holes in total, compared with four in the original item.
The final full module set passed `lcompile.py --all`. A first combining proof
exceeded the limit; replacing geometric rewrites by the abstract equality-transport
calculation and keeping affine definitions folded resolved that compile failure.
No theorem is claimed globally axiom-free. Each remaining theorem has its recorded
source and complete natural-language proof. The assembly statement involves only
one coefficient stage; the other three isolate different geometric factors.

## No longer needed

None. No module, public import or unit route is withdrawn. The original direct
proof dependencies of the diagonal steps are now dependencies of the corresponding
new nodes, so they remain needed indirectly. The final combination uses only
functoriality, associativity and the four new statements.

## Where the brief, the DAG or earlier work was wrong

The existing diagonal assembly theorem is stated only for affine source and base,
while this item's final theorem is global. The additional assembly node records
the gluing argument required to bridge that gap. Its proof uses locality of
ordinary rank-one sheaf endomorphisms after cancelling the twist and shift, rather
than claiming arbitrary derived morphisms can be checked locally.

An extended attempt at the rank-zero unit calculation produced a typechecking
proof, but its kernel conversions exceeded the single-file limit. That experiment
is not part of this delivery; `supportedProductsUnit` is retained verbatim.

## New nodes

`lem-pur-finite-diagonal-base-change-reduction` realizes parent Step 5, just the
inverse-alpha square. Its proof is scalar compatibility of the normalized
adjunction mate followed by diagonal restriction.

`lem-pur-finite-diagonal-dnc-reduction` realizes parent Steps 6--7, just the delta
square. Its proof compares the actual coordinate and normal-frame maps and uses
coordinate-normalized uniqueness of the DNC comparison.

`lem-pur-finite-diagonal-vector-reduction` realizes parent Step 8, the existence of
the root-normalized line comparison together with just the vector-factor square.
Its proof reduces ordered integration, inverts it and restricts to the normal
zero section using the actual site-comparison counits.

`lem-pur-finite-diagonal-orientation-assembly` realizes the assembly part of parent
Step 9. It extends affine chart assembly to the global specified orientation at
one coefficient stage, without any coefficient reduction conclusion.

All four are sourced from blueprint/latest, finite-reduction-of-purity proof
Steps 3--4 and the indicated parent steps. Searches used LeanFinder, Loogle and
Mathlib grep, followed by direct library searches; no existing theorem gives
these precise global component statements. No definition or statement repair,
change record, consumer adaptation, or source-library edit is included.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Repair of returned head e8f8ba768: refresh the packet against current sheaf-dag,
restore the full adopted theorem signature in both metadata records, retain the
change record at its full repository-relative delivery path, and repeat the
server compile and delivery preflight. The already reviewed Lean proof is retained.

Completed the retirement assigned by coord/retire-items.tsv:1647. Withdraw
Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists and attach
lem-sc-determinant-short-exact-exists to the unchanged proved theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExactExists.

Adapt the only direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact:
replace its private import, move the proved private hom-wedge helper here, and
transport the adopted determinant isomorphism using exteriorSheafPowerIso.
The inverse formula follows from tensor-section naturality and both wedge
comparison identities. The public theorem signature, public imports, three
invertibility clauses, all-open arbitrary-lift formula, and uniqueness remain
unchanged. The parent DAG proof records the actual transport argument.

The adapted consumer compiled cleanly on the server after rebasing the packet.
The current consumer signature and public imports were checked verbatim against
sheaf-dag; the Lean file has no holes and satisfies the 100-column limit. Against an empty withdrawn module the
original consumer fails at line 69 with Unknown identifier
determinant_shortExact_exists, demonstrating the necessary migration.
The two further downstream consumers were compiled unchanged against the adaptation.
No source-library file changes. Change record:
coord/changes/K4-retire-determinant-short-exact-exists.md.

## Proved and sorry left

The assigned item has 0 existing sorry holes. Closed: none. Added: none.
Remaining in delivered modules: none. Split off: none.
The adapted AlgebraicGeometry.Scheme.Modules.determinant_shortExact and moved
private exteriorSheafPowerIso_hom_wedge are fully proved. The adopted
AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists is already proved
and is preserved unchanged (node lem-sc-determinant-short-exact-exists).
This is a duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists.
Its consumer's private import is replaced by the adopted module.
Its private helper moves to the consumer, where it is used in the transport.
Its direct proof imports of LocalSplittingFiniteFree, DeterminantWedgeMorphism,
DeterminantWedgeMorphismSplit and PullbackFreeGenerator are no longer needed in
legacy code; the unchanged adopted existence proof still uses all four.
ExteriorSheafPowerComparison is no longer a proof dependency of the adopted
existence node; it remains a required dependency and import of the legacy parent.
No mathematical node is removed and no lower adopted dependency is pruned.
All public statement imports of the consumer remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof obligation. Current source has
zero holes: the retirement queue explicitly assigns this duplicate for withdrawal.
The adopted API uses exteriorPower/wedge rather than exteriorSheaf/exteriorSheafSection,
so replacing the import alone does not preserve the consumer's formula; the proved
comparison isomorphisms provide the required conversion without a new theorem.
The current return says reviewer C-e8f8b passed head e8f8ba768, but landing
failed when --apply-fixes named the change record by basename. This repair
retains the full record at coord/changes/K4-retire-determinant-short-exact-exists.md,
rebases node metadata from current sheaf-dag, and restores the complete adopted
theorem signature in the item node and change record (both were truncated).
There is no item rework row. Previous B7 and R4 work is preserved.
The item node's old proof mixed this conversion with the canonical existence proof;
the delivered node separates them by recording conversion in the actual parent.

The LeanFinder query for short-exact determinant lines found ring-module determinant
and Picard-group results, not this sheaf statement. Loogle confirms Iso.trans for
transport; the msearch grep found no Mathlib determinant_shortExact_exists.
Direct rg searches found the exact proved adopted theorem and its sole legacy
consumer. The retained unit has empty realized lists; its determinant construction
route and the adopted proof's local splitting and gluing remain in use.
Zero ranks and empty opens need no nonzero assumptions or case exclusions.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

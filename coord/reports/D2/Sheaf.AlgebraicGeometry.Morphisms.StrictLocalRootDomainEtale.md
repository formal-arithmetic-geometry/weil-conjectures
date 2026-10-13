## What changed

Replaced `strict_local_root_domain_etale` with a complete proof of the unchanged
statement. The root algebra is finite; every maximal ideal is the kernel of
evaluation at the zero residue root, so it is local and its root belongs to the
maximal ideal. `IsRegularLocalRing.localization_at_prime_and_isRegularRing`
supplies regularity of H/(h) as a ring. The existing
`AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem` supplies regularity at the
root algebra's maximal ideal; `IsLocalization.atUnits` transports this back to
C and the upstream regular-local-domain instance gives IsDomain C. The existing
`root_split_away_cover_etale` proves the etale conjunct directly.

Replaced the unused public StrictLocalRootInvariants import with the public
Henselian and AdjoinRoot imports needed by the signature; all new imports used
only by the proof are plain imports. No existing signature or definition changed.
Removed the first worker's two sorry modules and their new nodes. Removed its
unchanged sandbox copy of StrictLocalRootInvariants from the delivery.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.strict_local_root_domain_etale` (one of one
original holes). Added: none. Left in the delivered module: none. Split off: none.
A scratch copy compiled with `#print axioms` shows only `propext`,
`Classical.choice`, and `Quot.sound` for both the item and
`AlgebraicGeometry.Scheme.root_split_away_cover_etale`; there is no `sorryAx`.
This is a proof, not a decomposition. The maintainer's pinned sorry ledger
remains authoritative for closure and whole-library progress figures.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants`.
Its node `lem-sbc-strict-local-root-invariants` is not a proof dependency of this
item (it was never in this item's old proof_deps). No node in the old proof_deps
was pruned: `lem-sbc-root-algebra-regular-at-root` is still used.

Discarded undelivered modules StrictLocalRootDomain and StrictLocalRootPunctureEtale,
and their nodes lem-sbc-strict-local-root-domain and
lem-sbc-strict-local-root-puncture-etale. Their proof-only imports were removed
from the item. No claim is made that any removed import's module is globally
unreachable: other targets can still need it.

## Where the brief, the DAG or earlier work was wrong

The first worker only paired two new sorry conjuncts, adding two holes to close
one. The new docstrings did not contain complete natural-language proofs and
the punctured-cover statement duplicated the existing, proved
root_split_away_cover_etale. Neither new node was self-contained in its natural
language statement. No decomposition survives this review.

The original DAG plan omitted the actual locality argument and the bridge from
regular local H/(h) to IsRegularRing (H/(h)), which the regularity-at-root theorem
requires. Both are now explicit; the bridge uses the existing
lem-weil-pbc-regular-local-localization, with no new statement.

## Second reading by D2

1. Compared every sandbox module with the repository. The only pre-existing
   modified declaration is strict_local_root_domain_etale; a byte comparison of
   its signature through `:= by` passes. StrictLocalRootInvariants was an exact
   copy and was excluded. No hypotheses, conclusions, universes, definitions,
   or data construction changed. The two new conjunct-only modules were removed.
2. Compiled the repaired file using lcompile.py, with no errors or warnings.
   Scanned for sorry, axiom, unsafe, opaque, implemented_by, extern, and skipped
   kernel checks: none occur. The scratch-copy axiom audit of the item and the
   existing puncture result gives exactly the three permitted axioms and no
   sorryAx. Evaluation maps and localization equivalences are concrete
   constructions; no arbitrary object is chosen from an unproved existence.
3. Read both proposed split statements; their conjuncts are mathematically true
   but their documents and dependency records were insufficient. Searched
   lean/Sheaf, upstream WeilConjectures, and Mathlib for punctured Kummer covers,
   root algebra locality, and regular-local localization. Found and read
   RootSplitAwayCoverEtale, RegularLocalLocalization, RootAlgebraRegularAtRoot,
   Mathlib Ideal.GoingUp and IsLocalization.atUnits; used those instead.
   No split statement or new node remains, so there is no new-statement search
   record to deliver. Checked n=1 (C is H), n>1, h in the maximal ideal,
   and that the nontrivial local ring assumptions exclude the zero ring;
   locality needs neither henselianity nor invertibility of n. Invertibility of
   n is used only for the etale conjunct. The residue-root construction uses
   positivity of n, so no n=0 case was silently assumed.
4. Read Stacks [0EYG](https://stacks.math.columbia.edu/tag/0EYG), especially the
   finite root algebra paragraph, [09EV](https://stacks.math.columbia.edu/tag/09EV),
   and [0AFS](https://stacks.math.columbia.edu/tag/0AFS). The proof follows the
   regular-local root route, and uses the already proved punctured-cover theorem.
   The unused invariants import is pruned. All old proof_deps are accounted for
   under No longer needed. Checked dag/units/sk-prop-input-spreading.json:
   this node appears in no realized slot; the regular-divisor tame root route,
   unit statement, and all unit steps are preserved. No unit record was edited.
5. Rewrote only proof, proof_deps, and proof_origin in the existing item node.
   The steps now record locality, regularity of H/(h), regularity at the root,
   transport from its maximal localization, and the existing punctured-cover
   theorem. The uses union equals proof_deps. Every cited Lean declaration was
   read and supplies the claim used at that step. No new nodes remain.

Changes by the second reader: replaced the conjunct-only decomposition with the
full proof, removed both new holes/nodes and an unchanged copied module, pruned
the unused invariants import, and repaired the existing DAG proof record and report.

The public-import pruning is recorded in
`coord/changes/StrictLocalRootDomainEtale-imports.md`. Inspected the only direct
importer StrictLocalRootTorsorProperties: it has its own public invariants import,
so rotations and fixed-algebra declarations remain visible to its 139 transitive
downstream users. An unchanged temporary copy was compiled against the repaired
item and excluded from the delivery. No consumer adaptation was necessary.

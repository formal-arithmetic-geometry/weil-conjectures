## What changed

Proved `isConstructibleEtaleSheafOfSets_of_generic_lisse` by Noetherian induction and finite partition assembly. Added auxiliary modules for the partition structure, generic stratum, reducible step, and open restriction. The generic stratum and induction assembly compile; reducible partition and open restriction remain named sorries.

## Proved and sorry left

Proved by reduction (no local sorry):
`AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_of_generic_lisse` and
`AlgebraicGeometry.Scheme.exists_etaleGenericLisseStratum`.
Both still depend on upstream open statements; the criterion also depends on the
reducible substep below. This delivery does not claim they are axiom-closed targets.

Sorries left: `AlgebraicGeometry.Scheme.nonempty_etaleLissePartition_of_reducible` (node `lem-weil-pbc-etale-lisse-partition-reducible`); `AlgebraicGeometry.Scheme.isLocallyConstantEtaleSheafOfSets_open_pullback` (node `lem-weil-pbc-etale-locally-constant-open-pullback`).

## No longer needed

Removed the following proof-only imports from the criterion module:

- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`: now used inside
  `EtaleGenericLisseStratum` and planned inside `EtaleLissePartitionReducible`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`: now planned inside
  `EtaleLocallyConstantOpenPullback`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`: now planned inside
  `EtaleLissePartitionReducible`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`: replaced by the
  constant-sheaf/localization argument in the open-restriction substep.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`: the generic-stratum proof
  uses the already proved upstream vanishing-ideal subscheme construction directly.

Every old proof dependency removed from the criterion node is accounted for:

- `lem-weil-pbc-noetherian-finite-components`: retained in the reducible substep's plan.
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`: replaced by Mathlib's
  `WellFoundedLT.induction` on closed subsets of the Noetherian space.
- `lem-weil-pbc-reduced-induced-closed-subscheme`: replaced by proved upstream
  `IdealSheafData.isReduced_subscheme_vanishingIdeal`, `range_subschemeι`, and
  the standard closed-immersion instances; the stronger wrapper theorem is unnecessary.
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`: retained in the generic
  stratum and reducible substeps.
- `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`: replaced by localization
  preserving constant sheaves in the open-restriction substep's argument.
- `lem-weil-pbc-sets-etale-inverse-image-restriction`: retained in the open-restriction plan.
- `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`: retained in the reducible plan.

`def-weil-constructible-subset` remains a direct dependency of final stratification
assembly. These are removals from this item's proof plan, not assertions that unrelated
users no longer reach those modules. No unit realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG described the full Noetherian induction only in prose and had no Lean declarations for the partition assembly or generic stratum. These are split into strict intermediate statements. The reducible and open-restriction arguments are left as separate named statements for follow-up.

## New nodes

`lem-weil-pbc-constructible-etale-lisse-partition`, `lem-weil-pbc-etale-generic-lisse-stratum`, `lem-weil-pbc-etale-lisse-partition-reducible`, and `lem-weil-pbc-etale-locally-constant-open-pullback`.

## Earlier second reading (a previous round; superseded)

The generic stratum proof was compiled and checked against its unchanged target statement. The new partition structure exactly records finite immersed lisse pieces. The two remaining named statements are strict substeps of the DAG plan and retain the stated hypotheses.

## Second reading by J2

1. **Unchanged interface: pass.** Read all five delivered modules and diffed the criterion
   against the repository version. Its only existing declaration has a byte-for-byte
   unchanged source signature; its public imports are unchanged. The added helpers are
   private and fully defined. The other four modules are new, with matching new nodes.
   No target, existing definition, or existing statement changes; no change record is needed.

2. **Lean and axioms: pass with the reported open obligations.** All five files compile
   through `lcompile.py --all`, without errors or unexpected warnings. The only two local
   sorries are exactly the two public named theorems listed above, each with source and
   a complete proof in words. No forbidden declaration or hollow definition occurs.
   A scratch module printed axioms for all four public theorems and the partition
   structure. Each theorem uses only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`; the partition structure uses only the first three. In particular the proved
   generic-stratum reduction still uses the upstream open composition comparison.

3. **Split statements: pass.** The reducible statement assumes partitions only on proper
   closed subsets and has no generic-lissity hypothesis; the open-pullback statement is
   only about local constancy and needs no finiteness or Noetherianity. Neither restates
   the criterion. Checked the empty closed subset (zero-part partition), singleton and
   nonreduced irreducible supports (the reduced induced subscheme is integral), two
   intersecting components (remove earlier components), and empty open restrictions.
   Infinite stalks are allowed in the local-constancy lemma, as required. Searched the
   library with alternate words, and ran additional LeanFinder, Loogle, and Mathlib grep
   searches through `msearch.py`; the node records now refer to searches actually run.
   `WeilConjectures.ConstructibleSheaf.Pullback` has analogous theorems, but they and
   its local-constancy class require abelian coefficients and cannot apply to `Type`.
   No existing exact set-valued result was found.

4. **Route and pruning: pass after report repair.** Read induction, disjoint partition
   assembly, reduced generic stratum construction, and final `Stratification` packaging.
   The proof combines genuine strict substeps and handles the empty base case directly.
   The generic stratum already takes the short proved upstream route for reducedness.
   Proof-only imports use plain `import`; dependencies of the two open substeps remain
   as their proof plans. Expanded `No longer needed` to name every removed original
   import and proof dependency, including where it survives transitively.
   `dag/units/sk-prop-sf-cbc.json` has empty realized statement/step lists; this auxiliary
   reduction changes none of them and keeps the chapter's finite-pushforward route.

5. **Nodes: pass after repair.** Replaced placeholder proof text and null proof origins
   in the three theorem nodes with the actual generic-stratum proof and the complete
   planned reducible/open-restriction arguments. Set dependencies to the union of uses.
   Expanded all four new node statements to be self-contained and to cite their notions.
   Recorded their exact Lean signatures, corrected the partition's docstring blueprint
   id, and linked new nodes to the nearest blueprint ancestor through the criterion.
   Existing criterion node statement and statement dependencies remain unchanged.

Changes by this reader: corrected the partition blueprint tag, new-node statements,
proof plans, dependencies, origins, Lean signature records, blueprint ancestry and
search records; made the pruning and conditional proof status explicit in this report.
The compiled Lean proof terms and the two true named open obligations are retained.

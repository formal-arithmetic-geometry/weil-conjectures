## What changed

Proved `TopCat.Sheaf.shortExact_map_pushforward_closedSubset` directly from
`TopCat.closedPushforwardAbelianStalks` and
`TopCat.shortExact_iff_stalkFunctor_map_shortExact`. On the closed subset, the three
canonical stalk isomorphisms and their naturality form a `ShortComplex.isoMk`;
`ShortComplex.shortExact_of_iso` transports short exactness of the source stalk complex.
Outside the subset, the three stalks are zero; Mathlib supplies middle exactness and
the endpoint mono/epi conditions.

Removed the draft's `stalk_shortExact_pushforward_closedSubset`, its new node
`lem-sc-closed-immersion-pushforward-exact-stalk`, and its change record. Restored the
original copyright header, module documentation and theorem docstring. Existing
statements and definitions are unchanged.

Removed three unnecessary direct public imports. The import change is recorded in
`coord/changes/closed-immersion-pushforward-exact-imports.md`; all downstream users
are listed there. The two Sheaf proof-dependency imports remain ordinary imports.

## Proved and sorry left

Closed the original hole in `TopCat.Sheaf.shortExact_map_pushforward_closedSubset`
(node `lem-sc-closed-immersion-pushforward-exact`): 1 of 1 original holes closed.
No holes added and no holes remain in any delivered module. There are zero split-off
statements. The draft's added hole in
`TopCat.Sheaf.stalk_shortExact_pushforward_closedSubset` was removed with the redundant
new declaration; it is not counted as an additional original hole proved.

The module compiles cleanly through `lcompile.py`. A scratch copy with
`#print axioms TopCat.Sheaf.shortExact_map_pushforward_closedSubset` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed direct imports:
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: unused by statements and proof.
- `Mathlib.Topology.Sheaves.Functors`: redundant through Abelian -> Skyscraper -> Functors.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: redundant through
  Abelian -> Grp.AB -> ShortComplex.Ab -> ShortExact.

Neither original proof dependency is pruned: both existing DAG nodes are used explicitly.
No project module is claimed to leave the target import closure.
The draft-only stalk intermediate node is not delivered.

## Where the brief, the DAG or earlier work was wrong

The draft left the entire stalkwise core unproved and described its redundant factorization
as a proof of the target. That was at most a decomposition, with net zero holes closed.
Its added theorem was equivalent to the original target by the stalkwise criterion.
The existing proved inputs already give every required fact. The draft also deleted
original documentation, which has been restored.

The original DAG plan is correct and matches the final proof without changes.
The relevant source is [Stacks Tag 01AX](https://stacks.math.columbia.edu/tag/01AX),
whose exactness proof invokes the stalk description
[Tag 00AE](https://stacks.math.columbia.edu/tag/00AE) and stalkwise exactness.
The local literature checkout is absent on this machine, so these primary-source
pages were checked directly.

## Second reading by K2

1. **Visible declarations: PASS.** Compared the whole delivered module with the repository
   using `diff`. Programmatically compared the existing theorem's signature, including
   all whitespace up to `:= by`: byte-identical. No definitions, hypotheses, conclusions,
   declaration visibility or targets changed. Import removals are documented in the
   change record. Restored all original documentation.
2. **Proof and axioms: PASS.** Compiled the complete module locally through `lcompile.py`
   with no errors or warnings. Scanned for forbidden declaration forms and `sorry`:
   none. A scratch axiom check reports only the three permitted axioms. There is no
   data chosen from an unproved existence theorem; the isomorphism uses the actual
   canonical stalkPushforward map and its proved invertibility.
3. **Split-off statements: PASS after repair.** Removed the draft's redundant open
   stalkwise statement and node. No new statements remain. Searched with Loogle,
   Lean Finder and grep through `msearch.py`, and searched `lean/` for alternative
   exactness routes. Mathlib provides iso transport and zero-object exactness; a similar
   private closed-embedding proof in TorsorExtensionPushforward is inaccessible as an
   API and repeats the stalk calculations already provided by our proved input.
   Checked edge cases: for Z empty only the zero-stalk branch occurs; for Z=X only
   iso transport occurs; a closed point and a zero complex require no extra hypotheses.
4. **Top-down proof, imports and unit: PASS.** The final proof opens the original hole
   and assembles the two existing proved inputs with Mathlib primitives, leaving no
   new holes. The three unused/redundant imports were removed. Both original
   `proof_deps` are used, so no old dependency is missing from No longer needed.
   Reviewed `dag/units/sk-thm-curveestimate.json` and its `realized` entries: the unit
   route is unchanged, and this proof preserves all three steps of the existing node.
5. **DAG agreement: PASS.** The original node's on-subset identification, off-subset
   vanishing and final stalkwise detection are exactly the final Lean proof. Its
   `proof`, `proof_deps` and document `proof_origin` remain accurate; no existing node
   edit is necessary. No new node or new public declaration is delivered.

Second reading changed the draft by fully proving the stalkwise core inside the original
theorem, deleting its redundant split-off declaration/node/change record, restoring
original documentation, pruning the three unnecessary direct imports and writing the
complete import-change record and this report.

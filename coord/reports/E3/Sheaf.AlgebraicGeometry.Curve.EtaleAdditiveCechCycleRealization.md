## What changed
Kept the target signature unchanged. Split the augmentation construction into two
new modules: `EtaleAdditiveCechAlphaQuasiIso` and `EtaleAdditiveCechBetaClosed`.
The target constructs the beta cycle using the cycles/kernel isomorphism, lifts
its homology class through alpha, lifts that class to a global cycle by the epi
homology projection, and applies cyclesMap. The cycles inclusion and homology
projection naturality equations complete the proof.

## Proved and sorry left
Closed `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_cycle_realization`.
Added two holes: `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_alpha_quasiIso`
(node `lem-pbc-etale-additive-cech-alpha-quasiiso`) and
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_beta_closed`
(node `lem-pbc-etale-additive-cech-beta-closed`). This is a decomposition, not a
complete proof without sorry dependencies. No other sorry is left or added. All three delivered modules compile without
errors or warnings through lcompile.py. The target proof contains no sorry.

## No longer needed
Removed the target's direct proof imports
`Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation` and
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation`. Their nodes
`lem-sc-etale-open-cech-injective-augmentation` and
`lem-sc-first-quadrant-column-augmentation` remain needed by the alpha
quasi-isomorphism step and are not globally pruned. No planned module is globally
unnecessary. The normalization node remains a statement and proof dependency;
its definitions are used directly and its public import is retained.

## Where the brief, the DAG or earlier work was wrong
The two planned augmentation components had no chain-map compatibility interface.
The new beta lemma isolates vanishing of its differential; the alpha lemma
isolates construction and quasi-isomorphism of the global augmentation. The
remaining homology-to-cycle lifting argument is now explicit Lean.

## New nodes
`lem-pbc-etale-additive-cech-alpha-quasiiso`: the global restriction chain map
and its quasi-isomorphism, in `EtaleAdditiveCechAlphaQuasiIso`.
`lem-pbc-etale-additive-cech-beta-closed`: coefficient cycles map to closed
cochains in the total complex, in `EtaleAdditiveCechBetaClosed`.
No changes to definitions, target signatures, or other modules.

## Second reading by E3
1. Compared the delivered target module and existing node with the repository.
   Verdict: the existing theorem signature is byte for byte unchanged, and no
   definition, visibility, or public import changes. The two other modules are
   new named theorems; there are no adapted modules or change records.
2. Compiled all three modules in dependency order with lcompile.py, without errors
   or warnings. An appended scratch probe printed axioms for all three theorems:
   only propext, Classical.choice, Quot.sound and sorryAx. The only direct holes
   are the two reported named theorems. No forbidden declarations or hollow
   definitions occur. Existential witnesses are used within a proposition proof;
   no definition chooses arbitrary data from an unproved existence theorem.
3. Read the alpha and beta statements against the actual normalization definitions
   and Stacks 01EQ (https://stacks.math.columbia.edu/tag/01EQ). Verdict: both are
   true, strictly partial augmentation steps, not restatements of cycle realization.
   Alpha is independent of z and n; beta needs no cover and no homology lifting.
   Checked degree zero, one open equal to top, empty covers (which force X empty),
   and empty/repeated intersections. The signs agree with Cech degree first.
   Repeated searches using different terms through leanfinder, loogle and grep,
   and searched local Lean by concept. The proved total-resolution theorem exposes
   only an abstract homology isomorphism, not the prescribed alpha map; its map
   construction is private. The augmentation-homology theorem requires affine
   intersections, absent here. Neither closes these holes in a few minutes.
4. Read the proof from the target down. Verdict: the cycles/kernel isomorphism,
   epimorphism surjectivity and the two naturality identities give a valid direct
   reduction. Imports are minimal for the statements and this proof. The two old
   augmentation proof dependencies remain under alpha, so no module is globally
   pruned. Read sk-thm-p1's realized statement and steps: this is a lower-level
   augmentation reduction, leaving the unit route and realized record unchanged.
5. Checked each node's declaration, verbatim Lean signature, source, proof plan,
   proof_deps, proof_origin, creation and blueprint records. Verdict: they agree
   with the Lean. Restored normalization as a direct parent proof dependency,
   because its explicit definitions are used in the new proof.

Changes by the second reader: corrected the parent dependency record, clarified
retained dependencies in No longer needed, and added independent concept-search
records to both new nodes. No Lean proof or signature needed repair. This remains
one upper hole closed and two lower holes added, a decomposition with ledger net -1 (closed minus added),
not a complete axiom-free proof.

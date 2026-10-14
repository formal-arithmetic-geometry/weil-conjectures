## What changed

Restored `Sheaf.Paper.ModuleCupPullbackCycleStep` from the exact Lean source in
`coord/repair-notes/Sheaf.Paper.ModuleCupPullbackCycleStep.json`. The supplied
repository and sandbox had no item source. Preserved the two returned signatures
and proofs. Made the `ModuleCupPairingExists` import proof-only.

The original collision is no longer reproducible against the current compiled
baseline. The restored module compiles; the dry-run compilation and axiom probe
complete, and preflight reaches its report checks. No forced adaptation is needed.

Change record: `coord/changes/module-cup-pullback-cycle-step.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_cycle_step` is proved from
`moduleCup_pullback_naturality` applied to the two resolution classes.
`AlgebraicGeometry.Scheme.Modules.moduleCup_pairing_exists` is proved from
`exists_moduleCupResolutionPairing`.

Holes closed against the current repository: none. Holes added: none.
The two restored declarations have complete local proofs (2 of 2); no statements
are split off. No sorry remains in the restored module and none is added elsewhere.
The axiom check of `moduleCup_pairing_exists` lists only `propext`,
`Classical.choice`, and `Quot.sound`. The check of
`moduleCup_pullback_cycle_step` additionally lists `sorryAx`: the existing
`moduleCup_pullback_resolution_maps` theorem remains open upstream. Thus this
restoration does not make the cycle-step axiom-complete. This repair
restores the returned complete proof; it does not claim an additional hole closure
against the current repository, which has no source for this item.

## No longer needed

Removed the public exposure of `Sheaf.Paper.ModuleCupPairingExists`; its proof-only
import remains necessary. No further module or node pruning is established.

## Where the brief, the DAG or earlier work was wrong

The sandbox did not contain the delivered version promised by the repair brief.
The current repository also contains neither the assigned source nor a node with
this module in its lean record. The repair record retained the full delivered
source and established the signatures to restore.

The earlier report incorrectly stopped at the missing source. The repair record
allows restoration. Its historical instance-name collision does not recur with
the current compiled dependencies. Both proofs compile without changing any
upstream module. The dry run is required to pass before this repair is handed over.

## Second reading by V4

1. **Visible declarations:** the repository file is absent (`diff` reports no
   such file), so I extracted the complete returned source from
   `coord/repair-notes/Sheaf.Paper.ModuleCupPullbackCycleStep.json` and compared
   it with the sandbox. The only difference is `public import` becoming `import`
   for `ModuleCupPairingExists`. Both theorem signatures and bodies are byte for
   byte identical. No definitions or upstream modules are changed. Verdict: the
   restoration preserves the returned interface, with the documented reduction
   in import exposure.
2. **Proof:** compiled the delivered module with `lcompile.py`, exit 0, no
   warnings. Compiled a scratch copy with `#print axioms` for both declarations.
   Pairing existence has only the three allowed axioms; cycle compatibility also
   has upstream `sorryAx`. Read `exists_moduleCupResolutionPairing` in
   `ModuleCupPairingExists` and `moduleCup_pullback_naturality` in
   `CechCupPullbackCompat`: the first is precisely the helper's conclusion;
   the second has exactly the same schemes, morphism, quasicoherence assumptions,
   degrees and cup characterizations and is specialized to `D.left.class p a`
   and `D.right.class q b`. No local sorry or forbidden declaration occurs.
   The historical instance collision does not recur. Verdict: complete local
   proofs; cycle compatibility still depends on an existing upstream hole.
3. **Split statements:** none added, so no new small-case or duplicate-statement
   obligation arises. The restored helper aliases the existing pairing-existence
   theorem, without adding a hole or constructing data by arbitrary witness
   choice. The tensor comparison in the unchanged signature comes from the
   existing, proved `module_pullback_tensor`, whose section formula fixes the
   comparison. Verdict: no split and no hollow construction.
4. **Route and pruning:** the one-line specialization is already the shortest
   library route. Read the naturality proof: it obtains compatible computing
   resolutions, lifts classes to cycles, transports the paired cycle and applies
   the two cup characterizations. It does not call this restored theorem; there
   is no mathematical circularity. The three public imports supply the cup
   predicate/resolution types, tensor comparison and cohomology pullback in the
   signature; the two plain imports supply the proofs. No further pruning is
   claimed. No unit record mentions this missing item, and no unit or its
   `realized` record is changed. Verdict: retain the restored route and imports.
5. **DAG:** searched both library roots, `dag/nodes` and `dag/units` for the module,
   declarations and docstring node id. There is no current node for this item,
   and the sandbox contains no node edits. The existing naturality node
   `lem-sc-picard-cech-cup-pullback-compat` records its computing-resolution
   argument, and `lem-sc-module-cup-pairing-exists` records the helper's actual
   dependency. Verdict: no node record contradicted or changed; the absent item
   node is a documented limitation of the restoration, not an invented node.

Second reading changed only this report: added explicit hole counts, recorded
upstream `sorryAx`, and documented these checks. The Lean proof was retained.

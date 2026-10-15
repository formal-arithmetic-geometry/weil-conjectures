## What changed

Filled the proof of `Algebra.exists_profinite_component_ring_pullback` in
`Sheaf.RingTheory.ProfiniteComponentRingPullback`. The witness is the existing,
explicitly constructed `WContractification.PullbackProfinite C T u`. Its spectrum
homeomorphism is composed with a swap of the factors to obtain precisely the subtype
in the unchanged statement. The component homeomorphism, both compatibility equations,
w-locality, closed-point assertions, localization bijections and surjectivity are proved
using the existing source construction and its topological pullback lemmas.

The stronger `IsIndPrincipalZariski` assertion uses the planned existing local-ring
criterion; ordinary `IndEtale` uses the source `IndZariski` instance. Added the proof-only
import `WeilConjectures.RingTheory.ProEtale.WContractible`. Removed the four unused direct
imports listed below, including the unused public `Mathlib.AlgebraicGeometry.Scheme`.
No existing declaration signature, visibility, definition or target statement changed.
Updated only the item's node fields `proof`, `proof_deps`, and `proof_origin`.

## Proved and sorry left

Closed one existing hole: `Algebra.exists_profinite_component_ring_pullback`.
Added zero holes. No `sorry` remains in the delivered module. No statements were split
off, no modules or declarations were added, and this is not a decomposition.

The resulting theorem still depends on the existing open theorem
`Algebra.isIndPrincipalZariski_of_bijective_localRingHom`, node
`lem-weil-pbc-local-rings-ind-zariski`, in
`Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso`. That dependency is not delivered or
changed here. Thus this delivery closes the item's local hole, not its entire axiom
closure. The exact axiom check gives `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`; the last is inherited from that existing criterion. Separate axiom checks of
the construction, spectrum homeomorphism, pullback theorem, ind-Zariski instance,
component/closed-point results and ind-etale implication give only the three allowed
axioms. The ring data are constructed as a colimit, never chosen from an open existence
statement.

## No longer needed

Removed direct imports:

- `Mathlib.AlgebraicGeometry.Scheme`: no scheme object occurs in the statement or proof;
  this was an unused public import.
- `Sheaf.RingTheory.ClosedComponentSpectrumRestriction`: the existing source construction
  already realizes the graph restriction. This module has no other direct importer in
  the library and is pruned from the targets' closure by removing this edge.
- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`: no direct use remains.
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`: no separate direct import
  is needed; its closed tools are supplied through the construction import.

The last two source modules remain transitive dependencies of the source construction;
they are not claimed as pruned modules. Likewise removing the redundant direct Scheme
import does not remove its transitive reachability.

Every removed old `proof_deps` entry is listed here:

- `def-weil-affine-spectrum`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-closed-component-spectrum-restriction`
- `lem-weil-pbc-locally-constant-prime-spectrum`
- `lem-weil-pbc-qcqs-scheme-spectral`
- `lem-weil-pbc-quasicompact-components-clopen-intersection`
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`

These standalone proof steps are replaced by already proved source constructions and
tools, without any new holes. The four remaining proof dependencies are exactly the
union of the node's step `uses`. No node or removed dependency realizes a unit statement
or step in any `dag/units/*` `realized` record; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old DAG expanded the graph construction and its topology and localization
arguments even though the source library already constructs this ring and proves the
needed properties. The original worker report also incorrectly said no imports had
been removed and omitted two removed proof dependencies; this report records the full
pruning accurately. Its claim that the theorem was fully proved is qualified above:
the stronger principal ind-Zariski criterion remains an existing open dependency.
There is no disputed statement or mathematical change. The import-only change record is
`coord/changes/ProfiniteComponentRingPullback-imports.md`; the dry run required it for
removing an unused public import. All Scheme declarations remain publicly available
through the retained public imports, as documented there.

## Second reading by D4

1. Compared the delivered Lean file and node with their repository versions. Restored
   the accidental indentation change in the final conclusion line; the existing
   theorem signature is now byte for byte identical through `:=`. All hypotheses,
   universes, existential witnesses, the actual structure-map equations, stronger
   principal ind-Zariski clause and every conclusion are preserved. The node's
   statement, statement dependencies and Lean record are unchanged. Verdict: pass.
2. Compiled the delivered module through `lcompile.py` without errors or warnings.
   Inspected every proof branch and the source construction. There are no `sorry`,
   forbidden declarations, hollow definitions or unproved choices in the delivery.
   Checked `#print axioms` in a scratch copy and isolated the existing open criterion
   as described above. Verdict: pass, with the pre-existing open dependency recorded.
3. There are no split-off statements or new declarations to validate or search for.
   Checked the construction on the empty profinite space, the zero ring (where a map
   to its empty component space forces the source empty), singleton component choices,
   and repeated components under noninjective maps. No hidden nonemptiness or
   surjectivity assumption is used; surjectivity is assumed only in the final clause.
   Verdict: pass.
4. Searched the library and read the existing `PullbackProfinite`, connected-component,
   closed-point and ind-Zariski tools. The proof takes the available closed source
   construction, then the planned open criterion only for the stronger principal
   presentation. Removed the unused public Scheme import; the other public imports
   supply notions appearing in the statement, and both proof imports supply used
   declarations. Completed the pruning list and checked all unit `realized` records.
   Verdict: pass.
5. Read the original and delivered node against the Lean proof. Rewrote the proof
   steps to follow their actual order, name the factor swap and both compatibility
   computations, distinguish ordinary from principal ind-Zariski, and identify the
   sole existing open dependency. Corrected source locations and retained precisely
   the four used dependency nodes. The proof origin and dependency union now agree
   with the code; no new nodes are needed. Verdict: pass.

Second-reading changes: restored the signature's original whitespace; removed one
unused public import; corrected the node's proof description and source citations;
expanded the report's pruning, local-hole accounting and axiom evidence; added the
required import-only change record with all 30 downstream modules and their holders. The compiled
mathematical proof itself required no repair.

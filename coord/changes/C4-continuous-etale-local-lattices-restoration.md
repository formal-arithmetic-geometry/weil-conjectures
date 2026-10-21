# continuousLisse_etale_lattice

## Reason

Restore the module assigned by coord/rework.tsv after its cluster-restore quarantine.
The precise archived source compiles against the current library, including the
restored ContinuousLatticeFiniteCoproduct interface. The repair restores the missing
public theorem and its complete proof at the original path; no mathematical interface
or definition is redesigned.

## Old

The live path lean/Sheaf/Paper/ContinuousEtaleLocalLattices.lean is absent.
The original module is preserved at
quarantine/Sheaf/Paper/ContinuousEtaleLocalLattices.lean, and its existing DAG node
lem-weil-pbc-continuous-etale-local-lattice still carries its full Lean attachment.

## New

Restore lean/Sheaf/Paper/ContinuousEtaleLocalLattices.lean verbatim from that archive:
continuousLisse_etale_lattice and all three proved private helpers. Both public imports,
all proof imports, the public signature, and the complete finite-cover proof are
identical to the archive. Update only the existing node's proof_origin note to record
restoration and validation. No target statement or definition changes.

## Users

A source scan finds no live Lean consumer. The quarantined consumer below uses the
public theorem to obtain the etale surjection, its qcqs hypotheses, the integral module,
its explicit free cover and its rationalization isomorphism. All of these retain their
exact archived types. The downstream DAG dependency remains needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousEtaleLocalLattices | C4 (assigned rework) | Restore the missing complete module. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | quarantined; not edited | Original theorem call and destructuring remain valid; no adaptation. |

The complete quarantined consumer has other missing imports; their restoration is
outside this repair. No forced adaptation is included.

## Status

landed 20261021T021909-L-2790584 2026-10-21 (merge of deliver/C4/Sheaf.Paper.ContinuousEtaleLocalLattices)

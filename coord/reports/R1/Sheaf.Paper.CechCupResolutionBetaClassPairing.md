## What changed

Restored Sheaf.Paper.CechCupResolutionBetaClassPairing and its node from the historical
repair diff because both are absent from the checked-out library. The original public
theorem signature and two public imports are preserved. Replaced its former proof-only
import of Sheaf.Paper.CechCupSignedAxisPairing by
Sheaf.Paper.CupCechTotalCochainPairing.

The private helpers prove the natural-number indexed tensor homology pairing by two
quotient descents, explicitly handle incoming boundaries in degree zero, compose with
the existing total cochain morphism, and transport both axis formulas by homology
naturality. The generic construction adapts the library's proved integer-indexed
HomologicalComplex.tensor_homology_pairing; that theorem cannot be applied directly
because the index type differs. The upper assembly, recovered from S2's previous proof,
lifts beta classes along quasi-isomorphic alpha maps, forms a product cycle using
Leibniz, and applies IsModuleCupProduct. No data is chosen from an unproved existence
theorem in a definition; the existential cochain map is eliminated only in a proof.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing is proved from
named existing statements with its recovered signature unchanged (node
lem-sc-cech-cup-resolution-beta-class-pairing). All private helpers, including
betaPairing_signed_axis_pairing and the full tensor homology descent, are proved.
No sorry remains in the delivered module; no holes are added or split off.

The imported existing exists_cupCech_total_cochain_map remains a hole in the unchanged
library and is the actual next construction obligation. This is a proof from that
existing construction, not a claim that the entire import closure is free of sorry.
Since the assigned module is absent from the current source base, this restoration
does not close a textual hole in that base; it restores and proves the assigned theorem.

## No longer needed

Removed the recovered proof-only import Sheaf.Paper.CechCupSignedAxisPairing. Its node
lem-sc-cech-cup-signed-axis-pairing is not needed by this proof: the cochain pairing and
proved private descent supply the two homology axis formulas. This removes the signed-axis
sorry from this module's dependency route, without changing that independently held module.

Sheaf.Algebra.Homology.TensorHomologyPairing is not imported because its integer-indexed
result needs the natural-number adaptation proved here. Both public imports are required
by the unchanged signature. No other existing module is claimed to become unreachable.
The cube unit's statement and realized proof steps are unchanged; its cup comparison
route is retained.

## Where the brief, the DAG or earlier work was wrong

The brief says the assigned file and node exist with a sorry, but neither exists in the
initial checkout. The complete previous interface and upper proof are recorded in
coord/repair-notes/Sheaf.Paper.CechCupResolutionBetaClassPairing.json and were recovered
from there. The old delivery failed on a duplicate generated instance in a batch import.
The repaired assigned module compiles in 23.7 seconds. A separate module importing
both CechCupSignedAxisPairing and the restored CechCupResolutionBetaClassPairing
compiles in 1.4 seconds and prints the axioms of both public theorems. Each uses
only the three standard axioms and sorryAx from named existing holes; neither
import fails. The delivery dry run also runs the maintainer's declaration probe.

The unrelated direct-import conflict is still reproducible: a scratch module that
explicitly imports GlobalTensorPullbackMonoidalNormalization followed by
ModuleCupNaiveDerivedCompatibility fails on the duplicate generated CommRing
instance before importing either Cech module. This delivery does not claim to
repair that independent pair. Their anonymous local-instance declarations need
unique names in a separately authorized repair; neither module is changed here.

Return-point dispositions:
1. The assigned module and its axiom probe now compile; its original signature
   and both public imports are retained.
2. CechCupSignedAxisPairing is neither restored nor adapted in this delivery.
   Its existing source and interface remain intact, and the assigned proof has
   no dependency on it. The two Cech modules can also be imported together.
3. No existing importer needs adaptation: a source search finds no importer of
   the absent assigned module. The historical self-importer attributions do not
   identify an additional failing consumer. No foreign module is edited.

The first dry run fetched a newer base containing Sheaf.Paper.CechCupSignedAxisPairing.
Changing its proof was correctly refused as an unforced adaptation. The final delivery
changes only the assigned module and its node: the proved support is private inside it.

Edge cases include p=0 or q=0 (explicitly proved), arbitrary commutative coefficient
rings (the sign is an integer unit), empty index sets, and zero inputs. No cover or
quasicoherence hypotheses are added. The two coefficient cup cochain definitions in the
existing cochain pairing and in the assigned statement are definitionally equal.

## New nodes

lem-sc-cech-cup-resolution-beta-class-pairing restores the absent assigned node with its
original statement and signature. Its proof dependencies now use
lem-sc-cup-cech-total-cochain-pairing, and the remaining homology and comparison glue is
proved in the assigned module. There are no new lower statements or holes. The record is
coord/changes/cech-cup-beta-pairing-restoration-R1.md.

## Second reading by R1

1. Interface: PASS. The assigned source and node are absent from the read-only checkout.
   Independently recovered the historical module from the repair record and ran diff.
   The sole public theorem signature is byte-for-byte identical, including every
   hypothesis and conclusion; both public imports and its docstring are preserved.
   Only private proved helpers and the proof-only import differ. No definition or
   foreign module is delivered; the restoration has its change record.
2. Proof: PASS. Independently compiled the delivered module in 20.9 seconds without
   errors or warnings. Compiled a fresh scratch copy with #print axioms for all twelve
   theorems in 21.2 seconds. The ten helpers preceding or supporting the axis assembly
   use only propext, Classical.choice and Quot.sound. The signed-axis helper and public
   theorem additionally use sorryAx from existing imported obligations. No delivered
   declaration contains sorry, forbidden axioms, unsafe code or hollow data. Existential
   cochain maps and cycle lifts are eliminated within proofs, not chosen as data in
   definitions.
3. Split statements: PASS (none). No new public lower statement or hole is introduced.
   Read all private helper statements and their proofs. The zero-degree cases explicitly
   prove the incoming maps zero; positive-degree boundary witnesses use n-1 legitimately;
   the right-boundary sign is a unit and is cancelled. Arbitrary commutative rings,
   zero inputs and empty families do not require any added assumptions.
4. Route and pruning: PASS. Independently searched lean/ and Mathlib via grep,
   LeanFinder and Loogle using tensor/homology/descent queries. No shorter applicable
   natural-number tensor pairing was found: the existing tensor_homology_pairing is
   indexed by integers; its bilinear helper is private. Mathlib's descHomology and
   homology naturality are already used. The removed old proof dependency is exactly
   lem-sc-cech-cup-signed-axis-pairing, fully listed above; its proof-only import is
   replaced by the cochain pairing actually used. Both public imports supply signature
   notions. Read sk-prop-av-cube.json: its realized statement and step lists are empty,
   and this delivery changes neither the unit nor its general cube theorem route.
5. Nodes: PASS. The restored node's statement and recorded Lean signature agree with
   the historical statement and current code. Its three proof steps describe tensor
   descent, alpha lifting and the characterized cup calculation; proof_deps is the
   union of their uses, and proof_origin records the actual route. The historical
   blueprint.from.via also named lem-sc-cech-cup-resolution-total-pairing, which is
   absent from the checkout; the restoration omits that withdrawn intermediary while
   retaining its three existing lineage links. This is provenance cleanup below the
   unit, not a change to a unit statement or realized proof step.

Changes by the second reader: added this independent review and clarified the withdrawn
historical lineage link. No Lean proof repair was necessary. The proposed restoration of
that link was dropped after checking that its node no longer exists. Holes added: none;
public restored declarations proved: cupCechResolution_beta_class_pairing (one of one).
The absent baseline contains no textual hole to close, so its textual net is zero;
relative to the historical assigned route, one existing signed-axis hole is pruned.

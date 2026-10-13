## What changed

Prepared a reduction of `exists_cupCechResolutionComparison` in
`Sheaf.Paper.CechCupResolutionComparisonExists`. The pairing construction reuses the
proved private construction from `ModuleCupPairingExists`, retaining the flasque
terms. It proves restriction, Leibniz and augmentation pairing, equips all three
resolutions with computing injective comparisons, and applies a single-resolution
comparison lemma three times. Added proof-only imports of ModuleCupGodementPairing,
ModuleCupFlasqueAcyclicity, the source acyclic-resolution criterion, and
CechFlasqueResolutionComparison. No existing signature or definition was changed.

The complete flasque pairing construction was compiled in isolation using lcompile.py
(scratchpad/FlasquePairing.lean, exit 0). The actual two-module set cannot yet be
compiled: the required baseline module CechCupResolutionComparisonData has no .olean
in the published library, locally or on the server. It remained absent across
several automatic two-minute refreshes. No dependency was copied or recreated to
work around this failure. This report records a candidate reduction, not a verified
delivery; the dry run is required before it can be marked READY.

## Proved and sorry left

Candidate upper hole closed: AlgebraicGeometry.Scheme.Modules.exists_cupCechResolutionComparison
(lem-sc-cech-cup-resolution-comparison-exists). No sorry remains in that module's text.
The pairing construction is checked in isolation; full-module verification is blocked.

Hole added: AlgebraicGeometry.Scheme.Modules.cupCechFlasqueResolutionComparison
(lem-sc-cech-flasque-resolution-comparison), in the new module
Sheaf.Paper.CechFlasqueResolutionComparison. This proves only comparison data for a
given individual termwise flasque resolution; it does not construct a resolution or
supply a pairing. It is strictly a part of the original proof. One upper hole is
replaced by one lower hole: a decomposition, with candidate net zero holes.

## No longer needed

None. The sole original public import, CechCupResolutionComparisonData, remains
needed by the unchanged statement. All three original construction dependencies
remain used. ModuleCupPairingExists cannot be used as a black box because its public
existence theorem does not retain termwise flasqueness; it was not an original import
or proof dependency, so this is not counted as pruning. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

Tool/baseline failure: CechCupResolutionComparisonData is in the read-only sources
and named as the item's public dependency, but lcompile.py reports its object file
missing from the published compiled library. A read-only check confirms that the
server's published build also lacks it. The project contract requires waiting for
the next green global build rather than recreating this declaration. This prevents
checking the assembled proof and running the required successful dry run.

The proposed single-resolution lemma was checked on degree zero, the zero sheaf,
and empty covers. Empty covers require the empty scheme by the covering equality;
sheaf gluing then gives zero sections and the same construction applies. Positive
degree uses flasque Cech acyclicity and finite diagonals, not affine or quasi-coherent
hypotheses. Searches found no existing theorem with this full given-resolution
comparison-data interface.

## New nodes

lem-sc-cech-cup-resolution-comparison-exists: the target proof node is updated for K1 ownership.
lem-sc-cech-cup-resolution-comparison-data (def-sc-cech-cup-resolution-comparison-data): restored public comparison-data definitions.
lem-sc-cech-flasque-resolution-comparison: the comparison step for one supplied
termwise flasque computing resolution. Its statement has no pairing or existential
choice of resolution; its source and complete natural-language argument are in the
new module's docstring. No change record is needed because all existing signatures
and definitions are unchanged.

## Earlier second reading (a previous round; superseded)

The restored comparison-data source was recovered unchanged from the prior reviewed
N3 delivery and compiled together with the target. The target proof and the
single-resolution comparison split compile successfully in the sandbox.

## Earlier second reading (a previous round; superseded)

The restored comparison-data source was recovered unchanged from the prior reviewed
N3 delivery and compiled together with the target. The target proof and the
single-resolution comparison split compile successfully in the sandbox.

Change record: coord/changes/cech-comparison-data.md.

## Second reading by K1

1. I compared the delivered modules with the repository tree and checked every
   existing declaration used by the proof. The target module and the two
   comparison modules are new on this checkout; the restored comparison-data
   module is byte-for-byte the reviewed source recorded by the change record.
   No unrelated declaration or target statement was altered.

2. I compiled `CechCupResolutionComparisonExists.lean` with lcompile.py (exit
   0), and also compiled the sandbox module set. The only remaining `sorry` is
   the named split theorem
   `AlgebraicGeometry.Scheme.Modules.cupCechFlasqueResolutionComparison`.
   There are no axioms, unsafe declarations, or hollow definitions. The split
   theorem has its source, proof description, and DAG node.

3. The split statement is a genuine reduction: it takes one supplied
   termwise-flasque computing resolution and returns only its comparison data;
   it does not restate the pairing existence theorem or choose a resolution.
   Its hypotheses and conclusion are exactly those used three times by the
   target proof. Searches recorded above found no existing declaration with
   this interface. Edge cases (degree zero, zero sheaf, and empty covers) were
   checked in the proof analysis.

4. The target proof follows the unit route: the Godement pairing supplies all
   three complexes and their flasque witnesses, the local construction proves
   restriction, Leibniz, and augmentation pairing, and the split comparison
   theorem is applied separately to the three resolutions. The comparison-data
   definitions remain public because they are part of the target interface.
   No proof dependency was removed; no unused import was found.

5. The DAG records for the target, comparison-data definitions, and split
   theorem agree with the Lean declarations, including statements, proof
   dependencies, source, unit, and blueprint references. The target hole is
   closed and one strictly simpler lower hole remains, so this delivery is a
   decomposition with net zero holes.

I changed only this report section after the initial review: it documents the
five checks required for the second reading and the successful local compile.

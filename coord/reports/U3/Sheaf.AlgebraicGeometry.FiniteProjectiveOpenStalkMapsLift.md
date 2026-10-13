## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_projective_open_stalk_maps_lift`
in `Sheaf.AlgebraicGeometry.FiniteProjectiveOpenStalkMapsLift`, without changing
its statement or visibility. Added the proof-only import
`Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift`. Its existing uniform local
lifting theorem supplies a common family of natural stalk comparisons. Choose
the given finite-free retractions, lift the projected stalk maps, intersect the
finitely many neighbourhoods with T, and precompose the lifts with the source
inclusions. Naturality and the splitting identities prove the stalk formula.
Updated the node's proof, proof dependencies and proof origin to this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_finite_projective_open_stalk_maps_lift`
(node `lem-sc-finite-projective-open-stalk-maps-lift`).
No sorry remains in the delivered module. No holes or modules were added.
The proof uses the existing named theorem
`AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts`
(node `lem-sc-open-stalk-free-map-local-lift`), which currently has sorry in its
own module; it is an existing dependency, not a new hole in this delivery.
The finite-family assembly and retract descent are fully proved here.

## No longer needed

No existing imports were removed: both public imports are needed by the
unchanged signature. The old direct planned proof dependencies
`lem-weil-pbc-stalk-internal-hom-finite-presentation`
(`Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`) and
`def-pc-perfect-complex` (`Sheaf.AlgebraicGeometry.PerfectComplex`) are not needed
by this proof and are not imported. The latter's retraction condition is already
an explicit hypothesis; no perfect complex is constructed or used. The former
is replaced by the existing finite-free open-site local lifting interface.
This is pruning of this node's direct dependencies, not a claim that either
module is unreachable from every other target. The shared local lifting theorem
retains the finite-generator argument and restriction-stalk comparison below it.
The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned internal-Hom comparison has a ringed-space finite-presentation
interface and is unnecessary here: the existing open-site finite-free lifting
lemma gives exactly the shared comparisons and lifts on every smaller open
needed for the finite intersection. No statement defect was found.
The first local compile could not find that landed lemma's object file; the
worker waited for the compiled cache rather than duplicating the declaration.

## Second reading by U3

1. Compared the delivered module with the repository by diff and checked the
   theorem signature byte for byte, including binders, hypotheses, conclusion
   and visibility: identical. Only the proof, its explanatory docstring and one
   plain proof-only import changed. No definitions or public imports changed;
   no interface change record is needed.
2. Compiled the module with lcompile.py (6.2 seconds, no errors or warnings),
   and compiled a scratch copy with #print axioms. The theorem uses only
   propext, Classical.choice, Quot.sound and sorryAx, the last from the existing
   open-stalk interfaces, including exists_open_stalk_free_map_local_lifts.
   The delivered module has no sorry, axiom, unsafe, opaque, implemented_by,
   extern or skipped kernel check. The choices occur inside an existential
   theorem proof; no definition chooses data from an unproved existence theorem.
3. No new statements, modules or split-off holes were added. Read the existing
   finite-free lifting theorem's full interface and proof docstring: it provides
   one common natural comparison before quantifying over sources, targets and
   maps, and lifts on every smaller neighbourhood. It is strictly the
   finite-free single-map input needed here. Empty I gives Z=T and a vacuous
   conclusion; zero rank is covered by that input. The finite intersection
   genuinely uses the supplied finiteness of I. There is no hidden assumption
   that the targets are finite or that the retractions are isomorphisms.
4. Read the proof from its conclusion backwards and searched the open-site and
   finite-source lifting modules with rg. The proved ringed-space local lifting
   and finite-locally-free restriction results have different source/stalk
   interfaces and do not directly replace the common open-site comparison.
   The present short route correctly combines the existing finite-free input
   with finite intersection, naturality and the given splitting identity.
   Both public imports serve the signature; the new lifting import is plain.
   The report names both discarded old proof dependencies. The unit
   sk-prop-av-cube has empty realized statement/step lists; neither the unit
   statement nor its steps nor its realization record is changed or bypassed.
5. Compared the node JSON with the repository: exactly proof, proof_deps and
   proof_origin changed. Read each new step against the Lean proof; the uses
   and proof-dependency union agree. Its statement, source, Lean signature,
   statement dependencies, chapter and unit are untouched. No new node fields
   or change records are required.

Verdict: pass. Second reading added this audit section only; no repair to the
Lean proof or DAG was necessary. One original named hole is closed, zero holes
are added, and the result still depends on existing unproved lower interfaces;
this is not a claim of an axiom-free final target proof.

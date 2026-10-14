## What changed

Restored `Sheaf.Paper.CechCupResolutionTotalPairing` with its original theorem
signature, replacing the absent `CechCupSignedAxisPairing` dependency with the tracked
`CupCechTotalCochainPairing` theorem and the new proved `NatCochainPairingDescent` module.
The total theorem identifies all six comparison chain maps from their component
fields, and combines homology descent, cycle-class naturality and the two cochain
axis formulas. Its three private cycle helpers are proved.

The general descent lemma adapts the existing proved integer tensor-homology pairing
to natural degrees, explicitly treating zero-degree boundaries. It then composes with
homologyMap and identifies the output cycle by injectivity of the cycle inclusion.
Both modules compile without warnings, individually within 60 seconds (6.2 and
19.3 seconds in the final local set compile). No upstream instances are changed.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing` is proved with its
original signature (node `lem-sc-cech-cup-resolution-total-pairing`). This restores
one proof removed by the rollback.

`AlgebraicGeometry.Scheme.Modules.natCochain_pairing_descent` is proved (new node
`lem-sc-nat-cochain-pairing-descent`). Its private helpers `descend_bilinear`,
`tensor_cycles_lift` and `nat_tensor_homology_pairing` are proved as well.
No sorry remains in either delivered module; no hole is added or split off.
The existing total cochain morphism existence dependency retains its own named hole
`AlgebraicGeometry.Scheme.Modules.exists_cupCech_total_cochain_map`; it is unchanged
and is not a new hole of this delivery.

## No longer needed

Removed the untracked `Sheaf.Paper.CechCupSignedAxisPairing` import and node dependency
`lem-sc-cech-cup-signed-axis-pairing`. The compiled artifact alone had incorrectly
made the earlier single-file compile appear successful.

The previously restored `Sheaf.Paper.CechCupResolutionBetaClassPairing` module,
`cupCechResolution_beta_class_pairing` declaration and their proof dependency are
unnecessary for the total theorem. Neither module nor declaration is delivered here.
No tracked source importer of either absent module exists in the baseline.
The tracked canonical total-cochain construction and its alpha/beta axis calculation
are retained. The blueprint unit has no realized nodes bypassed by this route.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily coupled the total pairing to beta-class sheaf
cup compatibility, introducing the reported importer failures. This repair does not
restore or modify that companion: it proves both total axes directly at cochain level
and then descends to homology. Thus both beta-class attribution points and the total
importer point are addressed without modifying unrelated instance modules.

The sandbox's replacement signed-axis import had no tracked source, despite existing
compiled artifacts. The required dry run caught this; the repair now uses only tracked
or newly delivered source modules. A mere successful compile against cached artifacts
was insufficient. No existing public signature, visibility or target definition is
changed, and no forced adaptations are needed.

## New nodes

`lem-sc-cech-cup-resolution-total-pairing` restores the rolled-back total theorem
with the original signature. The baseline has no node file, so the delivery tools
treat its historical record as a new node. Its proof dependencies now record the
tracked total cochain pairing and proved general descent step, rather than the
absent signed-axis theorem.

`lem-sc-nat-cochain-pairing-descent`, module
`Sheaf.Algebra.Homology.NatCochainPairingDescent`: a proved general theorem descending
an arbitrary tensor total cochain morphism to bilinear homology in nonnegative degrees.
It is strictly the homological descent step; it contains no Cech, resolution or axis
compatibility assertions. Its proof follows Stacks 068G and the signed tensor formula
of 07MB, using the existing library integer proof as its implementation model.

Change record: `coord/changes/CechCupResolutionTotalPairing-restored.md`.

## Second reading by M2

1. Interface: PASS. Compared both delivered paths with the repository: both modules
   and both node files are absent after rollback, so no existing baseline declaration
   is edited. Both public theorem signatures are byte-for-byte identical to their
   node's `lean.statement`; the restoration and absent baseline are explicitly recorded
   in `CechCupResolutionTotalPairing-restored.md`. No target or existing definition is
   changed. The only definition delivered is the private `map_cycle`, constructed
   directly from cyclesMap and the cycles isomorphisms, without witness selection.
2. Proof: PASS. Read all proofs, including the two boundary arguments and cycle
   transport helpers. Both files compile without warnings (6.1 and 18.7 seconds).
   No delivered theorem contains sorry, and no forbidden declaration mechanism occurs.
   Scratch-copy axiom checks confirm the general descent theorem uses only the three
   permitted axioms; the total theorem additionally uses sorryAx from its unchanged
   open dependencies. It is a proved reduction, not a completed axiom-free target.
   The total-map witness is eliminated inside a proof of an existential theorem;
   no data definition chooses an arbitrary witness from an unproved existence theorem.
3. New statements: PASS. No statement is split off with sorry. The new descent theorem
   is precisely the general homology step, without Cech or resolution assumptions,
   and is fully proved. Checked p=0, q=0, p=q=0, zero complexes and the zero ring:
   degree-zero incoming differentials vanish, positive-degree primitives lie in degree
   p+q-1, and the second-variable sign is a unit even over the zero ring. Independent
   msearch queries used descHomology, bilinear cycle-module descent and liftCycles /
   homology-projection naturality (Loogle, LeanFinder, grep), and rg found the upstream
   integer-indexed tensor_homology_pairing. That theorem does not accept natural-indexed
   complexes; the present argument uses Mathlib's descHomology directly twice.
4. Route and pruning: PASS. Read exists_cupCech_total_cochain_pairing and its tracked
   morphism-existence dependency. The total theorem applies its two axis equations,
   componentwise alpha/beta identifications, and proved descent, with no detour through
   sheaf-cup beta compatibility. Both proof-only imports are plain imports. All public
   imports supply signature notation, objects, or the natural-degree tensor-sign
   instance required to form the total tensor complex. The report names both absent
   companions and their unnecessary dependencies. sk-prop-av-cube has empty realized
   statement/step lists; no realized node is bypassed or altered.
5. DAG: PASS. The total node's proof and proof_deps name the cochain pairing, descent
   and comparison data actually used. The descent node records its cycle inclusion,
   boundary-vanishing, two quotient descents and naturality argument. Its lean record
   matches its public theorem exactly; source, creation, origin, searches, chapter and
   unit fields are present. Neither new node moves the target hole into a restatement.

Second reading changed only this report: added the explicit five-point review and
clarified the inherited sorryAx limitation. No Lean proof or signature needed repair.

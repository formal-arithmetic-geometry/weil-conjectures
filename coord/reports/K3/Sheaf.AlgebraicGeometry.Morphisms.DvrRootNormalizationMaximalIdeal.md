## What changed

The original signature of `AlgebraicGeometry.Scheme.dvr_root_normalization_maximalIdeal`
is unchanged. Its proof now decomposes the generic torsor into Galois field components,
uses a component-wise first-order root calculation, and completes the ideal argument in Lean.
The new modules are `Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents` and
`Sheaf.AlgebraicGeometry.Morphisms.DvrGaloisComponentsRootCotangent`.
Their imports are private proof imports in the original module. No existing public import changed.
Mathlib Noetherianity, Nakayama, localization and locality prove the assembly.
The original statement's unused `let N` remains verbatim; its unused-variable linter is
suppressed only for that declaration so the unchanged statement compiles without warnings.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.dvr_root_normalization_maximalIdeal`
(node `lem-sbc-dvr-root-normalization-maximal-ideal`). There is no sorry in its proof.
Added two named holes:

- `AlgebraicGeometry.Scheme.field_torsor_galois_components`
  (`lem-sbc-field-torsor-galois-components`).
- `AlgebraicGeometry.Scheme.dvr_galois_components_root_cotangent`
  (`lem-sbc-dvr-galois-components-root-cotangent`).

This is a decomposition, not a proof free of sorry: one hole closed, two added, net -1.
The first remaining statement is purely over fields, with no root or normalization.
The second works for an arbitrary finite family of Galois fields, without torsor data
or finite normalization, and concludes only spanning modulo the maximal ideal square.
The finite-generation/Nakayama step, localization identification and reverse ideal
inclusion are fully proved. The maximal ideal's finite generation is indispensable
for the Nakayama step and is obtained from the original finite-normalization hypothesis.

## No longer needed

Removed the original module's direct proof import of
`Sheaf.FieldTheory.EtaleFieldGaloisClassification`. Its node
`lem-exc-etale-field-galois-classification` remains needed in the field-component proof plan,
and its module remains imported by that new helper; this is rerouting, not pruning.
No mathematical node or module was pruned. No unused original public import was removed.
The two new helpers replace the original uncited geometric steps with explicit Lean inputs.

## Where the brief, the DAG or earlier work was wrong

The original node had only the finite-field classification among its proof dependencies;
it did not state its uniformizer-root/Abhyankar calculation as a Lean input. Classification
alone does not give a decomposition of a scheme torsor into Galois field factors with
compatible structural maps, either. The two new statements isolate those missing inputs.
`RootNormalizationCotangentRoot` is unsuitable as a proof dependency here: it imports
`RootNormalizationRootNotSquare`, which imports the current item, creating a cycle.
The existing generic-chart field model also has different hypotheses and is not the
field-only decomposition stated here. The unit's trait/tame route is kept; its realized
statement and step nodes have not been bypassed. No statement correction is made.

The sources read were Stacks Tags 03SF, 03QR, 09EV, 09EB, 0BRM, 09E7 and 0307,
and the recorded classification and integral-closure interfaces. Edge cases checked: n=1, trivial G, disconnected
torsors, residue characteristic zero, positive characteristic prime to n, and the
empty family in the general component theorem. Degrees dividing n force tameness;
without invertibility this reasoning would fail. A zero-length family has no
normalization point. The new fields are existential witnesses in a theorem only;
no data is defined by choosing witnesses of a sorry theorem.

## New nodes

`lem-sbc-field-torsor-galois-components`: isolates the finite-field/Galois-set torsor
argument from all DVR geometry. Each orbit has normal stabilizer equal to the kernel
of the commuting right-translation action, so its field is Galois of degree dividing |G|.
The isomorphism is over Spec K, not just an abstract scheme isomorphism.

`lem-sbc-dvr-galois-components-root-cotangent`: isolates the root-index/tame calculation
for arbitrary finite Galois field families. Its first-order conclusion is strictly
weaker than maximal ideal generation; it does not assume the normalization finite.
Three search kinds are recorded for each node: LeanSearch was unavailable, LeanFinder
and Loogle found arithmetic/local APIs, and source grep found no matching theorem.
The full DAG and blueprint were searched; no exact field-family statement was found.
No change records or forced adaptations are needed.

## Second reading by K3

1. Compared the delivered `DvrRootNormalizationMaximalIdeal` module with the repository
version. The target signature is byte-for-byte unchanged; only proof imports, proof text,
and the linter suppression for the pre-existing unused `N` binding differ.
Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`. The target has no `sorry`,
and the only remaining holes are the two named split-off theorems, each with a matching DAG
node and source/docstring proof. No forbidden declarations or hollow definitions occur.
Verdict: pass.
3. Checked the split-off statements against their edge cases and the stated torsor/root
hypotheses. They are strictly weaker intermediate claims than the target and introduce no
arbitrary data through definitions. Searches recorded in `searches.jsonl` found no existing
library duplicate. Verdict: pass.
4. Reviewed the proof route and imports. The proof uses the two new component lemmas,
Noetherianity, Nakayama, and localization; the former direct classification import is
rerouted through the field-components helper. The unit's realized route remains intact and
the report's pruning section records that no mathematical node was removed. Verdict: pass.
5. Checked all three DAG nodes against the Lean declarations, including `proof_deps`,
`proof_origin`, module paths, and split status. Verdict: pass.

Changed during second reading: no mathematical statements or proof steps; added this audit
section only.

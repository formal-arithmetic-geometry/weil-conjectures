## What changed

Repaired the landing refusal for duplicate statements in
`Sheaf.AlgebraicGeometry.SectionRingChartDenominatorGenerator`.
Removed all five duplicate private declarations: `nonvanishing_iso`,
`nonvanishing_tensor`, `sectionRing_mul_component`, `nonvanishing_power`, and
`nonvanishing_of_local_smul`. Replaced the direct proof import of
`Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` with
`import all Sheaf.AlgebraicGeometry.SectionRingProjPreimageForward`.
The denominator proof now uses that module's existing private `nonvanishing_power`
and `nonvanishing_of_local_smul`, without rewriting either proof. Its other three
helpers are needed only inside the imported positive-power proof.

The overlap proof and both public theorem signatures are unchanged. No existing
module is adapted, no visibility is changed, and no change record is needed.
Updated the new denominator node's proof, dependencies and origin to record reuse.
The prior second reading described the superseded duplicate-helper version and
has been removed so the second reader can review this repair independently.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_sheaf_map`
(node `lem-sc-section-ring-quotient-chart-overlap-sheaf-map`).

The new theorem
`AlgebraicGeometry.Scheme.Modules.sectionRing_chart_denominator_generator`
(node `lem-sc-section-ring-chart-denominator-generator`) is also proved.
No sorry remains in either delivered module; no holes are added or split off.
Both modules compile without warnings using lcompile.py in import order.
The dry run runs the delivery axiom probe on both modules.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` from the new denominator
module; it remains a transitive dependency of SectionRingProjPreimageForward.
Removed the five duplicate private helper declarations listed above.
The denominator node no longer directly uses `def-sc-invertible-section-ring`
or `lem-sc-nonvanishing-iff-generates-at` for its positive-power step; these are
provided transitively by `lem-sc-ample-proj-canonical-map-preimage-forward`.
The original overlap node also removes direct proof dependencies
`def-sc-invertible-section-ring` and
`lem-weil-pbc-nonvanishing-section-trivializes`: the former remains a statement
dependency and public import, while the latter is used through the new denominator
node. Neither module is pruned from the import closure. No existing library module
or unit-level step is pruned. All original public statement imports remain necessary. SectionRingProjPreimageReverse is not needed;
the forward module alone supplies both helpers the denominator proof calls.

## Where the brief, the DAG or earlier work was wrong

The returned delivery and its second reading incorrectly concluded that existing
private helpers could not be imported. `import all` gives access to them without
changing their visibility; the library's SectionRingQuotientChartOverlapPointwise
already uses exactly this mechanism. The five duplicate statements identified by
the landing tool are now absent. The repair imports and uses existing proofs,
rather than renaming duplicates or altering their binders.
No mathematical statement or target signature changes. The zero exponent retains
the tensor-unit generator proof; positive exponents retain the nonvanishing
trivialization and its unique-quotient argument. The curve-estimate unit's route
is unchanged.

## New nodes

`lem-sc-section-ring-chart-denominator-generator` remains the only new node.
It is a proved strict part of the chart-overlap argument: generator bijectivity
for a single denominator on one inverse chart. It introduces no sorry.
Its proof dependencies now explicitly record the existing forward-preimage node
whose private lemmas are reused. No additional node or change record is added
by this repair.

## Second reading by K1

1. PASS: compared the delivered overlap module with the repository using diff and
   extracted its full theorem signature. The existing signature is byte-for-byte
   identical. The only new public declaration is the denominator theorem in its
   own new module; no definition, visibility, target, or existing statement changes.
   No change record or forced adaptation is required.
2. PASS: compiled both delivered files in import order with lcompile.py, without
   errors or warnings. Scratch copies with #print axioms show exactly propext,
   Classical.choice and Quot.sound for both public theorems, with no sorryAx.
   The source scan found no sorry, axiom, unsafe, opaque, implemented_by or extern.
   There are no new definitions or arbitrary choices of data from existence claims.
3. PASS: no statements are split off with sorry. The new proved denominator theorem
   is strictly a part of the argument, establishing a generator on one inverse chart,
   rather than restating overlap equality. Checked n=0 (tensor unit), n>0 (positive
   power invariance), empty opens, zero denominators (empty inverse chart under the
   fraction assumptions), and schemes with nilpotents. Cancellation is by a free
   generator and never assumes reducedness. Read both reused private lemmas in
   SectionRingProjPreimageForward and the unique-quotient theorem. Independent
   leanfinder search for a nowhere-vanishing invertible-sheaf generator, loogle
   search for nonvanishing, and rg searches through section-ring modules and the
   upstream FreeGenerator module found infrastructure, not a duplicate of the new
   ambient-image denominator statement. The existing transfer power-generator lemma
   assumes generation already; it does not supply the required denominator argument.
4. PASS: the proof reduces to cancellation of fractions, affine extensionality,
   the positive homogeneous chart cover and morphism locality. Existing proved
   positive-power/local-scalar lemmas are reused with import all; the duplicate
   helper statements from the returned version are absent. New imports are plain
   proof imports; the public imports supply the signatures. Checked the old
   proof_deps and the curve-estimate unit's realized record: no unit statement,
   step, or route is bypassed. No module is pruned from the closure.
5. PASS: both node lean.statement fields match their Lean signatures exactly.
   The existing node changes only proof, proof_deps and proof_origin. Its steps
   match denominator generation, fraction cancellation, affine extensionality,
   local equality and restriction transport. The new node has the required source,
   searches, creation, blueprint, chapter, unit and Lean records, and records reuse
   of the forward-preimage private proofs. Each proof_deps list is the union of
   its step uses.

Second reading changed only this report: completed No longer needed with the two
removed direct dependencies of the original overlap node and recorded this audit.
The mathematical proof and node records required no repair. One original hole is
closed; zero holes are added; zero statements are left split off with sorry.

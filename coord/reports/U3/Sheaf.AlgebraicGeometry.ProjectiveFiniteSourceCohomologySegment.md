## What changed

Proved the body of
`AlgebraicGeometry.Scheme.Modules.exists_projective_finite_source_cohomology_segment`
in `Sheaf.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment`, preserving its
signature and all public imports. Added only proof imports of
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`,
`WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`,
and
`Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation`.

The private, proved helper `pushforward_cohomology_linearEquiv` upgrades the existing
additive affine-pushforward cohomology comparison to a linear equivalence over the
arbitrary base's global sections, by scalar naturality. A local heartbeat increase is
needed for its comparison of underlying Ext functors; compilation remains within the
single-file time limit. The main proof constructs the short exact kernel sequence, constructs the two
linear maps, and proves exactness after transport through that equivalence.

Added one new module with a strictly narrower presentation theorem: it supplies an
actual sheaf epimorphism onto the closed pushforward with coherent kernel and finite source cohomology. It does
not supply a cohomology segment, a connecting map, any comparison to Y, or finiteness
of the original coherent sheaf's cohomology. The remaining combination is proved in
Lean, using the existing long exact sequence API. No definitions or existing
statements changed; no forced adaptations.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_projective_finite_source_cohomology_segment`
(node `lem-pc-p2-projective-finite-source-cohomology-segment`). No sorry remains in
that module, and its private helper is fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_projective_finite_cohomology_presentation`
(node `lem-pc-u3-projective-finite-cohomology-presentation`), in the new module
`Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation`.
Its whole proof is `by sorry`; its docstring and node give the full construction
and source. This delivery is a decomposition (one hole closed, one added), not a
net reduction in holes. The arbitrary Noetherian-ring twist-source construction is
left for the next worker. Existing imported lemmas may have transitive sorries;
none was added to them by this delivery.

The decomposition handles q=0, higher q, the empty coordinate type (empty scheme),
and a singleton coordinate type (Spec of the base ring). It never assumes the
next cohomology group finite. No arbitrary witness is made into a definition:
existence is eliminated only inside a theorem proof, and K is the constructed
categorical kernel of the supplied sheaf epimorphism.

## No longer needed

No modules are globally pruned and no public imports were removed. The old direct
proof dependencies `lem-pc-projective-space-twist-quotient`,
`lem-pc-projective-space-twist-cohomology`, and `pqf-def-cohomology` are no longer
used directly by the segment proof. The twist quotient and twist calculation move to the presentation node's
proof dependencies; both remain needed there. `pqf-def-cohomology` remains a
statement dependency, including of the new node. Its module
`Sheaf.Paper.PQFCohomology` is not imported for this proof: the existing Ext-based
H API supplies the required exactness directly. The original item's direct proof
uses the Mathlib boundary exactness node instead. This is not claimed as a globally
pruned module because other users and statement dependencies still reach it.

## Where the brief, the DAG or earlier work was wrong

The first dry run found an import cycle through the upstream
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` module and the
proper-cohomology finiteness route back to this item. Its import was removed.
The new presentation theorem consequently also contains the coherent
closed-pushforward step, which cannot be imported from that upstream module
without circularity. The base-linear affine-pushforward comparison and the
cohomology exactness assembly remain fully proved here.

The original planned proof dependencies were not actually imported by the assigned
module; only statement imports were present. The recorded closed-immersion
cohomology declaration
`nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom` assumes a base field.
Its additive predecessor works without that assumption and suffices after the
proved scalar-naturality upgrade. Similarly the twist-cohomology declarations
recorded in `Cohomology.Serre` and its geometric Cech-complex comparison require a
field. They cannot directly prove finite twist cohomology over an arbitrary
Noetherian ring. The new presentation theorem isolates precisely this affine-base
transport and arbitrary-ring gap, keeping the source's twist route.

LeanSearch returned Internal Server Error; this is recorded as unavailable, not
as an unsuccessful mathematical search. LeanFinder, Loogle, and Mathlib grep ran
and supplied no exact projective finite-cohomology presentation.

Checked Stacks Tags 01YS, 01Y6, and 01XT directly. Tag 01XT is Lemma 30.8.1;
01XS is the section tag, not the lemma. The new node uses the correct lemma tag.
The second dry run flagged adding `Limits` to a public section's `open` command.
The original `open CategoryTheory` command was restored and kernel names were
qualified inside the proof, preserving the existing command interface.
The existing unit record has no realized statement or step nodes, and the
blueprint ancestor tool returns None for this generated item's name chain; the
new node retains the parent's explicitly recorded ancestor `lem-pc-coherent-hi`
and extends its via chain. No unit or chapter route is changed.

## New nodes

`lem-pc-u3-projective-finite-cohomology-presentation` states the sheaf presentation
portion of Stacks 01YS, with the finite cohomology of its source from 01XT.
It includes coherence of closed pushforward as the first geometric step.
Its module contains exactly one public theorem and no definitions. The natural
language proof explicitly treats empty and singleton coordinate types and
identifies the required scalar action. The node retains the existing twist
quotient and twist calculation dependencies. No change record is required:
existing signatures, definitions, visibility, and public imports are unchanged.

## Second reading by U3

1. Interface: PASS. Read the full diff against the repository module. The existing
   theorem signature and docstring, public imports, universe, namespace and open
   commands are byte-for-byte unchanged. Only three plain proof imports, one
   private proved helper, and the theorem proof were added. No definitions or
   existing public statements changed, and no change record or adaptation is needed.
2. Proof: PASS as a decomposition. Compiled both modules with lcompile.py in import
   order (5.6 and 37.6 seconds), without warnings. Scanned for forbidden declarations
   and attributes: none. The sole delivered sorry is the named presentation theorem.
   Scratch copies with #print axioms show only propext, Classical.choice, Quot.sound
   for the helper, and those plus sorryAx for the segment and presentation. The
   scalar naturality proof uses the additive comparison without a field assumption;
   the exactness proof uses the actual kernel short exact sequence and transports
   both maps through inverse linear equivalences. All chosen witnesses stay inside
   theorem proofs; no arbitrary existence witness becomes definition data.
3. Split statement: PASS. The presentation supplies just the geometric epimorphism,
   coherent kernel and finite source cohomology, not the target's exact segment.
   Its complete docstring construction follows Stacks 01YS, 01Y6 and 01XT, which
   I read directly. Checked q=0 and positive degrees, zero F, empty coordinates,
   singleton coordinates, and the zero base ring: the construction remains valid.
   For a singleton all twists are trivial and positive cohomology vanishes; for
   empty coordinates all modules are zero. Independent LeanFinder search for a
   quotient by sums of line bundles with finite cohomology, Loogle search for
   Module.Finite with Epi, and Mathlib AlgebraicGeometry grep found no replacement.
   Repository search found the ring-level twist quotient, but the cohomology
   comparison/calculation API is field-specialized and the general projective
   finiteness theorem imports this item, so it cannot close this hole without a
   cycle. Closing the presentation requires the substantial arbitrary-ring twist
   calculation, not a short missing tactic.
4. Route and pruning: PASS after report correction. All three added plain imports
   serve the proof; the public imports serve the existing statement. The exact
   sequence uses the upstream Ext cohomology API directly. The twist quotient and
   twist cohomology route remain in the new presentation node. The unit record
   sk-thm-picard-coherence has empty realized statement/step arrays; no realized
   unit step is bypassed or changed. The old direct proof dependencies not used
   directly are now explicitly listed under No longer needed; none is globally
   pruned, and pqf-def-cohomology remains a statement dependency.
5. Nodes: PASS after metadata correction. Read both node files and their sources,
   dependencies, proof steps and origin against the Lean proof. The parent records
   presentation, affine comparison (the additive predecessor in the recorded
   affine-comparison module), and boundary exactness; the new node preserves the
   twist route and has the required creation, source, search and blueprint fields.
   Replaced its compressed lean.statement with the exact multiline Lean signature.

Second reading changed only report pruning precision and the new node's verbatim
Lean statement record; no Lean proof, declaration signature, or import changed.
This closes one of the item's one holes and adds one narrower hole: net zero,
reported as a decomposition rather than a completed finiteness proof.

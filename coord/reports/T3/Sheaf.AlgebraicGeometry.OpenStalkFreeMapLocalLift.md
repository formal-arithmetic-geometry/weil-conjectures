## What changed

Proved the unchanged declaration
`AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts` from two strictly
smaller statements: existence of a finite-free lift on one neighbourhood, and transport
of arbitrary open-site stalk comparisons through further restriction. The private proved
`restriction_lift_stalk` lemma performs the naturality and inverse-cancellation calculation
in arbitrary categories. The lift on W is the restriction of the map on V conjugated by
the comparison of iterated with direct slice restriction.

Added proof-only imports of OpenStalkFreeMapOneLift and OpenStalkRestrictionTransport.
Both new modules contain one named theorem. No existing signature, definition, visibility,
or public import changed. No forced adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts`
(node lem-sc-open-stalk-free-map-local-lift), 1 of 1 original holes. No sorry remains in the item.
Added:
- `AlgebraicGeometry.Scheme.exists_open_stalk_free_map_one_lift`
  (node lem-sc-open-stalk-free-map-one-lift), one hole in OpenStalkFreeMapOneLift.
- `AlgebraicGeometry.Scheme.exists_openStalk_restriction_transport`
  (node lem-sc-open-stalk-restriction-transport), one hole in OpenStalkRestrictionTransport.

Both new holes are public named theorems with complete natural-language proofs and source
citations; each proof is exactly `:= by sorry`. This is a decomposition: one original hole
closed, two lower holes added, net minus one hole closed in the targets' import closure.
It is not a sorry-free proof. The one-open lemma has no uniform comparison family or
further-restriction clause. The transport lemma has no finite-free source, prescribed map,
or local lift. The uniform lifting conclusion follows by a proved combination of these two
parts, rather than one application of a restated target. Data is selected only within theorem
proofs, not in new definitions. All delivered declarations are checked by the delivery axiom
probe; sorryAx is expected for the two lower holes and the theorem using them.

## No longer needed

No original imports were removed: both public imports are required by the unchanged signature.
The old proof dependencies no longer directly used by the item are:
- `new-module-restriction-stalk-components`
  (Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents);
- `def-sc-open-module-stalk-functor` (Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor),
  which remains a required statement import;
- `lem-weil-pbc-finite-free-local-stalk-map-lift`
  (Sheaf.AlgebraicGeometry.FiniteFreeLocalStalkMapLift);
- `def-weil-pbc-module-finite-type-presentation`.

The lower nodes retain the relevant dependencies in their plans. No module is claimed globally
unreachable or globally pruned. The first worker's proof-only import of
FiniteProjectiveOpenStalkMapsLift has been removed because it creates a cycle: that theorem
now imports and applies this item.

## Where the brief, the DAG or earlier work was wrong

The old plan hid slice-site and scalar transport work. The first worker used the singleton
case of FiniteProjectiveOpenStalkMapsLift, which now depends on this item. Local compilation
against older compiled artifacts accepted that proof, but the delivery cycle check rejected
it. The second reader replaced this circular route with a strictly smaller, source-backed
single-neighbourhood lifting statement. Existing FiniteFreeLocalStalkMapLift supplies the
ringed-space germ-level construction used in its plan; a slice/open equivalence and stalk-ring
transport still need formalizing. Existing FiniteLocallyFreeStalkHomLift is also germ-level,
not a matching slice/ambient-scalar interface. Neither is restated here without the necessary
transport work, and the downstream finite-projective theorem is not imported.

Existence of arbitrary comparison isomorphisms alone gives no coherence with comparisons
chosen in advance. OpenStalkRestrictionTransport handles this by explicitly extending the
coordinate automorphism using open pushforward, its invertible counit, naturality at the
unit, and the adjunction triangle identity. Existing OpenModuleStalkRestrictionComparison
states comparison existence but not this extension law. Sources read:
https://stacks.math.columbia.edu/tag/01CP,
https://stacks.math.columbia.edu/tag/00A0,
https://stacks.math.columbia.edu/tag/0096.

## New nodes

`lem-sc-open-stalk-free-map-one-lift`, in
`dag/nodes/sec-abelian-varieties/lem-sc-open-stalk-free-map-one-lift.json`, states lifting
on just one neighbourhood with a comparison chosen with the lift. It removes the target's
uniform coordinates and further-restriction requirements. Its proof is finite basis-germ
lifting (Tag 01CP) transported from the open subscheme to the slice site.

`lem-sc-open-stalk-restriction-transport`, in
`dag/nodes/sec-abelian-varieties/lem-sc-open-stalk-restriction-transport.json`, states
comparison transport only, independently of sources, ranks, maps and local existence.
Its proof uses canonical germ comparisons (Tag 00A0) and the open-pushforward adjunction
(Tag 0096). No change record is needed because existing interfaces are unchanged.

## Second reading by T3

1. Compared every delivered existing module with the repository version. The existing theorem's
   signature is byte-for-byte unchanged, and all public imports and definitions are unchanged.
   Only proof-only imports, a private proved helper, elaboration options, and the proof differ.
   There are no adaptations to another group's files. Verdict: pass after cycle repair.
2. Compiled the delivered modules in import order using lcompile.py. The item has no sorry;
   the two added modules each have exactly the named theorem listed above, with proof exactly
   `:= by sorry`. No axiom, unsafe, opaque, extern, implemented_by, or holed definition occurs.
   The proof constructs g by restriction and conjugation, with all equalities kernel-checked.
   Axiom probes allow only the three standard axioms plus sorryAx from still-open statements.
   Scratch `#print axioms` checks passed: restriction_lift_stalk uses only propext,
   Classical.choice and Quot.sound; the main theorem and both split theorems use those
   plus sorryAx, with no other axiom.
   Verdict: valid conditional proof / decomposition, not an unconditional completed proof.
3. Read the two split statements and their complete docstring proofs. Tested m=0, V=U, W=V,
   arbitrary N, and zero modules; x in W excludes an empty neighbourhood. Rank zero requires
   no representatives. The arbitrary-comparison extension follows from naturality and the
   invertible counit; no equality with canonical comparisons is silently assumed. Repeated
   Mathlib searches with Loogle (`"stalk", "lift"`, no hits), LeanFinder (eight affine Tilde
   localization hits), and grep, and read FiniteFreeLocalStalkMapLift and
   FiniteLocallyFreeStalkHomLift. No independent exact interface was found. The two parts
   are strictly simpler than the uniform target, with neither restating its conclusion.
   For transport, searched `"counit", "iso"` (twelve equivalence infrastructure hits)
   and inspected restrictAdjunction with its IsIso counit instance; no exact law was found.
   LeanSearch was attempted separately for the one-open lemma but returned Internal Server
   Error; this unavailability is recorded, with the successful other search kinds retained.
   Verdict: true, source-backed, needed lower statements; the interface transport remains open.
4. Reviewed the top-down reduction and imports. The generic cancellation calculation is short
   and correct. All imports in the item are needed by either signature or proof. The report
   lists every old proof dependency not used directly, including the stalk-functor node that
   remains a statement import. Read dag/units/sk-prop-av-cube.json: its realized statement
   and step lists are empty, and no unit route is changed. Verdict: pass; no global pruning.
5. Compared node proof steps, proof_deps unions, proof_origin, and Lean declaration records.
   The item now follows the actual one-open lifting and transport reduction. Both new nodes
   include source, self-contained statements, exact Lean signatures, search records, creation
   and blueprint ancestry data. Verdict: pass after updating the circular planned step.

Changed during second reading: removed the circular finite-projective import/application;
added OpenStalkFreeMapOneLift and its node; updated the item's proof and DAG route, and
rewrote the report to account honestly for one hole closed and two holes added. Retained the
correct generic transport proof and the restriction-coordinate lemma. No existing interface
was changed.

Validation: the complete three-module set compiled without warnings, and the delivery
axiom probes passed. The first repaired dry run found only the missing LeanSearch metadata
for the one-open node; this was repaired by an actual search attempt and its unavailable
service record.

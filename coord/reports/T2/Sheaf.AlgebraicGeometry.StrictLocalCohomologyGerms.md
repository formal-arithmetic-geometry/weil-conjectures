## What changed

Completed the zero-hole retirement assigned by coord/retire-items.tsv row 797.
Withdrawn Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms and redirected its canonical
DAG attachment to WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms.
The adopted free sheaf, generator evaluation, derived Hom comparison, cohomology
presheaf, homology germ map and neighbourhood functor now provide the six common
constructions; their duplicate definitions are removed.

The only retained constructions are the source isomorphism and source legs whose target
is on strictHenselizationScheme. They now have explicit smallModel_ names in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms. They preserve their
old restriction, homology comparison and legs. The adopted source comparison has its
target on strictLocalization and is deliberately also available from the new module.
The derived-restriction proof explicitly imports its existing localized-germ rewrite
lemma as a private proof dependency, so the delivered compile order includes it. The continuity presentation likewise
imports its injective-sections proof dependency explicitly and uses the adopted geometry
existence theorem directly; the former small-model existence wrapper is an exact alias.
Eight live consumers are migrated atomically: four direct public-import changes,
and the seven consumers mentioning small-model source isomorphisms or legs. One consumer
needs only the import change. All adapted modules were unclaimed in the shared claim
records when prepared; no held module or adopted-source file was edited.

Seven parent-node clarifications explicitly cite the small model; each has a complete
statement_change/citer record. No mathematical conclusion or hypothesis changes.
Change record: coord/changes/T2-retire-strict-local-cohomology-germs.md.

A temporary Lean probe reconstructed the complete old eight-definition interface in a
separate namespace and proved each old/new equality by rfl. It compiled successfully,
including the exact equality of the two small-model maps. A focused final probe also
compiled after the irreducible attribute was added, proving both model-specific
isomorphism and source-leg equalities by explicit unfolding and rfl. The probes are scratch work,
outside the delivered Lean files. This checks the map preservation used by every consumer,
rather than merely checking their types. Negative degrees, zero complexes, arbitrary
schemes and universes keep precisely the original binders and constructions.

## Proved and sorry left

The assigned item starts with 0 sorry bodies. Holes closed: 0. Holes added: 0.
No declaration in any delivered Lean module contains sorry. No proof obligation is split
off. This is a definition retirement, not a claimed numerical proof reduction.
The two model-specific constructions and all consumer proofs remain complete.
The source-isomorphism forward-map equation and the defining source-leg equation
(smallModel_strictLocalCohomologySourceIso_hom and
smallModel_strictLocalCohomologySourceLegs_app) are also proved without holes.
The initial two-definition module and the eight-definition equality probe compiled without
warnings. The full set exposed the existing localized-Hom timeout; the source isomorphism
now has an irreducible definition and proved equation API, and its localized-Hom consumer
uses that equation instead of unfolding the geometric invertibility proof. The updated
StrictLocalLocalizedHomGerm and StrictLocalMateProjectionData compiled against the
delivered overlay; DerivedCohomologyGermIso and StrictLocalCohomologySourceColimit also
compiled. The whole delivered-set compile and axiom probes run before pushing. A subsequent full
compile reached the injective-source-derived restriction but exposed published compiled
statements for the complex mate and injective comparison that predate the landed geometry
transport (Q.legs rather than Q.smallModelLegs). Their current shared sources already
contain the correct small-model legs. The published build subsequently advanced to
2026-10-21T22:51:53Z, allowing delivery validation to resume.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms.
Its eight public duplicate names no longer have local definitions. The six common
constructions and the two canonical strictLocalization maps are all provided by the
adopted source module; the small-model pair has its distinct node and API names.

The four direct consumers replace their import of the withdrawn twin with
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms. The original direct public
imports of derived GlobalSections, UpperLowerStarCoherence and
StrictLocalSmallModel.NeighbourhoodGeometry are unnecessary in the focused small-model
module: the adopted canonical import supplies the required common interfaces. This
module needs only the section-cone data publicly, together with the adopted API.

The mate-continuity presentation no longer imports the duplicate small-model geometry
existence wrapper: its proof is exactly the adopted existence theorem. That wrapper
module remains in the library for its other users.

The former canonical node's pointed-cone/residue/stalk proof dependencies no longer
belong to its canonical attachment; its adopted proof uses canonical restriction and
its invertibility. They remain genuinely needed by the small-model definition node.
No mathematical dependency is falsely declared globally pruned, and no unit route is
bypassed. The remaining common-presheaf parents retain their canonical-node citation.
Quarantined archives and adopted-source declarations are preserved. Three archived
predecessors of the live StrictLocalSmallModel injective-source modules still mention
the old API; their live replacements are adapted in this packet, and the archives are
not current rework rows. See the change record for their paths.

## Where the brief, the DAG or earlier work was wrong

This item is a retirement with zero holes, not an unproved cohomology theorem.
The retirement table correctly marks the twin DIFFERENT: two definitions have different
strict-local target schemes. A blanket import substitution would silently change the
small-model mates and their germ calculations. Conversely, copying all eight definitions
to another module would preserve six unnecessary duplicates. This packet removes those
six copies while making the actual model distinction explicit for the remaining pair.

The existing canonical DAG attachment named the twin and therefore could not coexist
with the adopted common constructions. It now records the adopted canonical API; the
small-model source maps have a distinct definition node. Parent statements only gain
explicit model citations; their prior statements and every citer check are recorded.
The initial delivery check exposed a stale compiled import of the retired neighbourhood
geometry through the exact existence wrapper. The proof now uses its adopted theorem
directly, and explicit proof imports order the adapted injective-source chain before
the continuity presentation. No target statement, source-library body, blueprint unit
statement or unit step changes.

## New nodes

def-weil-pbc-small-model-cohomology-germs attaches the two complete source-map
constructions on the small coordinate-ring colimit model. It reuses the adopted six
common constructions and the existing generic pointed-section-cone restriction and
invertibility criterion. Its proof and Mathlib searches are recorded; it has no hole.
The DAG and blueprint searches found no separate existing definition node for this
specific pair after the canonical node moves to its adopted source attachment.
The residue-functoriality and strictly-henselian-sections nodes are used as generic tools
for the existing small model, as in the prior proof; they supply precisely the closed
lift and its identity-neighbourhood germ isomorphism. They do not replace any unit step.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the planned stalk and quotient argument with the existing theorem
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap` from
`WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`. A closed immersion
provides the required `SurjectiveOnStalks` instance by inheritance. Removed the
unused `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks` import and updated the
sandbox DAG node to record the shorter route.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` is
proved. No `sorry`s remain in the delivered module.

## No longer needed

The planned dependencies `lem-weil-pbc-closed-pushforward-stalks`,
`lem-weil-pbc-locally-surjective-iff-stalks`, `def-weil-closed-immersion`,
`def-weil-locally-ringed-space-morphism`, `def-pc-scheme`, and `def-weil-residue-field` are not
needed by this proof, nor is `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`.

## Where the brief, the DAG or earlier work was wrong

The DAG plan was valid but unnecessarily long: the library already proves the
more general residue-field isomorphism for morphisms surjective on stalks.

## Second reading by M1

1. Compared the only delivered Lean module with the repository using diff. The
   existing declaration signature and public imports are byte-for-byte unchanged;
   only the proof and its private import change. No definition or target changes.
2. Local compilation passes without warnings. A scratch copy with #print axioms
   checks both the item and the upstream theorem: only propext, Classical.choice,
   Quot.sound; no sorryAx. No sorry, axiom, unsafe, opaque, implemented_by or extern
   occurs in the delivered module. Read the upstream proof: it lifts a residue
   representative through the surjective stalk map, then uses field injectivity.
3. No statement is split off and no new Lean declaration is needed. Searches by
   stalk surjectivity and residue-field bijectivity confirm the existing upstream
   theorem. LeanSearch was unavailable; Lean Finder, Loogle and direct rg were
   checked. Empty sources are vacuous (there is no w); identity immersions and
   affine quotient immersions satisfy the argument, with no point-surjectivity
   hypothesis. The general upstream result is strictly stronger than this item.
4. The existing generic theorem is the shortest route. Both public Mathlib
   imports provide signature notions; the upstream import is proof-only. Checked
   dag/units/sk-thm-p1.json: neither the item nor its removed proof dependencies
   realizes a unit step, and no unit route or realized field changes. Added the
   omitted def-pc-scheme to the complete old-proof-dependency pruning list.
5. The Lean proof and revised proof/proof_origin agree. Found that the first
   worker cited a nonexistent node for the upstream theorem. Added its DAG record
   with the existing declaration (existing:true), complete proof in words and
   search evidence, without duplicating the proved theorem. Restored unrelated
   JSON text formatting. No existing statement or statement dependency changes.

Second reading changed only the DAG metadata and report; the Lean proof is kept.

## New nodes

lem-weil-pbc-surjective-stalks-residue-field-iso records the existing proved
AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap in
WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism. It is a generic tool,
not a new theorem or an open split-off statement. No change record is needed.

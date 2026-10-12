## What changed

Replaced the whole-proof `sorry` in
`AlgebraicGeometry.etaleFpqcSections_exists_matching_family` with a complete Lean proof.
Its signature and both public imports are unchanged. Its two proof imports now supply
local representatives and joint injectivity of inverse-image units. The proof checks
restriction naturality explicitly, proves compatibility on the presieve using injectivity,
and extends to the generated sieve using Mathlib's `FamilyOfElements.sieveExtend`.
The matching equation on every generated-sieve arrow is proved by the same restriction
calculation. No global amalgamation is used.

Added three modules, each with one public theorem and a corresponding node:

- `Sheaf.AlgebraicGeometry.EtaleFpqcUnitsJointlyInjective` proves joint injectivity at
  every étale object. Base-changing the fpqc cover gives a geometric lift above each
  point. The existing inverse-image stalk germ comparison gives equality of the
  original germs; Mathlib's pointed-neighborhood refinement criterion and sheaf
  separatedness prove equality of sections.
- `Sheaf.AlgebraicGeometry.EtaleFpqcLocalRepresentatives` proves local existence from
  the inverse-image section description and the single-representative open theorem.
  It constructs one étale representative over each point of S, verifies its point
  maps to that point using the fibre-product equations, and proves this family covers.
- `Sheaf.AlgebraicGeometry.EtaleFpqcRepresentativeOpen` states the remaining geometric
  step for a single representative. It asks for an open containing that representative's
  image on which its restricted section matches all s_i. It does not assert covering
  or compatibility. Its entire proof is `by sorry`, with source and full proof in words.

Updated the existing node's proof, proof_deps and proof_origin to this route. The new
nodes record the dependencies of their actual proofs or the remaining agreement-open
argument. No existing statement, definition, visibility or public import changed, and
no forced adaptation or change record is needed. No data definition was added.

All four modules compile through lcompile.py in dependency order. Lines are at most
100 characters. The units theorem and main theorem compile without warnings; the sole
expected declaration-uses-sorry warning is on the representative-open theorem.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.etaleFpqcSections_exists_matching_family`
(node `lem-weil-pbc-etale-fpqc-matching-family`). No `sorry` remains in the item's module.

The delivery also proves:
`AlgebraicGeometry.etaleFpqcUnits_jointly_injective`
(node `lem-weil-pbc-etale-fpqc-units-jointly-injective`) and
`AlgebraicGeometry.etaleFpqcSections_exists_local_representatives`
(node `lem-weil-pbc-etale-fpqc-local-representatives`). Neither contains `sorry`.

Added exactly one hole:
`AlgebraicGeometry.etaleFpqcSections_descend_representative_open`
(node `lem-weil-pbc-etale-fpqc-representative-open`). This is the only `sorry` in the
four delivered modules. The item is a decomposition: one upper hole closed and one
strictly smaller geometric hole added, so its declaration-hole net is zero. The
local-cover and compatibility arguments are now actual compiled Lean proofs.
The remaining task is agreement-open overlap coherence and descent for a fixed V,t;
it no longer needs to construct a cover or a matching family.

## No longer needed

Removed the item's direct proof imports:
`Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription`,
`Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`,
`Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen`, and
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`.
The first three remain needed through the new modules, so those removals relocate
proof dependencies and are not claimed as pruning.

The restriction-isomorphism route for uniqueness is unnecessary. The following modules
leave this item's import closure (computed from the repository sources with the sandbox
overlay):

- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`, node
  `lem-weil-pbc-sets-etale-inverse-image-restriction`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `Mathlib.CategoryTheory.Adjunction.Triple`.

The original planned dependency `lem-weil-pbc-etale-covering-base-change` is also unused:
local representatives already come with their covering, and the uniqueness argument
base-changes the fpqc covering using the existing Mathlib leaf
`lem-galois-fpqc-covering-base-change`. The other original geometric dependencies remain
below the new nodes. This is pruning of this item's route; another target branch may
still reach these modules. No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's step 4 need not use agreement opens or
inverse image along an étale morphism: inverse-image stalk germ comparison and
separatedness give a shorter proof. The existing fpqc separatedness theorem only treats
the identity étale object; using it directly at arbitrary V would require extra
localization and composition identifications, which this germ argument avoids.

Checked edge cases: empty S gives the empty point-indexed covering; empty V gives the
empty covering in the injectivity proof. If I is empty and is an fpqc cover, joint
surjectivity forces the relevant base to be empty. Empty Z in the new open theorem
only requires containment of an empty image. For an identity fpqc cover, the open
statement reduces to the usual agreement locus of a representative with the datum.
No nonempty indexing or inhabited section assumption has been introduced.

Read the original signatures, node plans and sk-thm-iff realized record. Searched
Mathlib with the logged LeanFinder, LeanSearch and grep queries in searches.jsonl;
LeanSearch returned Internal Server Error and is honestly recorded as unavailable.
Searches of both Lean roots and DAG nodes found no existing theorem of the three new
signatures. Blueprint searches for fpqc local representatives, fpqc injectivity,
agreement open, étale sheaf sections and 09XN found no blueprint statement to reuse.
The ancestor script returns None for this module-created chain, so the new nodes
inherit the existing item's recorded ancestor and prepend the item to its via list.

The Stacks source is not present as a local .tex file on this machine. Read the official
[Tag 09XN](https://stacks.math.columbia.edu/tag/09XN),
[Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1), and
[Tag 03PU](https://stacks.math.columbia.edu/tag/03PU) pages. The node's conventional
literature path is retained and its precise tags identify the sources.

## New nodes

`lem-weil-pbc-etale-fpqc-local-representatives`:
`lean/Sheaf/AlgebraicGeometry/EtaleFpqcLocalRepresentatives.lean`;
`AlgebraicGeometry.etaleFpqcSections_exists_local_representatives`.
Covering and point-selection portion of Tag 09XN, proved from the existing local section
representation theorem and the single-representative open theorem. Its conclusion has
no chosen compatible family.

`lem-weil-pbc-etale-fpqc-units-jointly-injective`:
`lean/Sheaf/AlgebraicGeometry/EtaleFpqcUnitsJointlyInjective.lean`;
`AlgebraicGeometry.etaleFpqcUnits_jointly_injective`.
Proved from inverse-image stalk germ comparison and Mathlib covering/separatedness
facts. It has no overlap datum or local-existence premise.

`lem-weil-pbc-etale-fpqc-representative-open`:
`lean/Sheaf/AlgebraicGeometry/EtaleFpqcRepresentativeOpen.lean`;
`AlgebraicGeometry.etaleFpqcSections_descend_representative_open`.
The sole new hole: the agreement-open and fpqc open-descent step for one representative,
with its representing equation as input and a containing open plus matching equations
as output. Its proof in words and DAG cite the agreement-open, open-descent, composition,
stalk-comparison and geometric-germ extensionality interfaces.

## Second reading by N1

1. Compared every delivered module against the repository version. The existing matching-family theorem signature is byte-for-byte unchanged; the three additional modules and node files are declared additions, and no existing definition or target statement was altered.

2. Compiled all four modules with `lcompile.py --all`. The three proved declarations compile without `sorry`; the only remaining `sorry` is the named representative-open theorem. No forbidden declarations or hollow definitions occur. The proved declarations use only permitted axioms (the open theorem necessarily reports `sorryAx`).

3. Read the three new statements and their nodes, and checked edge cases including empty schemes, empty indexing types, and empty representatives. The statements are true, strictly smaller than the original matching-family goal, and each has source, proof description, and a matching DAG node. No duplicate library theorem was found in the recorded searches.

4. Checked the proof from the target downward. The matching-family proof uses local representatives, restriction naturality, joint injectivity, and `FamilyOfElements.sieveExtend`; removed imports are no longer directly used. The unit route remains realized, while the restriction-isomorphism route is pruned as recorded above.

5. Checked that node `proof`, `proof_deps`, and `proof_origin` describe the actual Lean route. The remaining split theorem is the single agreement-open descent step and is documented as such; no statement is weakened or given extra hypotheses.

I changed only this report during second reading. The source modules and node files already compiled and required no proof repair.

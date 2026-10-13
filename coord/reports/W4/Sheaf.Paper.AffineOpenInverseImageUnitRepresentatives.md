## What changed

Replaced the hole in `affineOpenSections_inverse_image_unit_representatives` with a
complete Lean reduction. The proof obtains finite local unit lifts, refines them
until they are compatible, glues them using the underlying set sheaf of F, and
proves the representative equation by unit naturality and separatedness.
Monomorphism cancellation proves the needed terminal-to-pullback arrow equation.
The supplied adjunction, universes, hypotheses and conclusion are unchanged.

Added proof-only imports of `Sheaf.Paper.AffineOpenInverseImageFiniteLocalLifts`,
`Sheaf.Paper.AffineOpenInverseImageCompatibleRefinement`, and
`Mathlib.CategoryTheory.Sites.Whiskering`. The two new modules contain one public
named intermediate theorem each, with source and complete proof in words.
Updated the original node's proof, proof_deps and proof_origin to follow the Lean.
No existing definitions, interfaces, or other modules were adapted.

All three modules compile through lcompile.py without warnings. The finite local
lifting statement was checked on empty limits, empty covers, singleton diagrams
and zero coefficients. The compatibility statement also handles empty overlaps:
for an empty index its stage covering forces the original stage empty and the
identity refinement works. The final gluing proof uses the sheaf axiom for empty
covers with no nonemptiness assumption on the covering index.

## Proved and sorry left

Closed the original hole in
`affineOpenSections_inverse_image_unit_representatives`
(node `affine-open-inverse-image-unit-representatives`). No sorry remains in the
item's module. Its proof is complete from the two intermediate statements.

Added exactly two holes, each the entire proof `:= by sorry`:

- `affineOpenSections_inverse_image_finite_local_lifts`, node
  `lem-weil-pbc-affine-open-inverse-image-finite-local-lifts`, module
  `Sheaf.Paper.AffineOpenInverseImageFiniteLocalLifts`. It only gives a finite
  stage covering and local sections; it asserts no agreement on overlaps.
- `affineOpenSections_inverse_image_compatible_refinement`, node
  `lem-weil-pbc-affine-open-inverse-image-compatible-refinement`, module
  `Sheaf.Paper.AffineOpenInverseImageCompatibleRefinement`. Given the local lifts,
  it gives a later compatible covering refinement; it asserts no amalgamation
  or global section.

This is a decomposition: one upper hole closed, two lower holes added, net -1
before the maintainer measures the target closure. It is not an axiom-free proof
of the mathematical statement. No data definition depends on either new hole.

## No longer needed

No original import was removed: the original file had only the three public
statement imports, and all remain. Removed the redundant proof import
`Mathlib.CategoryTheory.Sites.Sheaf` after compilation; Whiskering supplies it.

The explicit colimit-site construction is not needed by this route:
`lem-weil-pbc-colimit-of-sites` and `Sheaf.CategoryTheory.ColimitSites` are absent
from the new dependency route. No use is made of the disputed larger
`lem-weil-pbc-affine-etale-site-colimit` / `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
These are route exclusions, not claims that no other target branch uses them.

The original direct dependencies for directed reindexing, finite diagram descent,
finite cover descent and open inverse-image restriction move to the finite local
lifting subargument; they are not globally pruned. The filtered-colimit
sets-elementwise lemma is no longer a direct dependency of the item, although
it underlies the existing local inverse-image section description. The original
six direct planned dependencies are replaced in the item's node by the two new
local steps and the definition nodes used in its proved sheaf calculations.

## Where the brief, the DAG or earlier work was wrong

The original node's plan hides the coherent affine-site section construction;
its finite-descent and colimit-site declarations do not directly present the
unit representatives required by this signature. The replacement separates
local lifts from agreement and proves their sheaf-theoretic combination.

Existing `etaleInverseImageSectionDescription`,
`etaleInverseImage_joint_representatives`, and
`etaleSet_eventualLocalStageCompatibility` were read. They respectively concern
set sections/local representatives or supplied canonical set comparisons, with
schemes in universe v and coefficients in universe v+1; this item has schemes
and AddCommGrpCat coefficients in the same universe u+1 and an arbitrary supplied
adjunction. Thus they do not apply directly to this statement. The new lemmas
record the missing local steps at this exact interface; their proofs in words
explain adjunction and unit transport. The already-proved compatibility module's
geometric overlap argument is also suitable reference material for the second
new item after the universe and adjunction comparisons are supplied.

Tag 09XN is the comparison with the big site, not a lemma named describe-pullback;
the local representative paragraph of its proof supports the local lifting
step. The Stacks pages 09XN, 09XM, 0EYL, 03Q6 and 0A35 were read online because
the literature copies are absent on this machine. LeanSearch returned Internal
Server Error; the logged unavailable searches are not counted as negative matches.

The item's existing blueprint ancestry is retained: the generic ancestor helper
prints None for this module-created node, but its recorded ancestor is
`lemma-weil-pbc-gabber-effacement`; the new nodes inherit that explicit ancestry.
No node realizing a unit statement or unit proof step is bypassed.

## New nodes

`lem-weil-pbc-affine-open-inverse-image-finite-local-lifts`, in
`dag/nodes/sec-proper-base-change/`, records the finite affine stage covering with
local unit lifts before any agreement or gluing. Its source is the local
representative paragraph of Tag 09XN and finite descent in 0EYL/03Q6. Three actual
search kinds are recorded, including the unavailable LeanSearch result.

`lem-weil-pbc-affine-open-inverse-image-compatible-refinement`, in the same
chapter, records eventual overlap agreement as a covering refinement, without
constructing the final section. Its source is the equality-open argument of
09XM and the finite overlap argument of 03Q6. Three actual search kinds are
recorded. Neither new node states the original global representative conclusion.
No change record is needed: no existing signature or definition changed.

## Second reading by W4

1. I compared the delivered item module with the repository version line by line.
   The theorem signature of `affineOpenSections_inverse_image_unit_representatives`
   is byte-for-byte unchanged: all universes, typeclass hypotheses, adjunction data,
   section data, and the existential conclusion remain present. The two new theorem
   signatures were checked against their node statements, including the empty-finite-
   family case and the separate covering hypotheses. Verdict: unchanged item and
   matching new statements.
2. I compiled all three delivered modules with `lcompile.py --all`. The item proof
   uses the two lower theorems, sheaf amalgamation, unit naturality, and cancellation
   of the pullback monomorphism; each use typechecks in the exact hypotheses supplied.
   The only remaining `sorry`s are the two named lower theorems, each with a source,
   full proof description, and a corresponding DAG node. No definition contains a
   `sorry`, and the delivered declarations introduce no axiom, unsafe, opaque, or
   implementation escape. Verdict: proof and split-hole requirements pass.
3. I read both new node files and searched the existing Lean and DAG declarations for
   inverse-image local lifts and compatible refinements. No existing declaration has
   either exact interface. The finite-local-lifts node stops before overlap agreement;
   the compatible-refinement node stops before amalgamation; neither restates the
   item's global representative conclusion. Their source places and three recorded
   search kinds are present. Small cases recorded by the worker (empty finite family,
   empty overlaps, singleton diagram, and zero coefficients) are covered by the
   quantifiers and the stated constructions. Verdict: both splits are true,
   strictly smaller, and needed.
4. I checked pruning against the actual imports and proof. The three original public
   imports are retained because the signatures and geometric definitions need them;
   `Mathlib.CategoryTheory.Sites.Whiskering` is proof-only. The item proof follows
   the unit route: local lifts, eventual compatibility, then sheaf gluing and unit
   naturality. The item node's `proof` and `proof_deps` name exactly those steps and
   the two new nodes, while the lower nodes retain their stated source dependencies.
   The unit `sk-thm-p1` and its realized route are unchanged. Verdict: imports,
   dependency metadata, and unit route agree with Lean.
5. I checked the delivered report against the source and DAG records, including the
   explicit explanation of why the earlier direct colimit-site route was replaced.
   No statement-change record is needed because no existing interface changed; the
   two new modules are necessarily a CODEX delivery because they add public split
   statements. I corrected the report by adding this second-reading section; no Lean
   source or node statement was changed. Verdict: delivery documentation is complete.

The second reading changed only `report.md`, adding this required review section.

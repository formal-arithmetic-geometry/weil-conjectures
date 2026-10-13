## What changed

Replaced the sorry in `affineOpenSections_zero_detection`, without changing its signature
or visibility. The proof rewrites the canonical component formula, obtains an open zero
neighbourhood of the limit image, applies Mathlib `AlgebraicGeometry.exists_map_eq_top`,
and explicitly factors the later-stage arrow through that open. Presheaf functoriality
and preservation of zero finish the argument.

Added proof imports `Sheaf.Paper.EtaleSectionZeroNeighbourhood` and
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`. Removed the redundant public import `Mathlib.AlgebraicGeometry.Morphisms.Affine`: its
statement vocabulary is already public through the étale-site import, and its proof API
is supplied by the private `AffineTransitionLimit` import.
Added the single-morphism helper module and its node; updated the item's proof route.
No definitions, signatures, instances, attributes, or other modules were changed.

Both modules compile cleanly with lcompile.py. The open factorization uses an actual
`IsOpenImmersion.lift`, not a chosen witness in a definition. All existential elimination
occurs inside the theorem proof.

## Proved and sorry left

Closed: `affineOpenSections_zero_detection` (node
`affine-open-sections-zero-detection`), the item's only original hole.

Added and left: `etaleSection_zero_neighbourhood` (node
`lem-weil-pbc-etale-section-zero-neighbourhood`), with its whole proof `:= by sorry`.
This is a decomposition: one hole closed, one added, net zero. The new statement is the
single-morphism sheaf-local step, not eventual vanishing under another name. It has no
indexing category, limit, affine hypotheses, transition maps, or finite-stage conclusion.
The compact inverse-limit argument and the actual restriction-factorization proof are
completed in the item.

The helper's proof is fully described in its docstring and node: zero geometric germs
have zero étale-neighbourhood representatives; an étale neighbourhood covers its open
image, where separatedness gives zero; union gives an open zero locus. The pullback
stalk isomorphism puts the image of T inside it. Left-adjoint uniqueness handles arbitrary
H with its supplied unit. Empty T admits the empty open; s=0 admits the whole object.
For the original theorem an empty limit is handled by exists_map_eq_top; a singleton
system needs no special branch; the zero sheaf is immediate. No hollow data were added.

## No longer needed

Removed the redundant import `Mathlib.AlgebraicGeometry.Morphisms.Affine`; its
proof API is available through the proof import `AffineTransitionLimit`. The statement
vocabulary remains available through the public étale-site import.
The following original proof-plan dependencies are not needed by this proof and were
removed from its proof_deps:

- `lem-weil-pbc-affine-etale-site-colimit`, module
  `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`;
- `lem-weil-pbc-colimit-of-sites`, module `Sheaf.CategoryTheory.ColimitSites`;
- `lem-weil-pbc-etale-inverse-image-restriction`, module
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `lem-weil-pbc-cofiltered-limit-directed-reindex` (the Mathlib directed-reindexing route);
- `lem-weil-pbc-filtered-colimit-sets-elementwise` (the Mathlib elementwise-colimit route).

These are pruned from this item's route, not claimed unreachable from every other target.
Neither general colimit-site theory nor directed reindexing is imported for the proof.
The elementwise-colimit leaf is no longer used directly by the item, but is cited
in the new helper’s natural-language zero-germ argument; it is not globally pruned.
The new route uses the existing Mathlib leaf
`lem-weil-pbc-limit-image-contained-in-open`. No node realizing the unit's statement or
steps in `dag/units/sk-thm-p1.json` is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned general site-colimit construction is unnecessary
for zero detection: the open zero locus and compact affine-limit image containment suffice.
Existing abelian global-section continuity APIs use coefficients in the universe above the
scheme universe, so they cannot be applied directly to this item's same-universe coefficient
category. They were not adapted or duplicated.

LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder and grep
returned structure-sheaf/algebra zero-locus results, not the needed arbitrary étale-sheaf
zero-neighbourhood statement. Blueprint searches for zero loci, section vanishing, and
pullback stalks found no duplicate of the helper. The existing pullback-stalk blueprint
node supplies its stalk comparison. Sources read: Stacks 03PN and 03PU, and the existing
lemma-openclosed-stalk-upperstar node and Lean interface. Second reading corrected
the source for unit-germ compatibility to Stacks 03Q1 (3) and its existing
`lem-weil-pbc-inverse-image-stalk-germ` node; 03PU omits the injectivity proof.

## New nodes

`lem-weil-pbc-etale-section-zero-neighbourhood`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-section-zero-neighbourhood.json`,
records `etaleSection_zero_neighbourhood` in
`lean/Sheaf/Paper/EtaleSectionZeroNeighbourhood.lean`. It isolates only the local sheaf
argument; Mathlib supplies the geometric descent to a later stage. Its source, complete
proof, edge cases, performed searches, and ancestor are recorded. The intentional public-import removal is recorded in
`coord/changes/affineOpenSections_zero_detection_imports.md`; no existing signature
or definition changes.

## Second reading by P1

1. Compared the full item module with the repository using `diff -u`. The complete
   `affineOpenSections_zero_detection` signature, its visibility, universes, every
   hypothesis (including the supplied adjunction and canonical component equation),
   and its existential conclusion are byte-for-byte unchanged. There are no definition
   changes or forced adaptations. The only delivered new declaration is the named
   helper. Verdict: no accidental interface or mathematical statement change.

2. Compiled both modules in import order with `lcompile.py --all`, including after
   removing the redundant affine import. No errors or warnings. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   There is exactly one explicit sorry, the reported public helper theorem. Neither
   module defines data or uses axiom, unsafe, opaque, implemented_by, or extern.
   The factor b is an actual `IsOpenImmersion.lift`; existential choices occur only
   inside the proposition proof. Verdict: the reduction is kernel-checked, with its
   one dependency hole explicitly accounted for; net holes closed minus added is zero.

3. Read the helper against the filtered-colimit stalk definition in Stacks 03PN,
   Definition 59.29.6, and pullback-stalk compatibility in 03Q1 (3). A zero germ is
   zero on a pointed étale neighbourhood; that morphism is étale and open, and its
   map onto its open image is a covering. Separatedness detects zero on that image.
   The union of these zero opens is again zero by the sheaf axiom. At every point of
   T an algebraic-closure point, the unit-germ formula and naturality for restriction
   transfer the assumed zero to the germ of s at its image. Left-adjoint uniqueness
   transports the supplied unit, so no chosen adjunction is implicitly assumed.
   Checked empty T, empty V, s=0, a=id with p=V.hom, and the zero sheaf: each gives
   exactly the claimed open, including the empty-cover sheaf condition when needed.
   The helper has no finite-stage, limit, or affine claim, so is strictly the local
   part of the argument, rather than a renaming of the item. Fresh LeanFinder,
   Loogle and grep searches with germ/vanishing terminology found no exact Mathlib
   match. Read the related `EtaleSectionsEqualOpenExistence`,
   `EtaleSectionsEqualOpenArbitraryCriterion`, `EtaleSetSectionComparisonEqualOpen`,
   and `InverseImageStalkGerm`: their coefficient universe is above the scheme
   universe, whereas this item uses the same universe. They are not direct
   specializations; no short proof of the helper using them was found.
   Verdict: true, suitably smaller, and not a duplicate of an applicable interface.

4. Read the proof downward. The first step applies exactly the helper's canonical
   unit/restriction expression, using hp j. Affineness supplies CompactSpace and
   IsAffineHom, exactly the hypotheses of `exists_map_eq_top` (read its statement
   and closed-complement proof in AffineTransitionLimit.lean, lines 180–198).
   The last step verifies both the over-X factorization equation and g ≫ i = D(f)
   before functoriality and map_zero; no unproved descent assertion is hidden there.
   The report lists all five old proof_deps omitted from the item's new route.
   Checked `dag/units/sk-thm-p1.json` and its realized statement and four steps:
   this item lies below the strict-henselian comparison step; no realized node is
   bypassed or removed. Verdict: genuine reduction below the unit level, minimal
   direct imports after removing the redundant affine import.

5. Compared the changed item node with the repository: only proof, proof_deps and
   proof_origin differ. Its three steps match the helper, compact-limit theorem,
   and elementary factorization in Lean. Checked the new node's full statement,
   lean.statement, source, created record, blueprint ancestor, chapter/unit, and
   search records. Its docstring describes the whole remaining proof. The original
   node wrongly treated the bare stalk isomorphism as also giving compatibility
   with unit germs; added the existing germ-compatibility node, the elementwise
   filtered-colimit leaf, and the étale-open-map leaf to the proof citations and
   their union proof_deps. Verdict: the DAG now names the facts actually needed.

Second reading changed the item's obsolete proof docstring to the actual
zero-neighbourhood/compact-limit/factorization route, corrected the helper's source
and unit-germ explanation and DAG citations, removed the redundant public affine
import, and updated this report. No theorem signature or proof term was changed.

The delivery dry run required a change record for the public-import removal;
added `coord/changes/affineOpenSections_zero_detection_imports.md`. The sole direct
importer `Sheaf.Paper.AffineOpenSectionsCanonicalColimitCore` publicly imports the
removed affine module itself, so all transitive users retain that API. An attempted
unchanged downstream scratch compile could not load the baseline's missing
`AffineOpenSectionsDescent.olean`; this does not affect the clean two-file delivery
compile and is recorded as a verification limitation in the change record.

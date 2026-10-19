## Worker report

The module defines the enriched mapping cylinder of a simplicial functor using the disjoint union of object sets. `mappingCylinderHom` gives `C` mapping simplicial sets in the left summand, `D` mapping simplicial sets in the right summand, `D(fa,d)` for left-to-right maps, and the empty simplicial set for right-to-left maps. `mappingCylinderComp` gives the four specified composition formulas; the three enriched category laws are named statement-only helper theorems with `sorry`, and `mappingCylinderFixed` packages the real mapping-set and composition data. `mappingCylinder` bundles this fixed enrichment.

The retraction `mappingCylinderRetraction` sends a left object to `f.obj a`, a right object to itself, uses `f.map` on left-left maps, identities on left-right and right-right maps, and the unique map from the empty simplicial set on right-left maps. Its identity and composition laws are named statement-only helper theorems. `mappingCylinderBridge` is the left-to-right arrow represented by the identity of `f.obj x` in degree zero.

The theorem `enriched_mapping_cylinder_localization` uses the fixed interval factorization `K`, `i`, `r` from `simplicial_arrow_attachment_localization`, a labelled arrow family `a`, the hypothesis `mapsLabelsToIdentities` for the retraction, and the condition that every bridge arrow occurs among the labels. For every identity-collapse extension `gbar` over the strict attachment, it states that `gbar` is a Dwyer--Kan equivalence. The theorem proof is `sorry`, as required at stage 2.

Dependencies used: `Sheaf.CategoryTheory.SimplicialArrowAttachmentLocalization` (`arrowFamily`, `labelledArrowMap`, `mapsLabelsToIdentities`, `attachmentPushout`, `IsCollapseExtension`, `walkingArrow`, `walkingGroupoid`, `adjoinInverse`), `Sheaf.CategoryTheory.SimplicialNaturalEquivalenceHomotopy`, and `Sheaf.CategoryTheory.SimplicialModelTargetTest` (the latter two are imported for the homotopy-category argument recorded in the source proof plan).

Edge cases checked: the empty left or right summand is represented by the explicit empty simplicial set and empty mapping block; the reverse mixed block has its unique map; `V` may be empty, and repeated or coincident labels are permitted by the labelled-arrow-family interface. No cofibrancy or Kan hypothesis on `C`, `D`, `f`, or their mapping simplicial sets was added.

Searches made: `msearch.py Q28 lem-coef-enriched-mapping-cylinder-localization leanfinder "enriched mapping cylinder localization Dwyer Kan equivalence"` found only unrelated cylinder and simplicial localization declarations; `msearch.py ... loogle "SCat, DwyerKanEquivalence, mappingCylinder"` found no matching enriched mapping-cylinder theorem; `msearch.py ... grep "mappingCylinder|mapping.cylinder|Dwyer|Bergner" CategoryTheory` found no existing declaration in Mathlib; `rg -n "mappingCylinder|mapping.cylinder|Dwyer|Bergner"` over the project found only ordinary chain-complex cylinders and unrelated simplicial constructions. The existing dependency module `SimplicialArrowAttachmentLocalization` supplies the fixed attachment model used here.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q28

The node and file were read together. The two summand mapping clauses, the left-to-right mapping object, the empty right-to-left mapping object, all four composition cases, the retraction action, identity-collapse hypothesis, bridge coverage hypothesis, and Dwyer--Kan conclusion are each represented in the Lean declarations above. The Lean theorem additionally makes the fixed interval factorization explicit, exactly as required to use the recorded attachment model. No hypothesis was added about cofibrancy, Kan fibrancy, or nonempty object sets.

## Maintainer review fix (2026-10-18)

The independent maintainer review made only docstring and import changes to
`lean/Sheaf/CategoryTheory/EnrichedMappingCylinderLocalization.lean`. The signatures and
definitions are unchanged. (1) H8: the docstring of `enriched_mapping_cylinder_localization` now
carries the node's five proof steps with the nodes they use. `emptyTensorRight` now has a
source/blueprint docstring, and the module docstring now has `## Main definitions` and
`## Main statements`. (2) H9: the unused imports `Sheaf.CategoryTheory.SimplicialNaturalEquivalenceHomotopy`
and `Sheaf.CategoryTheory.SimplicialModelTargetTest`, and the `open` of the latter namespace, were removed;
stage 3 imports them when it proves the theorem. The module compiles clean with `nt_compile.py`.

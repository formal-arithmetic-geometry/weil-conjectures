# Stage-1 worker report: def-sfb-modobj-extension-along-iso

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-modobj-extension-along-iso.json`: existing item, split into three proof steps; no exact Mathlib match. The statement is unchanged. Its statement dependencies additionally name `def-sfb-modobj-extension`, which defines the functor in its conclusion.
- `citations.json`: five step/node pairs, each with a verbatim quotation from the cited statement.
- `report.md`: rewritten on resumption after independently checking the retained split and its sources. The retained `searches.jsonl` contains the actual earlier searches; this resumption did not rerun or invent searches.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: `lem-weil-pbc-quasi-inverse-adjoint` and `lem-weil-pbc-conjugate-iso-unit-equation`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id, `extendScalarsIsoComapInv`, `comapEquivalenceOfIsIso`, `extendScalars`, and the phrase “extension of scalars.” No project declaration states the general module-object comparison. Ordinary ring-module change-of-scalars and sheaf constructions have different statements. Upstream master is reference material only and was not used as finished-proof evidence.

## Wanted sources

None. All sources used below are available locally.

## Issues found and changes

The imported proof uses two categorical theorems without corresponding node citations. The retained split cites the existing quasi-inverse-adjoint and conjugate-isomorphism Mathlib leaves, specifies both adjunctions and their directions, and applies the identity comparison of their common right adjoint. No clause has been moved into a new helper.

There is no statement dispute: the statement agrees verbatim with the current main-20261015 blueprint and with the shared item, which is still imported and unreviewed. There is no `blueprint_update` requiring a different route. The unit's clause 5 supplies all the extension hypotheses through the restriction-equivalence context. The chapter route and the unit's adjoint-comparison argument are followed.

The imported item is classified as a definition although it asserts an isomorphism and has a proof. Its `chapter` and `unit` fields and the corresponding chapter/unit JSON records are absent. These are maintainer-owned metadata; I leave them unchanged and read the actual current chapter and unit `_section.md` files. This item is not the unit's key node. The permitted `blueprint.same_as` is `[]`; the coextension comparison is a different assertion, and the unit states a larger conjunction.

## Unfinished work

No mathematical repair to the retained split was necessary on this resumption. The dependency nodes' own work is separate; the extension-restriction-adjunction node is now split in the current shared snapshot. This delivery uses their stated interfaces. A separate reader is still to inspect and deliver this sandbox. Nothing is pushed by this worker.

## Not duplicates

No new nodes. I read the current whole-blueprint searches for “extension along,” “quasi-inverse,” and “left adjoint,” and opened the two existing categorical leaves instead of creating helpers. The source unit and restriction-equivalence node are already present; extension and coextension along an isomorphism have different left/right-adjoint assertions. Thus there are no new/existing same-tag pairs requiring separation.

## Review by Q37

I independently read the current item statement and proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-change-of-scalars/`, that unit's `_section.md` (especially clauses 2, 3 and 5), and the chapter `_section.md`. I read the full statements of every node cited by the three proof steps, and the extension definition. The hypotheses are a braided closed monoidal category with equalizers and coequalizers, tensoring on both sides preserving colimits, a commutative source monoid, and an isomorphism of monoid objects. The conclusion uses exactly these same objects. No SGA source is used.

Step 1 uses `def-sfb-modobj-restriction-equivalence` for the actual equivalence R from S-modules to R-modules and its specified quasi-inverse I in the opposite direction. `lem-weil-pbc-quasi-inverse-adjoint` explicitly gives I left adjoint to R, including the natural Hom bijections and adjointification. I checked Stacks `categories.tex`, Tags 001J (`definition-equivalence-categories`) and 0037 (`definition-adjoint`), and read Mathlib `CategoryTheory/Equivalence.lean:327,353,366` and `CategoryTheory/Adjunction/Basic.lean:719`. The construction adjusts equivalence coherence while keeping both functors, so the proof does not assume arbitrary equivalence isomorphisms satisfy triangle identities.

Step 2 uses the restriction-equivalence statement for its hypotheses and `def-sfb-modobj-extend-restrict-adjunction` for Ext left adjoint to that same R. I checked that the latter's context is precisely `def-sfb-modobj-extension`: braidedness, coequalizers, tensor colimit preservation and commutativity of the source are all available. Its statement identifies the tensor-coequalizer functor, unit and natural Hom bijection. Closedness and equalizers are present in the ambient context but are not extra requirements introduced by this step. No abelianity, exactness, or additional coefficient identification is used.

Step 3 uses the explicit identical-right-adjoint clause of `lem-weil-pbc-conjugate-iso-unit-equation`. Set L1 = Ext, L2 = I, R1 = R2 = R, and delta = identity. Both left adjoints go from R-modules to S-modules. Its statement yields a natural isomorphism c: Ext to I satisfying R(c_M) composed after the Ext unit equals the I unit; both sides have source M and target R(I(M)). I read Stacks Tag 0B65, `categories.tex`, `lemma-transformation-between-functors-and-adjoints`, including its proof, and Mathlib `Adjunction/Unique.lean:36,53` and `Adjunction/Mates.lean:311,425`. The cited statement supplies naturality and invertibility, not merely objectwise maps. Uniqueness is relative to the adjunction units. All three steps are correctly marked non-elementary and cite the statements they need; none extracts extra conclusions from a cited proof.

For Mathlib, all 15 search records in the item have exactly matching tool/query entries in the retained `searches.jsonl`. They include LeanFinder, Loogle, LeanSearch, source greps, and second phrasings. I read the recorded results and checked the actual candidates above, plus `CategoryTheory/Monoidal/Mod.lean:350-430`: `scalarRestriction`, `scalarRestriction_hom` and `comap` define restriction only. The ordinary ModuleCat hits do not identify tensor-coequalizer extension for arbitrary module objects. The two general categorical results are already existing Mathlib leaves; applying them here still needs the module-object adjunction.

Against delivery-errors B-E, no new node needs a statement-only, source, definition-dependency or Mathlib-leaf audit, and no elementary fact, duplicate, or clause of this item has become a node. I verified all five quotation strings are literal substrings of the current cited statements, all cited nodes are unmerged, proof_deps equals the union of step uses, and no path through the 153 transitive dependencies returns to this item. Every changed node field belongs to the split's permitted fields.

For small cases I checked identity phi and zero modules: comparison of adjoints still works without equating arbitrarily chosen units. For ordinary commutative rings with a nonidentity automorphism, the comparison sends s tensor m to phi-inverse(s)m, with inverse m to 1 tensor m. Balancing follows from phi-inverse(s phi(r))m = phi-inverse(s)(rm), and the S-action agrees with inverse restriction. The zero ring also causes no exception. No nonzero, characteristic, size or faithfulness hypothesis was added. There are no new statements to test separately.

## Dry run

Required command (the installed parser takes only group and item as positional arguments):

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q37 def-sfb-modobj-extension-along-iso --no-push`

The earlier attempts recorded a worktree-capacity blocker before preflight. This resumption retries the unchanged delivery tool after the above audit. Only its final OK result establishes readiness; this worker does not push or bypass shared locks.

## Second reading by Q37

- Item statement: checked against `def-sfb-modobj-extension-along-iso.md` in the main-20261015 blueprint and clause 5 of `sk-def-sfb-change-of-scalars`; the functors, direction, and inherited hypotheses agree exactly.
- Step 1: checked against the statements of `def-sfb-modobj-restriction-equivalence` and `lem-weil-pbc-quasi-inverse-adjoint`; the restriction functors have the stated variance and the cited leaf supplies the left adjunction, so the verdict is correct.
- Step 2: checked against `def-sfb-modobj-restriction-equivalence` and `def-sfb-modobj-extend-restrict-adjunction`; every extension hypothesis is inherited and the cited adjunction has the same right adjoint, so the verdict is correct.
- Step 3: checked against `lem-weil-pbc-conjugate-iso-unit-equation`; with both right adjoints equal to restriction, its unit equation gives the required natural isomorphism and direction, so the verdict is correct.
- Existing dependency statements: checked `def-sfb-modobj-extension` and `def-sfb-modobj-restriction` while checking the extension-adjunction context; no missing definition or hypothesis was found.
- Existing Mathlib leaves: checked the full statements and recorded declarations for `lem-weil-pbc-quasi-inverse-adjoint` and `lem-weil-pbc-conjugate-iso-unit-equation`; both are reused as interfaces and no new node is needed.
- Small cases: identity coefficient isomorphism, zero modules, the zero ring, and an ordinary commutative-ring automorphism all satisfy the comparison; no extra nonzero, characteristic, or faithfulness assumption is hidden.
- Changes: none to the mathematics or node files; appended this second-reading section and retained the worker's three-step split and five verbatim citation quotations.

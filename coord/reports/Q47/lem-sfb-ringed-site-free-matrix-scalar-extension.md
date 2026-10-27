## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-free-matrix-scalar-extension.json: statement, split in eight steps; Mathlib has related sectionwise and ordinary-ring declarations but no direct match for the combined internal statement.
- citations.json: verbatim statement excerpts for each node cited in each step.
- No new nodes, no Mathlib leaves, no unit file changes.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, freeHomEquiv, matrix/scalar combinations, and the internal ringed-site notion. AdicSheaf.freeHomEquiv concerns a particular adic category and does not give the general site or internal coequalizer clauses. The ordinary-ring and sectionwise declarations do not establish this whole item.

## WANTED

None.

## Issues found

The statement is retained verbatim: it is a correct finite-basis assertion. Hemo–Richarz–Scholbach Example 3.1, printed page 6 (and Remark 3.2), supplies the continuous-coefficient motivation, but does not prove this general-site underived calculation. The proof is therefore marked agent-written, following the tensor construction and bilinear characterization in Stacks Tag 03EK, sites-modules.tex, section-tensor-product. The internal/sectionwise equivalence is an explicit hypothesis, not silently re-proved or assumed to identify arbitrary tensor sections with tensors of sections.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor returns None, since the ancestry eventually reaches a node created for Sheaf.SixFunctors.CtfStabilityDirectImages rather than a blueprint node. Retained this metadata and its specific inherited place; did not invent an ancestor or modify another node. Whole-blueprint searches for "free matrix", "finite free", "global sections" and "tensor product", together with whole-DAG concept searches, found no blueprint statement giving all the item's clauses. Related constant-coefficient finite-free tensor nodes require constant coefficients, or work with sectionwise tensors or derived resolutions, and do not replace the present general internal calculation.

## Mathlib searches

Ran and read all five searches recorded in this sandbox's searches.jsonl: two LeanFinder phrasings, Loogle for SheafOfModules/freeHomEquiv, grep of Algebra/Category/ModuleCat/Sheaf, and LeanSearch for the combined matrix/base-change assertion. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean, lines 30–110, including freeHomEquiv at line 61. This is an equivalence for sectionwise module sheaves. LeanSearch also returns LinearMap.toMatrix_baseChange and ModuleCat.ExtendScalars.map_tmul for modules over ordinary rings. Neither is a one-line proof of the internal comparison, including the passage through sheaf tensor and the balancing coequalizer. Preserved the item's imported Q55 search records and appended the exact newly logged queries; no search is invented.

## Not duplicates

No new nodes. In particular, the matrix clauses were not renamed into child nodes, and finite-sum identities were kept as proof steps. The generic internal-extension-finite-presentation node is restricted to pro-étale schemes and does not supply the general-site matrix assertion. The constant-finite-free-presentation-extension node also assumes constant source coefficients. Neither is cited for a claim it does not state.

## Review by Q47

I read the chapter and unit records, the source item, its three statement dependencies, the internal extension and extend/restrict adjunction nodes, and the tensor and sheafification nodes. I read Hemo–Richarz–Scholbach Example 3.1 and Remark 3.2 on printed page 6, and Stacks sites-modules.tex Tag 03EK's actual sheafified tensor construction and bilinear characterization. The chapter's internal-module coefficient route is maintained. This is below the continuous-coefficient direct-image subargument; no six-functor route or coefficient category is replaced.

Step 1 uses the internal/sectionwise equivalence's explicit preservation of sections and restrictions. It does not take preservation of finite free sheaves on faith: the finite tuple sheaf and its coproduct property are checked by componentwise gluing and the finite-sum formula. The module-object definition identifies the regular module. Step 2 uses the same equivalence and gives both inverse constructions for matrices, using the terminal object's unique arrows to restrict the global basis images. Step 3 calculates addition, composition and identity entries directly; its multiplication order is checked on e_j.

Step 4 uses the sheaf-tensor statement that the abelian tensor is the sheafified objectwise tensor, and the sheafification statement that maps to a sheaf factor uniquely. Ordinary tensor bilinearity extends the displayed sectionwise map; the written equation verifies the exact two coequalizer arrows of change-of-scalars. The extension hypotheses hold here: abelian sheaves have coequalizers, and the sheaf-tensor node supplies preservation of colimits by tensoring. Commutativity of R and S is assumed in the item. No point or subcanonical-site hypothesis is introduced. Step 5 checks the inverse as a natural S-linear map and one composite on every tuple. Step 6 computes the other composite on pure tensors in the presheaf tensor; it explains why the sheafification and coequalizer universal properties promote this to equality of sheaf maps. This replaces any erroneous assertion that all tensor sections are globally pure tensors.

For step 7 I checked the precise source statements again and corrected the draft citation: def-sfb-modobj-extension, rather than merely the overview definition, explicitly says that f is sent to the map induced by S tensor f. The extend/restrict adjunction explicitly gives u_M by insertion of the coefficient unit. These statements now support the two formulas actually used. The resulting matrix entry calculation and unit calculation are written out. Step 8 checks both zero-rank directions, the empty-sum inverse and zero rings. Also checked rank one (multiplication by a global coefficient), a rank-one composite (the order VT), arbitrary restrictions U' to U, and a nonflat coefficient map Z to Z/2; all equations use only unital ring laws and balancing, so no flatness has slipped in.

Against delivery-errors B–E: statements are self-contained, no child node was introduced, all non-elementary inputs are cited statements rather than facts hidden in their proofs, and citations.json contains literal excerpts from each one. The only substantial black boxes are existing definitions/constructions, already in the item's internal-module route. Elementary steps are the displayed finite-sum and balancing computations. The two application steps are marked non-elementary. Every step is shorter than 2000 characters, and there is no hidden independent lemma or clause moved into a new node. No disputed statement, source error or unfinished mathematical clause remains.

## What remains unfinished

Nothing in the stage-1 split. Server dry run and direct delivery are performed after this report is written.

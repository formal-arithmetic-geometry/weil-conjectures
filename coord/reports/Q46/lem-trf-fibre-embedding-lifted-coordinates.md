## Files written

- dag/nodes/sec-trace-formula/lem-trf-fibre-embedding-lifted-coordinates.json: statement, now split in five steps; Mathlib verdict no match. The original statement, statement dependencies, provenance and earlier searches are retained.
- citations.json: one verbatim statement quotation for each of the 18 step/node pairs.
- searches.jsonl: the prescribed search command's unmodified log.
- No new nodes; zero new Mathlib leaves. prepare.py is a sandbox-only construction helper.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by ampleness, fibre embeddings and lifted coordinates. AmpleImmersionAffineBase.lean:192 gives only a positive-power immersion over an affine base; it does not give fibre sections lifting to the family. No declaration found states this item's entire conclusion. The available project ampleness results are reference material, not evidence of the missing lifting result.

## WANTED

None. All sources used are present.

## Corrections and scope

The item was unsplit, with no proof and no saved attempt in this sandbox. There was no statement dispute or correction. Existing nodes already state both substantial inputs: lem-trf-affine-eventual-power-immersion and lem-trf-ample-fibre-section-lifting. Creating either again, or creating a node asserting the whole fibre-coordinate clause, would duplicate the DAG or merely rename the item. Intersection of finitely many lifting neighbourhoods and restriction is an elementary assembly step. An intersection of affine opens is not asserted affine: the affine-basis lemma supplies a smaller affine open.

Read SETUP.md's three levels, GOAL.md, the worker brief, stages/1-dag.md, delivery-errors.md B--E (including the duplicated historical copy), the chapter/unit records, and the current latest blueprint chapter, unit and lem-trf-local-term-locality text and proof. The latter contains the contracting-correspondence argument, while this item is an auxiliary lemma in its recorded fibrewise-ampleness branch. This split keeps that branch and its Stacks 0D2N route. No chapter or unit file is changed and no prohibited source is used.

Mathlib search: all five fresh queries were made through msearch.py with this item id; both semantic phrasings were read. Loogle and source grep returned no ampleness match. The Proj construction/valuative and structure-sheaf localization hits do not imply this line-bundle lifting statement. LeanSearch's germ-injective ring homomorphism lifting requires different objects and additional hypotheses; its other tensor and polynomial-law lifts are unrelated. Read Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:432--451 (fromOfGlobalSections) and Mathlib/AlgebraicGeometry/SpreadingOut.lean:245--260 (exists_lift_of_germInjective_aux). No false unavailability claim is recorded. Earlier item searches are retained as inherited provenance. Searches of all dag/nodes for 0D2M, 0D2N, ample-on-fibre and coordinate terms, and blueprint_refs.py searches for ample, embedding coordinates and 01NE, found no blueprint node giving the full item. Its same_as remains empty.

## Not duplicates

No new nodes were created. Existing eventual-power, lifting, projective-coordinate, properness and affine-basis statements are cited directly.

## Review by Q46

I read coherent.tex, lemma-ample-in-neighbourhood (0D2N), from its statement through the coordinate-lifting paragraph, and lemma-ample-on-fibre (0D2M). The source chooses a power beyond the cohomological lifting threshold and also sufficiently large to embed the fibre. I read morphisms.tex, lemma-finite-type-over-affine-ample-very-ample (01VT), especially (1) implies (6), and lemma-image-proper-scheme-closed (01W6). I also read constructions.tex, lemma-projective-space (01NE), its relative-base description after Definition 01NF, and lemma-projective-space-separated (01NH), together with schemes.tex, lemma-basis-affine-opens (01IT). There are no new-node sources to check.

Step 1 uses the statement of lem-trf-ample-fibre-section-lifting for a single bound applying to every section of every sufficiently high power; it does not take a uniform neighbourhood from that lemma. The statement of lem-pc-proper-base-change explicitly supplies properness after the residue-field base change. def-weil-proper-morphism includes finite type, and clause (1) of lem-weil-pbc-invertible-pullback-tensor includes invertibility after pullback. The statement of lem-trf-affine-eventual-power-immersion applies to a locally finite type scheme over any ring and gives every power above its bound, so max(a,b) satisfies both conditions. The fibre is not assumed smooth, reduced or flat. These are the exact cited statements, not constructions borrowed from their proofs.

Step 2 uses lem-weil-pbc-projective-space-proj-separated for projective space over the residue field, lem-weil-pbc-proper-to-separated for an over-field morphism from a proper source, and lem-weil-pbc-proper-immersion-closed for the resulting proper immersion. Each statement supplies precisely the assertion taken from it; no finite or quasi-finite replacement is used.

Step 3 uses the relative-projective-space standard charts and the twist's explicit frames. On D_+(T_k), T_k is the frame itself, so pulling back and applying the chosen isomorphism makes t_k a basis. This proves generation as sheaf surjectivity, using def-weil-pbc-generating-sections, without silently converting mere nonzero values by Nakayama. The transition e_l=(T_l/T_k)e_k checks the twist identification explicitly. I read lem-weil-pbc-projective-space-functor-of-points: it states every morphism arises from a generating pair and the uniqueness of the morphism for its pair, not merely full faithfulness. def-weil-pbc-morphism-to-projective-space-by-sections explicitly constructs the relative morphism as the pair of its structure map and its integral projective map. Thus the coordinate morphism is the existing closed immersion and the chosen twist isomorphism carries every coordinate correctly. This step is marked non-elementary because it invokes the universal property.

Step 4 reuses the section-lifting theorem independently on each coordinate; d is already beyond its bound. The item's proper/Noetherian/invertible/fibre-ample hypotheses exactly imply that theorem's hypotheses. I read both the tensor/pullback lemma and def-sc-tensor-pullback-power-comparison, including its normalized unit and recursion. The displayed local tensor formula checks that the comparison is the one fixed in the statement; it introduces no arbitrary automorphism of the line bundle.

Step 5 uses the full affine-opens-basis statement for an arbitrary open neighbourhood W. Finiteness makes W open. Restriction and pullback use the same section map v to 1 tensor v, so every restricted lift still has its specified fibre value. The other assertions have already been proved, making this step elementary apart from its cited affine-basis fact. There is no claim of generation away from the fibre and no shrinking argument that would require it.

I checked the returned-delivery criteria B--E against these statements. Every step citation has a verbatim quotation in citations.json. Each non-elementary fact is an existing cited statement, and no argument is hidden in a new statement-only node. All steps are shorter than 2000 characters. The off-unit proper base change, tensor pullback and projective universal-property results are generic tools, declared in split_report.tool_uses with their purpose. They do not replace a chapter or unit route.

Small cases: a nonreduced or disconnected proper fibre is allowed by the two main input statements. A zero-dimensional nonempty fibre still admits the same construction. r=0 gives one coordinate and one lifting neighbourhood. A negative lifting bound is not needed because both bounds are natural and the immersion bound is positive. s need not be closed: the fibre is taken over kappa(s), and no closed-immersion claim about Z_s into Z is used. An imperfect or finite residue field causes no issue in the affine-base immersion or section-lifting statement. No flatness is inferred, no intersection of affines is claimed affine, and the chosen power is positive. The excluded empty fibre is not needed for any nonemptiness inference about a coordinate index.

## Unfinished work

None in this one-level split. The existing cited nodes retain their independent downstream work.

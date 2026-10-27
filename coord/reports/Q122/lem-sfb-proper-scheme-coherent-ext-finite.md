## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-scheme-coherent-ext-finite.json: item split in six steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-coherent-derived-internal-hom.json: new statement-only prerequisite, Stacks 0D0C; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-scheme-coherent-derived-image.json: new statement-only prerequisite, the proper-morphism specialization of Stacks 0D0B; no Mathlib match.
- citations.json: one verbatim statement quotation for each of the eleven step/node citations.

Attachments: none. Searches under lean/WeilConjectures/ for the blueprint tag, finite/coherent Ext, coherent RHom, and proper coherent derived direct image gave no completed declaration stating the item or either new lemma. Existing affine derived-sections Lean was read as supporting source, without invoking any compiler. No Lean file was written.

WANTED: none. All sources used are available in literature/stacks-project/.

The item was unsplit and its statement agrees with perfect.tex, lemma-ext-finite, Tag 0D0D. Its statement, all hypotheses, all integer degrees, and structure-morphism A-action are preserved. Added the existing finitely-generated-module definition to its statement dependencies. The old Mathlib searches and all inherited provenance were retained; fresh searches, their actual answers, and the second phrasings are recorded in research-item.json, research-internal.json, research-image.json, and searches.jsonl. LeanSearch, LeanFinder, Loogle and grep all answered. The initial broad Ext grep also matched words such as extension, so a targeted logged AlgebraicGeometry grep was run and read. None is an exact match: HasExt asserts size, t-structure results assert support, and ordinary QuasicoherentData.pushforward does not give coherent derived pushforward. I read the latter's actual hypotheses at Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:298--336.

Nothing remains to finish for this one-level split. The two new lemmas deliberately remain unsplit for the queue. No declaration is reported proved in Lean, and no Lean sorry was introduced. No existing dependency was removed, no other node was edited, and no unit realization is appropriate: this auxiliary item is not the key statement of its unit.

## Not duplicates

lem-sfb-scheme-coherent-derived-internal-hom vs lem-trf-finite-module-target-rhom: the existing 0D0C node treats ordinary modules over a ring and a target concentrated in degree zero; the new node treats Zariski derived sheaf Hom of two complexes on a locally Noetherian scheme and produces coherent cohomology sheaves.

lem-sfb-scheme-coherent-derived-internal-hom vs lem-trf-bounded-above-coherent-rhom: the existing 0D0C node is the algebra problem in the source proof, on the one-object ringed site of a Noetherian ring; the new lemma is the scheme statement before affine localization and comparison with that algebra problem, not a one-line specialization of it.

lem-sfb-scheme-coherent-derived-internal-hom vs lem-trf-noetherian-quadrant-abutment: the existing 0D0C node concerns finite modules in a specified convergent spectral sequence; the new node concerns derived internal Hom on schemes and assumes no specified spectral sequence.

lem-sfb-scheme-coherent-derived-internal-hom vs lem-sc-sheaf-ext-coherent: the existing 0D0C node treats two coherent sheaves in degree zero and each sheaf Ext; the new lemma treats K unbounded below and L unbounded above, and also asserts a single lower bound for the whole derived Hom.

lem-sfb-scheme-coherent-derived-internal-hom vs lem-sfb-space-coherent-derived-internal-hom: that algebraic-space lemma is stated on the small etale site; the new lemma concerns Zariski module sheaves. Identifying these on the derived coherent subcategories is a comparison theorem, not a one-line specialization.

lem-sfb-proper-scheme-coherent-derived-image vs lem-sfb-proper-space-coherent-derived-image: the existing lemma uses small etale module sheaves on algebraic spaces; the new lemma uses Zariski modules on schemes, exactly the site of the item's source. No etale/Zariski comparison is assumed.

lem-sfb-proper-scheme-coherent-derived-image vs lem-pc-coherent-support-proper-higher-direct-image: the existing lemma treats a coherent sheaf and its higher images; the new lemma treats a cohomologically bounded-below complex with potentially infinitely many nonzero cohomology sheaves, including lower boundedness of the total derived direct image. Passing from the sheaf lemma needs the derived spectral-sequence/truncation argument.

Neither new lemma states finite global Ext or a clause of the item. The internal Hom lemma imposes no properness or affine base, while the image lemma contains no Hom at all. Both are the separate non-elementary lemmas explicitly used in the source proof, rather than elementary assembly facts.

## Review by Q122

I read perfect.tex at Tag 0D0D (lemma-ext-finite), including the displayed Ext/hypercohomology/Leray identities and the two cited lemmas. For the first new node I read Tag 0D0C (lemma-coherent-internal-hom), its complete statement and its reduction to the algebra problem using bounded Ext spectral sequences. For the second I read Tag 0D0B (lemma-direct-image-coherent-bdd-below), its proper-support hypothesis and its proof by truncation from lemma-direct-image-coherent. Proper f is a faithful specialization: a coherent sheaf has closed support and a closed subscheme of a proper scheme is proper over the base. Both new nodes use Zariski module sheaves, explicitly avoiding the different sites of the existing algebraic-space lemmas.

I compared the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md (3) with the inherited unit and chapter records. The latter describe the enclosing direct-image/compactification route. This item was created as the deformation-theory prerequisite in that route and its imported-ancestor field is null, also returned by blueprint_refs.py ancestor. I retained that value and its entire inherited via chain rather than inventing a blueprint identity. New nodes prepend this item to that chain and identify the exact 0D0D proof sentence they serve. Whole-blueprint searches for Ext finite, proper coherent, coherent internal, derived direct image coherent, and 0D0B/0D0C gave no blueprint node stating these facts. DAG keyword/tag searches were read and produced the distinctions above.

Step 1 uses exactly the statements of pqf-def-locnoeth (affine cover definition), lem-weil-pbc-affine-scheme-qcqs (quasi-compactness), def-weil-proper-morphism (finite type is part of properness), and lem-weil-pbc-finite-type-over-noetherian (Noetherian finite-type source). The base has its single Noetherian affine chart, so the latter lemma applies. I did not infer local Noetherianity merely from properness without checking the base.

Step 2 uses exactly the new internal-Hom lemma: X is locally Noetherian by step 1, both inputs have coherent cohomology, K is bounded above and E is bounded below. No perfectness or regularity is required. Step 3 uses exactly the new proper derived-image lemma: Y is Noetherian, f is proper, and G is bounded below coherent. Its conclusion is a coherent cohomology sheaf on the affine base, not yet a finite global Ext group.

For step 4 I opened lem-trf-open-ext-hypercohomology-comparison and cohomology.tex Tag 08DK. The node explicitly supplies arbitrary integer shifts, the open U=X, and naturality in the second derived argument. I used that stated naturality for the scalar endomorphism a id_E: postcomposition corresponds to multiplication of Hom-complex sections. This proves A-linearity of the comparison rather than mistaking its additive statement for a linear statement. The site of opens is a set and is small in a universe containing it and the module values; no large index category is introduced.

For step 5 I opened lem-pc-derived-sections-pushforward-comparison and the displayed equality in the proof of perfect.tex Tag 08D5. Its statement allows every scheme morphism and every unbounded input; U=Y makes its restricted objects the original ones. It explicitly says natural in E, which applied to each a id_G proves that its additive cohomology comparison respects the structural A-action. The proof does not cite an abstract Yoneda or adjunction statement for an unavailable comparison.

For step 6 I read pqf-lem-coherent-ft-locnoeth, lem-pc-affine-derived-sections-homology-comparison, and lem-weil-pbc-coherent-affine-sections-finite in full, and the existing affine-derived-sections Lean statement and docstring. The base is locally Noetherian, so coherence implies quasi-coherence and places T in the exact D_QCoh domain of the affine comparison. That comparison takes values in D(A) with the canonical global-section ring identification, so its H^n isomorphism is A-linear. The last lemma applies to the coherent sheaf H^n(T) on the affine open Y itself and gives finite generation over Gamma(Y,O_Y)=A. Inverse images of the finite generating set prove the conclusion; an additive isomorphism alone would not suffice.

These existing lemmas are recorded in split_report.tool_uses where their units differ: they are generic Ext/derived-section/affine tools used exactly as in 0D0D, and replace no unit-level route. I checked their dependency closures do not point back to this item or either proposed new node. Every non-elementary input is a cited statement, including the affine comparison and coherence-to-quasi-coherence implication. citations.json was generated from these opened statements and each quote was verified by literal substring comparison. No new definition or statement introduces an undeclared special notion. All new nodes are statement-only, their proof and proof_deps are empty, and their searched statements introduce all of their own objects.

I checked small cases: X empty or A the zero ring gives zero modules; K=0 or E=0 gives zero Ext; a point over a Noetherian ring recovers finite Ext of finite modules; shifts allow n negative and below the lower RHom bound without asserting nonnegative Ext alone. Neither new lemma asserts boundedness above of RHom or finite projective dimension, which would fail on singular Noetherian schemes. The pushforward lemma requires a Noetherian target and proper f, so it does not mistakenly assert coherence under arbitrary open immersions. All six non-elementary steps are under 700 characters, with no long inline hidden lemma. This addresses delivery-errors B1--B10, C1--C8, D1--D5 and E1--E7 against the actual statements and sources. No statement dispute or source error was found.

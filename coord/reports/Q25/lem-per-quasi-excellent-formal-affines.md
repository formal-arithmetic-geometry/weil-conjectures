# Q25: lem-per-quasi-excellent-formal-affines

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-quasi-excellent-formal-affines.json`: statement, split; no Mathlib match, original statement unchanged.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-adic-quasi-excellence.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-formal-completion-reduction-dictionary.json`: statement, unsplit; no Mathlib match.
- `citations.json`: verbatim statement quotations for every step/dependency pair.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint tag, quasi-excellence, and formal affines. The only quasi-excellent occurrence was explanatory prose in SixFunctors/Etale/Derived/Stability.lean. The formal-completion/coherent-formal-module declarations found concern module completions and do not assert quasi-excellence or this formal-scheme quotient dictionary. No compiler or Lake command was run.

## Literature wanted

WANTED: EGA I, §§10.8 and 10.10, completion of locally Noetherian schemes and coherent modules on affine formal schemes, for lem-per-formal-completion-reduction-dictionary. The archive is absent from literature/ega; no document was downloaded.

WANTED: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero: the non-embedded case, arXiv:0904.1592v2, §§2.4.1–2.4.3 and Theorems 2.1.6/2.1.8, for lem-per-quasi-excellent-formal-affines, archival copy. Read the already referenced online PDF at https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf, printed p.14, especially the paragraph that allows arbitrary characteristic by using Gabber instead of the characteristic-zero result. Its assertion that quasi-excellence survives completion is the route, not a replacement proof.

The actual Gabber theorem is available locally: Illusie–Laszlo–Orgogozo, Exposé I Théorème 9.2, printed p.17/PDF p.23. EGA III.1 §5.1.1 (printed p.149) locally recalls that completed coherent modules are coherent, but does not replace the full EGA I affine dictionary; the missing text remains explicitly wanted. The item's proof_origin is agent because its assembly and the omitted formal-geometric details are not presented as a verbatim proof from a local source.

## Corrections and scope

No statement dispute or alteration is needed. In particular, no characteristic-zero assumption, regular morphism, finite dimension, universal catenarity, or excellence has been added. I replaced the absent imported proof with a closed-fibre argument. It is insufficient to check only the originally chosen formal affines or their principal opens. The arbitrary formal affine is handled by its scheme quotient, which is an affine open of the fixed ordinary scheme X/I.

The existing lem-per-qe-complete-pair-lifting is restricted to Q-algebras, even though its source mentions general Gabber lifting. It cannot be cited for the current arbitrary-characteristic claim. This is why the general theorem is a new node. The formal dictionary contains no quasi-excellence and is a general infinitesimal-neighbourhood/affine-ideal comparison, rather than a new name for the item's quasi-excellence conclusion. It states all quotient levels and transition compatibility so that the change of ideal of definition is explicit.

The statement was seeded with all of its existing definition dependencies, and those remain. This is not the key node of sk-p-dl-a1-perverse, so no unit realization is changed. All new nodes inherit that unit and chapter and carry the exact ancestor/via chain obtained from blueprint_refs.py. Their place locates the formal-completion input in the ancestor's Step 3. The latest blueprint ancestor and its unit were read; neither introduces a different formal-completion route.

## Searches and duplicate audit

Read the current whole DAG by key words (quasi-excellence, completed rings, formal affines, ideal of definition, closed fibre, Gabber and source place), checked tags 0AHY/0GXU/0GXX/0GXY and relevant source references, and ran blueprint_refs.py searches for quasi-excellent, completion, Gabber, ideal of definition, coherent open ideal, adic completeness and formal completion reduction. No blueprint node states either new lemma. The existing items below are reused rather than reproduced: completion Noetherianness, completion modulo ideal, finite-type G-ring stability, quotient Noetherianness, G-ring affine-cover locality and J-2 affine-cover locality.

Each new node has two distinct LeanFinder phrasings, Loogle, LeanSearch and Mathlib grep, actually run through msearch.py and preserved in searches.jsonl and search-results.json. Both greps have zero hits for formal schemes/quasi-excellence. Semantic hits concern ordinary Scheme.IdealSheafData, ordinary locally Noetherian schemes, adic module maps, henselian pairs and local completion instances. Read the ordinary ideal-sheaf quotient code in Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean; it has an ordinary scheme as its input, not an arbitrary formal affine. Loogle returns scalar actions, transition-map identities and local completion instances, not either theorem. No search service was unavailable. The item itself was searched by all four kinds as well; its inherited searches have been retained.

## Not duplicates

lem-per-gabber-adic-quasi-excellence vs lem-per-qe-complete-pair-lifting: the existing iff assumes a Q-algebra; the new one-way theorem permits mixed and positive characteristic, which the item requires. Neither a generalization already in the DAG nor a clause of the formal-scheme item is being renamed.

lem-per-formal-completion-reduction-dictionary vs lem-per-formal-affine-principal-refinement: that node gives completed principal localizations, common refinements and local faithful flatness; it does not give the coherent open ideal or scheme quotients on an arbitrary formal affine chart. The new node compares all infinitesimal levels with their ordinary schemes and assumes no quasi-excellence.

lem-per-formal-completion-reduction-dictionary vs lem-per-regular-morphism-formal-completion: that theorem concerns preservation of regularity of a morphism over Q, with quasi-excellent source and target; it does not state the affine quotient dictionary. Here no morphism regularity or quasi-excellence is assumed or concluded.

lem-per-formal-completion-reduction-dictionary vs lem-per-quasi-excellent-formal-affines: the item concludes quasi-excellence of all formal-chart rings. The new input is the independent formal ideal/ordinary quotient dictionary, valid without quasi-excellence, and its higher infinitesimal quotients and compatibility are additional structure. The item still proves quotient quasi-excellence, cover locality and Gabber's hypotheses in separate steps.

## Review by Q25

I read Stacks formal-spaces.tex 0AHY (section-formal-schemes-EGA), the completion definition 0GXU, affine types 0GXX and local types 0GXY; algebra.tex 0316 (lemma-completion-Noetherian-Noetherian), 05GG (lemma-hathat-finitely-generated) and 00FN (lemma-Noetherian-permanence); more-algebra.tex 07QU (lemma-finite-type-over-excellent) and 07PV (proposition-finite-type-over-G-ring); properties.tex 0HA5 (lemma-locally-G-scheme) and morphisms.tex 07R4 (lemma-J). I read the local ILO theorem and the online Temkin paragraph quoted above. The Gabber node has exactly the local theorem's Noetherianity, adic completeness and quasi-excellent quotient hypotheses; the formal dictionary isolates the coherent-affine fact that Stacks' general completion paragraphs do not prove in full. EGA I is explicitly wanted, not claimed read. A future splitter of that new unsplit node can prove it via the affine equivalence between finite R-modules and coherent modules on Spf R: the completed ideal corresponds to an ideal J, quotient and powers correspond to R/J^n, and coherence plus openness makes J an ideal of definition. On the original charts this is C/(IC)^n = A/I^n. These local identifications glue and force compatibility with every affine presentation. This mathematical argument is retained here without inserting a hidden proof into the statement-only node.

Step 1 uses the exact statements of adic-completion-noetherian and adic-completion-mod-ideal: the ideal is finitely generated because A_i is Noetherian (the definition is explicitly cited). The new dictionary applies to a Noetherian X and coherent I as assumed. Its output is the glued formal scheme, its ideal and its ordinary quotient. Finite covering is immediate from the finite original cover and the equality of underlying closed-fibre spaces; no affine-intersection hypothesis is used.

Step 2 uses surjective-image-noetherian only for the surjection A_i to A_i/I_i. Finite-type-over-g-ring states exactly the needed finite type stability, and a quotient is generated by the empty list. The excellent-ring definition really includes J-2 for all finite type algebras: surjectivity makes the same finite generators work over A_i, so this part is written out rather than given another node. I checked that no converse descent of quasi-excellence is being assumed.

Step 3 uses precisely the two cited cover statements, whose full statements I opened: g-ring-affine-cover accepts any scheme and any affine cover; j2-affine-cover additionally requires local Noetherianity. The latter is established from the B_i before use, with pqf-def-locnoeth cited. I corrected an initially imprecise attribution: it is def-weil-pbc-g-ring itself that includes Noetherianity, so that definition is now explicitly cited instead of expecting the excellence definition to supply it. Together with J-2 this gives quasi-excellence on every affine of Z. This step makes no assertion that G-rings or J-2 are merely properties of the closed points.

Step 4 uses the new dictionary exactly as stated, taking n=1 and using its explicit completeness for J, not just for the original ideal K. The dictionary says that the ordinary open subset of Z is Spec(R/J); this supplies affineness, which does not follow merely from the topology of U. Step 3 applies to that affine of Z. R is Noetherian by the definition of formal affine in the item, and is J-adically complete by the dictionary, so all three hypotheses of Gabber hold. Gabber assumes no regular morphism, no Q-algebra, and no dimension bound. The new dictionary's ring J may differ from the chart's initial K; equality of adic topologies and completeness are in its statement, not silently inferred.

Step 5 is an elementary specialization of Steps 1–4 to a single initial chart. The construction can use that chart alone; it does not require silently assuming every affine ring of Spec A is quasi-excellent. I tested X empty, I=A, I=0, and nilpotent I. The unit ideal gives the zero ring and empty formal scheme; the zero ideal gives the original scheme; nilpotent ideals give a stationary tower. Positive-characteristic example A=F_p[t], I=(t) gives F_p[[t]], explaining why the Q-algebra-only lemma is insufficient; mixed-characteristic complete rings are also allowed by Gabber. In the dictionary, an empty U is represented by the zero ring, and for I=0 the assertion reduces to the ordinary affine open restriction. No reducedness was used, so nilpotents do not invalidate any hypothesis.

I checked delivery-errors B–E against these files: both new nodes are self-contained statements only, use single-escaped TeX, introduce every object, record real searches and source places, have empty proofs and proof dependencies, and make no new finished/Mathlib claims. Every citation's full exact statement is present in citations.json. The proof has five steps, none over 2000 characters. Three generic off-unit tool uses are declared in split_report rather than assigned to maintainer-owned tool_uses. There is no edge back to the item: none of the reused cover or completion results depends on this formal-affine lemma, and the new nodes have only definition statement dependencies. No SGA route, Lean change, build or repository write was made.

## Unfinished work

The two supporting statements deliberately remain unsplit for the next stage-1 workers, as required by one-level splitting. Nothing in the assigned item's assembly proof is left pending. Independent maintainer review remains the delivery process's next step.

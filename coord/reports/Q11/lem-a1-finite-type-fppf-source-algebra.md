# Stage-1 report: lem-a1-finite-type-fppf-source-algebra

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-finite-type-fppf-source-algebra.json: statement, split into six steps; no Mathlib match for tower descent. Its statement is unchanged mathematically; doubled TeX backslashes were normalized.
- dag/nodes/sec-purity-real-sheaves/lem-a1-fppf-integer-model.json: statement only, status unsplit, no Mathlib match; exact existing project declaration attached below. Its derived closed audit state is deliberately left to the maintainer's audit tool.
- citations.json: one entry for every step/node pair, with verbatim statement quotes.
- searches.jsonl: actual search-command output records. The node search entries preserve the exact tool/query and returned hit summary/digest; all services answered successfully.

One new node, zero new Mathlib leaves. The other six dependencies are reused Mathlib leaves/definitions. write_split.py is sandbox-local preparation only and is not part of the node delivery.

## Attachments

Algebra.FinitePresentation.exists_isPushout_faithfullyFlat belongs to lem-a1-fppf-integer-model, WeilConjectures/Mathlib/RingTheory/Finiteness/Descent.lean:195-217 (docstring 185-194).

I read the theorem and its proof. It assumes exactly finite presentation and faithful flatness of A → B, produces C finitely presented over Z, D finitely presented and faithfully flat over C, and an Algebra.IsPushout C A D B. This is precisely the canonical tensor-product isomorphism in the node; the already existing tensor-pushout node supplies its meaning. The single-universe source theorem covers arbitrary A,B by viewing them in their common maximum universe; C,D are asserted in that maximum, with no cardinal bound beyond it. No definition is being constructed with a sorry.

I also read local/sorry_map_slopmaster2_7d675a26.jsonl.gz: this declaration has s=false, ts=false at recorded lines 185-217. Following all its recorded project dependencies visits 86 declarations, none with s=true or ts=true. The newer source lines differ only in where the theorem signature starts relative to its docstring. The old full map has no entry for this declaration. The exact model is therefore an attachment candidate supported by the explicit later 7d675a26 audit, not a Mathlib leaf. I did not assign a derived closed state myself.

No exact source-library declaration for the item was found by its blueprint tag, its id, or finite-type/faithfully-flat/descent variants throughout WeilConjectures. The nearby Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat assumes B finitely presented over R, which the item does not. It cannot be attached to this item.

## WANTED

None. All sources used are present in literature/.

## Corrections and source comparison

The imported item is true exactly as written: descent.tex, Tag 0367, lemma-finite-type-local-source-fppf-algebra, lines 4351-4382. It imposes no Noetherian hypothesis and neither does this split. No STATEMENT-DISPUTED issue was found.

Stacks says to enlarge the model to contain finitely many coefficients. The proof spells that out with a finite polynomial algebra P over R tensor_Z C mapping to A; injectivity of the model map into A is not assumed or needed. This is a concrete choice of the finite enlargement in 0367, not a replacement route. We need P finite type over R and P → Q faithfully flat; we do not use P Noetherian or require any new finite-presentation conclusion for P. Every tensor map and its inverse is written explicitly. Reflecting surjectivity uses the exactness-reflection clause of the actual definition node, rather than citing a flatness definition as a tensor-exactness theorem.

The chapter and Rankin unit were read. The node is not the key node of that unit. This is its existing auxiliary schemehood branch below lem-a1-affine-hc0, via lem-a1-lft-flat-lfp-source-descent and the affine ring input to 02KL. No chapter/unit metadata or realized fields were changed. All reused external nodes are definitions or Mathlib leaves, so no off-unit theorem/tool permission is needed.

## Not duplicates

lem-a1-fppf-integer-model vs lem-weil-pbc-flat-finite-presentation-model: the existing node gives a merely flat finitely presented integer model of a flat finitely presented map; it does not make the model faithfully flat even when the final map is faithfully flat. The new statement includes precisely that additional model condition, using Stacks 034Y and the independently proved declaration. The latter declaration is not assigned to any existing node by the DAG declaration/name search.

lem-a1-fppf-integer-model vs lem-a1-finite-type-fppf-source-algebra: the model lemma assumes no ring R or finite-type condition on B over R and concludes no finite-type condition on A over R. It supplies a smaller approximation tool; the finite coefficient selection, tensor comparison and quotient generation proving the item stay in the item's six steps.

Whole-DAG searches for 034Y, its Stacks label, the declaration, faithful-flat model terminology and the broader finite-presentation approximation terminology found no duplicate. Whole-blueprint searches for 034Y, faithfully flat model, integer model, finite-type-local-source and faithfully were inspected. The 16 faithfully hits concern contraction, weakly etale refinements, or field-extension properties, not this integer model. The item has no second blueprint statement, so same_as remains empty. New ancestry is the item's full ancestry with the item prepended to via, and the exact 0367 first-sentence/034Y absolute-model substep is identified in from.place.

## Review by Q11

I checked B–E of coord/delivery-errors.md with the node statements and source text open. The new node is a self-contained existential statement without proof, proof dependencies or a hidden proof sketch. Every nonbasic notion in it cites the corresponding existing finite-presentation, faithful-flatness or algebra-tensor node. Its Stacks tag 034Y and label were verified against tags/tags and algebra.tex:47469-47519; I read both the absolute construction and the last general-base paragraph. Its source-library proof and sorry audit are recorded above. Mathlib searches for both model phrasings, plus Loogle and source grep, found base-change and fixed-base descent rather than the approximation theorem. Smooth.exists_subalgebra_fg requires smoothness and cannot supply this model. For the item, I read Mathlib/RingTheory/Finiteness/Descent.lean:76-105: its finite-type tensor-product descent is base descent, not the source-tower descent here. The finite-presentation scalar restriction hits also have the wrong conclusion. Neither is incorrectly declared a leaf.

Step 1 uses only the new integer-model statement. Its input is the exact faithfully flat/finitely presented map A → B in the item. The output gives the specified maps, canonical isomorphism and C finite presentation needed later; no assertion is taken from a dependency's proof.

Step 2 uses the existing tensor-pushout statement for the product map R tensor_Z C → A, the finite-presentation definition for finitely many generators of C, the module-tensor statement's explicit finite pure-tensor generation, and the finite-type definition for the conclusion. I opened all four statements. The polynomial description is a direct expansion of a finite sum of tensors and uses no theorem about Noetherian rings or base-change finite presentation.

Step 3 uses the finite-type definition to select b_j and the module-tensor statement to obtain the finitely many coefficients a_jk. P is an explicit finite polynomial algebra and phi is evaluation at those coefficients. Its finite generation over R is verified by expanding polynomial coefficients in the already given generators of T; this is an elementary step, not a new algebra lemma. There is no claim that an arbitrary subalgebra of a finite-type algebra is finite type.

Step 4 uses the existing faithful-flat-base-change statement with its R=C, S=D and R'=P. Its hypotheses are exactly those of step 1 and the constructed C → P; the node explicitly concludes faithful flatness for the first-factor module structure, as required later. The tensor-pushout statement constructs q with the stated pure-tensor formula. Its surjectivity is elementary from the displayed preimages of b_j and containment of the R-image, using precisely the finite-type definition. No Noetherian or injectivity hypothesis enters.

Step 5 cites the tensor-pushout universal property and the module-tensor statement for its explicit inverse maps and pure-tensor generation. They are maps between the right rings: A tensor_P (P tensor_C D) and B = A tensor_C D. The displayed balancing identity checks the inverse on the P factor, and the C balancing is inherited from C → P → A = u. The map Q → A tensor_P Q sends z to 1 tensor z and becomes q. The faithful-flat definition is unusually strong enough to state preservation AND reflection of exactness for arbitrary module complexes; applying its literal statement to P → A → 0 reflects exactness at A and therefore surjectivity. Tensor with the zero module is zero immediately from its universal property. This takes no unrecorded general tensor-exactness theorem. This step is routine and elementary from the three quoted statements, with the comparison itself spelled out, rather than hidden behind an identification lemma.

Step 6 uses the finite-type definition and actual surjectivity to lift an arbitrary a and apply phi to a polynomial expression. It is the written two-line quotient argument, not a new node for finite type of a quotient.

Every cited statement was opened, and citations.json contains verbatim parts of those actual statements (full statements to avoid truncating an important hypothesis), one for every step/node pair. The proof dependency list equals their union. No dependency leads back to the item: the only new node depends on the existing definitions and tensor Mathlib leaf, and all other citations are leaves/definitions. No new node restates a clause of the item or is proved inline and then invoked circularly. No step is longer than 2000 characters; the longest is the explicit tensor comparison/exactness argument at 855 characters.

I tested the zero-ring cases: if B=0, faithful flatness forces A=0, and the proof still works; faithful flatness of P → Q in step 4 makes a zero Q force P=0 when that case arises. Empty generator sets and empty sums are allowed: P=T with zero added variables, and the image of R already generates B if there are no b_j. The identity A=B, polynomial faithfully flat extensions, noninjective R → A, and non-Noetherian R are included. For the model node itself, identity maps use C=D=Z, and the zero map of the zero ring has a zero model; no nonzero-ring hypothesis was silently used. No SGA source or alternate purity route occurs.

## Unfinished work

No mathematical part of the split remains. The maintainer's independent review and derived closure/attachment update remain part of the normal delivery process. The model node itself has no new proof because the exact source-library proof already exists. Server dry-run and push results follow below.

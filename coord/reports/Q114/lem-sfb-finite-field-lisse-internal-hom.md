# Q114: lem-sfb-finite-field-lisse-internal-hom

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-lisse-internal-hom.json: statement, split; no Mathlib match. Five proof steps, no new nodes, no Mathlib leaves.
- citations.json: one verified verbatim statement excerpt for every node cited by every proof step (11 entries).
- report.md: this report. searches.jsonl is the unmodified output log of the required search command.

## Attachments

None. I searched the live project's WeilConjectures tree for the exact blueprint tag and for lisse/locally constant internal Hom, finite-field duals and cohomology. Etale/Derived/LisseFieldDual.lean concerns the small etale coefficient category and coefficient duals of complexes, not this pro-etale statement for an arbitrary constructible second variable. WeilSheaf/Dual.lean and WeilSheaf/Fourier.lean concern adic algebraic-closure coefficient sheaves/Weil structures. None states every clause of this item with its finite constant coefficients and same interval. Upstream sorry declarations were not treated as completed proofs.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The mathematical statement, including the finite-field, Noetherian, local-model and interval hypotheses, is unchanged. I added definition citations for cohomology sheaves and ordinary sheaf tensor to the text and statement dependencies. There was no preexisting sandbox item, report or search history to repair. The repository's earlier Q54 search records and all other imported fields are retained; four searches actually run by Q114 were appended.

Bhatt--Scholze Lemma 6.7.13 has quasi-excellence and coprimality hypotheses for its general internal-Hom theorem and proves it by closed-support devissage. It is context for this item, not the source of the sharper same-interval assertion for a locally free degree-zero source. The proof here is explicitly agent-written: the finite-free local calculation from Stacks sites-modules.tex Tag 0FNY, followed by exact Hom and its K-injective cohomology computation. It does not invoke the general finiteness theorem with absent hypotheses. No SGA source is used.

The fixed chapter and the two steps of sk-def-sfb-dc-restricted-functors were read. The item is a subsidiary finite-coefficient calculation under that unit's step 1, through lem-sfb-finite-field-internal-hom-finiteness and ancestor lem-sfb-dc-hom-preserves. It is not the unit's key node, so no unit record was written. Generic off-unit statements are explicitly declared in split_report.tool_uses.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Whole-DAG searches for finite locally free/projective ringed-site Hom and exactness, together with whole-blueprint searches for finite projective, locally free, internal Hom, finite local system, locally constant sheaves, tensor cohomology, lisse internal and Hom from, were read. Existing lem-sfb-ringed-site-perfect-duality and lem-sfb-ringed-site-strict-perfect-hom give much more general perfect-complex formulas; they were inspected but are not needed by the direct degree-zero argument. The needed restriction, covering detection, finite-local-model pullback and tensor comparison statements already exist and are cited. No elementary basis identity, finite direct-sum exactness fact, or clause of this item was made a node.

## Mathlib searches

I ran the required Q114/item search command with LeanFinder (derived Hom from a finite-dimensional local system and preservation of its cohomological interval), Loogle ("SheafOfModules", "ihom"), grep (constructible/locally constant with internalHom/ihom/RHom), and LeanSearch (exact derived sheaf Hom out of finite locally free modules and dual tensor cohomology). Thus a second mathematical phrasing was tried. All four services returned successfully. Finder gave condensed locally constant functors/closed structures; Loogle and grep gave no hits; LeanSearch gave dualTensorHomEquivOfBasis, dualTensorHomEquiv, underived sheafHom and module-sheaf structure/pullback results. I read LinearAlgebra/Contraction.lean lines 155-180 and 272-285 and the sheaf-Hom declaration locations. The module-level dual-tensor equivalences do not state a derived sheaf cohomology or constructibility result; this item cannot be a one-line specialization of them. Exact queries, result summaries and verdicts are in mathlib_searches and the untouched command log.

## Review by Q114

I read Bhatt--Scholze 6.7.13, including its proof, directly from the locally installed PDF. For the actual calculation I read sites-modules.tex Tag 0FNY (example-dual), Section 03DH and Tag 03DJ (extension-by-zero exactness and slice formalism), Tag 093R (pullback of locally constant sheaves), and the internal-Hom construction in sites-cohomology.tex, also inspecting 08JH/08JJ while checking whether the general existing perfect-duality nodes were needed. There are no new nodes requiring separate sources. I opened the statement of every node actually cited, and generated citations.json only from literal substrings of those statements.

Step 1 uses the locally constant definition's explicit slice trivializations, the sheaf-Hom definition's maps on every localized site, and the tensor definition's sheafified section tensor. A basis of each finite-dimensional vector space gives a finite free sheaf. The inverse evaluation formula is written explicitly, with both composites following from the basis expansion. Hence it proves the needed dual and Hom comparison rather than presupposing a general duality theorem. Local inverses glue by uniqueness; no choice of transition matrices is hidden. The resulting dual models are finite-dimensional, including dimension zero.

Step 2 applies lem-pur-site-restriction-module-adjunction-exact only to its stated exact slice restriction functor. In each slice Hom out of the free finite rank module is a finite direct sum, so images of short exact sequences are exact. The kernel, middle homology and cokernel therefore vanish on the cover. Clause 1 of lem-cbc-proetale-stalk-conservative states precisely the covering-family vanishing criterion used. Its additional geometric-stalk assertions are not used. lem-sfb-proetale-object-inverse-image-restriction supplies exactly the comparison of the module inverse images in that criterion with the slice restrictions in the computation. Its hypothesis holds because each U_i is an object in the given pro-etale covering; A is a finite commutative ring. This establishes exactness, not merely left exactness, without asserting sectionwise surjectivity.

Step 3 uses the fixed K-injective construction actually stated in def-pur-derived-internal-hom. Its first argument is L in degree zero, so the Hom complex has terms Hom(L,I^r) and differential Hom(L,d). Step 2 shows this additive functor preserves the kernel, image and quotient defining each cohomology sheaf; those are the objects in def-weil-derived-cohomology-sheaves. Applying step 1's inverse evaluation gives the exact desired isomorphism, with the cohomological sign unchanged. Naturality follows from functorial kernel/image maps and evaluation, and is recorded explicitly. No assertion about global Ext or acyclicity of sections replaces internal sheaf Hom.

Step 4 takes the input's finite stratification. def-weil-proetale-constructible-sheaf supplies its locally constant finite values and locally closed constructible strata. lem-exc-proetale-pullback-locally-constant applies to the stratum morphism and L dual, which step 1 proved to have finite local models; it explicitly preserves those models. lem-weil-pbc-ringed-topoi-module-pullback-tensor is for arbitrary ringed-topos inverse images and identifies the pulled-back ordinary tensor with the tensor of the two pullbacks. On the common refinement the explicit finite-free tensor calculation gives W to the finite direct sum power d. These are finite-dimensional A spaces and finite sets, so precisely the same strata witness constructibility. No etale/pro-etale coefficient equivalence, local Noetherian reduction, or derived-complete tensor is being assumed.

Step 5 uses the formula already proved: tensor with zero is zero outside [a,b]; constructibility holds inside it by step 4. I tested S empty, zero L, rank varying between cover members, N zero, a=b and arbitrary integer shifts. There is no positivity or invertibility hypothesis on char(A) relative to S in this local calculation. For a point with L=A^d the answer is N to the direct-sum power d, agreeing with the formula. No uniform rank or new cohomology bound is needed. The local-basis arguments remain elementary steps; the non-elementary covering, restriction and pullback facts have existing cited nodes. All five steps are under 2000 characters, with no concealed auxiliary comparison or new lemma.

Against delivery-errors B--E: the item is self-contained, existing definition dependencies are retained, the new notation has explicit definitions, JSON uses ordinary single TeX backslashes, and no new unsplit nodes or leaf claims were invented (B). Every non-elementary input has a citation to a statement that supplies it, with its hypotheses verified above and verbatim evidence in citations.json (C1/C4); the proof does not use the proof of a cited node (C3). The item carries the argument itself; it is not relabelled as a new node, and there is no circular dependency (D). Empty and zero cases, source hypotheses, coefficient categories, naturality, and the actual cohomological degree have been checked (E). No statement dispute was found. The only repairs made while drafting were to add the two missing definition citations and to make explicit the covering-inverse-image/slice comparison rather than silently equating the two.

## Unfinished work

None in the stage-1 split. Server preflight and delivery are performed with the prescribed delivery command; no Lean files were written and no compiler, Lake or local validation script was run.

# Q40: lem-sfb-ring-square-zero-extension-classification

## 1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ring-square-zero-extension-classification.json: statement; split using existing DAG statements, with no new nodes and no new Mathlib leaves. All original metadata and statement dependencies retained; the correction to the extension's typing is recorded below.
- citations.json: one checked verbatim statement quotation for each of the 29 step/node citations.
- searches.jsonl: five searches actually run for this item; the two semantic phrasings, Loogle, LeanSearch and Mathlib grep all returned results. The inherited searches remain in the node, and the new searches are appended with their real result records.
- report.md: this report.

## 2. Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and extension/classification/cotangent keywords. Existing derivation, universal thickening and trivial-extension declarations do not state the classification with all its clauses. The Mathlib hits concern the kernel of the naive differential (Algebra.Extension.H1Cotangent), conormal modules, or derivations relative to an existing lift; none classifies arbitrary square-zero extensions by derived Ext. Read RingTheory/Extension/Cotangent/Basic.lean (cotangentComplex and H1Cotangent), RingTheory/Derivation/ToSquareZero.lean (the lift/derivation equivalence), and the displayed search signatures, rather than treating their names as matches.

## 3. WANTED

None. All mathematical sources used are available in literature/stacks-project/.

## 4. What needed repair

The item had no proof. Its statement is correct after clarifying the typing of an extension (see below). The Stacks functoriality lemma explicitly omits a compatibility verification, but its following remark supplies the presentation argument; steps 9 and 10 write out that argument rather than citing the omission. The full-complex assertion requires truncation, not an assertion that the full cotangent complex has only two terms. Steps 2 and 3 supply that derived calculation using existing nodes. The existing two-term boundary node only asserts exactness at the middle: its statement alone does NOT supply surjectivity. Step 3 separately proves surjectivity from the triangle and projectivity of the arbitrary-rank free module V. The Baer assertion follows by actual addition of the two conormal representatives (step 8), not by an unstated additive-classification theorem.

The inherited blueprint.from.node is null, and blueprint_refs.py ancestor reports None. I preserved this maintainer-owned ancestry field. Its existing from.place specifies the entire supporting route down from det-thm-sf-ctf-stability-direct-images proof (3), and the split_report explains that role. Read the current latest blueprint proof at sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md and the chapter and unit records. This algebra input supports the already inherited deformation-theory route; no change to the chapter or unit is proposed. Searches of the whole blueprint for cotangent, square-zero and extensions of algebras found no node stating this item. same_as remains [].

## 5. Unfinished work

None within this one-level split. The pre-existing non-leaf dependencies remain their own items. No Lean file was written, no compiler or build was run, and no repository or launcher file was changed.

## Not duplicates

No new node was created, so there are no new/existing node pairs requiring distinction. Reused lem-trf-lci-naive-cotangent-model instead of making another 08RB comparison node, lem-sfb-two-term-derived-hom-boundary instead of another two-term Hom exactness node, and the existing projective Ext and triangulated exactness leaves instead of restating their consequences.

## Review by Q40

I read defos.tex from the setup of the extension diagram through lemma-huge-diagram (08S5), lemma-choices (08S7), lemma-extensions-of-algebras (0GPT), remark-extensions-of-algebras (0GPU), lemma-extensions-of-algebras-functorial (0GPV) and its following remark (0GPW). I verified their labels against tags/tags. I also read cotangent.tex lemma-relation-with-naive-cotangent-complex (08RB), derived.tex lemma-representable-homological (0149), remark-truncation-distinguished-triangle (08J5), lemma-negative-exts (06XS), and algebra.tex lemma-characterize-projective (05CF). There are no new statement-only nodes needing separate source review.

For step 1 I checked the polynomial universal property and the universal differential definition in the cited definition nodes. The basis formula for arbitrary, possibly infinite generators is explicitly justified by differentiating finite monomials. The cited cotangent comparison states the actual canonical truncation isomorphism for arbitrary polynomial presentations, not just an lci comparison under regularity hypotheses. Thus it applies here without flatness, finite presentation or regularity.

For step 2 I read the standard t-structure definition and the orthogonality and contravariant Hom exactness statements. The two required vanishing groups involve T and T[1], whose upper bounds are -2 and -3; the target M[1] has lower bound -1. These are strict separated bounds, with the correct cochain shift convention. Both kernel and cokernel of precomposition vanish. No assertion about the discarded lower cotangent cohomology was used.

For step 3 the boundary node explicitly supplies the map h to h[1]q, its kernel, its additivity and naturality. Its Ext-zero clause applied to [0 -> J/J^2] supplies the ordinary/derived Hom identification. The exactness leaf applied to the rotated two-term triangle gives surjectivity only after the projective Ext criterion makes Hom(V,M[1]) zero. The projective definition permits arbitrary direct summands of arbitrary free modules, so there is no finite-rank assumption. def-pc-ext defines precisely the derived Hom groups appearing here.

For step 4 polynomial evaluation lifts the generators, and the difference calculation explicitly verifies the derivation rule in the square-zero kernel. The universal property of differentials turns this difference into theta, while the boundary node kills theta d. An isomorphism of extensions fixes M and A, so transporting a lift does not change its conormal map.

For step 5 I checked the multiplication in def-sc-trivial-square-zero-extension and computed the ideal property of the graph, its zero intersection with M, and the exact kernel of the quotient to A. This is one concrete quotient-ring argument with all checks displayed, not a hidden general existence theorem. For step 6 the displayed surjection P direct-sum M -> E has exactly that graph as its kernel, giving reconstruction. Equal classes differ by theta d by the actual kernel assertion of the boundary node. Shifting every lifted generator by theta(dx_a) changes the conormal map by exactly theta d. This verifies injectivity and the sign of the graph. The split extension has representative zero.

For step 7 I checked that the antidiagonal is an ideal even when u is neither injective nor surjective. The quotient contains N injectively, has quotient A, and the explicit map on pairs proves its pushout property. Its chosen lift evaluates relations to u h, so the naturality clause of the boundary node proves the claimed coefficient map. Step 8 is elementary from that construction and additivity of the boundary node: paired lifts give (h1,h2), and addition gives h1+h2. It does not use a separate Baer theorem.

For step 9 I checked that the standard polynomial map sends each relation into the correct target kernel. The explicit lift to the ring fibre product evaluates it to h_s composed with the conormal map. The existing comparison node states naturality for arbitrary ring squares, including restriction along the target ring map. The boundary node states naturality for the resulting commutative differential square. These are exactly the two compatibilities used, so this proves the specified restriction/precomposition map, without replacing it by an unsupported flat base-change isomorphism.

For step 10 I checked the map from E^u to A fibre-product_B F on each pair and on every antidiagonal generator. Its kernel and quotient maps are identities. The injectivity/surjectivity argument is written out, and its converse is the indicated composition; neither uses an uncited five lemma or classification theorem. The classification invoked here was proved in steps 3--6. This is an elementary diagram chase from those earlier steps. For step 11 I read the full statement of lem-trf-cotangent-resolution-coherence: it explicitly asserts strict identities and compositions of the standard maps. Together with the natural comparison and boundary this proves the exact composition assertions. The two cotangent statements outside this unit are declared as generic tool uses in split_report, rather than silently treating them as unit-route replacements.

I tested the construction when M=0 (the graph quotient is P/J=A), when u=0 (the pushout has conormal map zero), when u is the identity, when f is the identity, and for a split extension. For R=A, the structure map gives a splitting of every extension, as the zero relative cotangent class requires. With A=0, any unital A-module is zero and the construction returns the zero ring; it does not invent nonzero square-zero unital extensions. For R=Z, A=F_p, E=Z/p^2 and M=F_p, h(p)=1 while d(p)=0; hence it is not a coboundary, confirming that non-split and non-flat cases were not inadvertently removed. Infinite generators cause no infinite sums: every polynomial and every relation has finite support. No step exceeds 2000 characters; all quotient and compatibility calculations are explicit, with no standard auxiliary lemma hidden in a long paragraph. I corrected initially mistaken draft labels for the huge-diagram/choices lemmas to 08S5/08S7 before delivery.

## Statement typing clarification

STATEMENT-DISPUTED: the imported wording “an exact sequence ... of R-algebras” is literally ill-typed at M. An arbitrary A-module is not a unital R-algebra. For example, with R=A=Z and M=Z, the kernel in the split extension has zero multiplication, so it has no multiplicative identity although its additive group is nonzero. Stacks 0GPT intends an extension of algebras with a square-zero ideal identified with the given module. The statement now explicitly says exactness is on additive groups, E is an R-algebra, p is an R-algebra map, and i identifies M with its square-zero ideal. This changes no mathematical hypothesis or conclusion; it makes the intended source meaning precise.

The first dry run rejected three quotations shorter than forty characters. They were replaced by the complete orthogonality and Hom-exactness statements; the next dry run passed. The final dry run includes the typing clarification above.

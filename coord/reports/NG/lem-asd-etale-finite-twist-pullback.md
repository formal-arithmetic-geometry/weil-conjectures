# Stage-1 report: lem-asd-etale-finite-twist-pullback

## Files written

- dag/nodes/sec-smooth-purity/lem-asd-etale-finite-twist-pullback.json: statement, split into eight steps; no Mathlib match for the complete item.
- citations.json: each step/node pair has a verbatim statement quotation.
- No new nodes, definitions or Mathlib leaves. No unit record is changed, since this item is not the unit's key node.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 by the blueprint ID, finite twists, Tate twists and roots of unity. Smooth/Conventions.lean defines HasTateTwist with comparison and local-constancy fields as parameters; it expressly says that the concrete roots model is not constructed there. AlgebraicGeometry/Sites/RootsOfUnity.lean proves trivialization over a field with a supplied primitive root, not arbitrary-scheme pullback, arbitrary coefficients, signed powers, coherence and exponent independence. Neither is an exact attachment. The read-only master is reference material, not evidence of completion.

## WANTED

None. The source calculations used are available in literature/stacks-project/.

## Corrections and scope

The statement is retained, including arbitrary commutative A, arbitrary schemes and morphisms, all signed twists and shifts, and the entire unbounded ordinary small-etale derived category. No STATEMENT-DISPUTED was needed. The source's finite-ring input is applied only to Z/m, then extended to arbitrary A by a written tensor-unit calculation; no finiteness or flatness assumption on A is introduced.

The previous item had no proof. The imported source references alone do not prove the dual, derived coherence and divisible-exponent clauses, so the proof origin is agent: the Stacks calculations are combined with explicit arguments. In particular 03Q1 (4) gives pullback of representables, not arbitrary internal-Hom pullback. Negative powers are handled only for locally free rank-one objects by the evaluation calculation.

The blueprint ancestor is prop-asd-smooth-base-change, proof paragraph 2, its ordinary inverse-image and twist comparison in the projective-line and affine-space models. Read its master text and the unit sk-prop-sf-cbc and chapter sec-smooth-purity. The item supplies that comparison without changing the unit or chapter route. Generic off-unit etale-site, root-algebra, tensor, and Yoneda lemmas are declared in split_report.tool_uses. They supply infrastructure; no compact-support or duality step of the unit is replaced.

## Not duplicates

No nodes were created. DAG and whole-blueprint searches for roots of unity, finite Tate lines, Tate twists and pullback of roots found the existing finite-line, pro-etale roots, and Weil-twist nodes. The finite-line lemma is reused at Z/m. The pro-etale roots comparison is restricted to isomorphisms of schemes, and the Weil compatibility lemma is in the adic/Frobenius coefficient setting; neither says this ordinary-etale arbitrary-pullback item. same_as remains [] because no blueprint node states all its clauses.

## Mathlib searches

Every new search was made using msearch.py and is appended to the item's existing search records. Ran LeanFinder twice with different natural-language descriptions, Loogle for rootsOfUnity and for Sheaf/pullback, and grep for twist/sheaf/roots patterns and rootsOfUnity/pullbackObjFreeIso. LeanSearch returned Internal Server Error and is recorded unavailable. Read the returned signatures, RootsOfUnity/Basic.lean and ModuleCat/Sheaf/PullbackFree.lean. The algebraic roots results do not construct the small-etale local system; pullbackObjFreeIso is about generic free sheaves and assumes a final site functor; condensed monoidal results use another site. None states all clauses of this item or specializes to it in one line. No unrun searches are recorded.

## Unfinished work

None at this one-level split. All cited nodes already exist; their downstream proof work is not claimed complete here. The sandbox is for a fresh second reader, not a delivery push.

## Review by NG

I read Stacks etale-cohomology.tex section-kummer (03PK), its root-cover calculation in lemma-kummer-sequence (03PL), and lemma-stalk-pullback (03Q1), including the representable clause (4). I also read groupoids.tex example-roots-of-unity (040M), sites-modules.tex lemma-tensor-product-pullback (03EL), section/internal Hom definitions (04TT/03EM through the cited definition), and sites-cohomology.tex lemma-pullback-tensor-product (07A4) and lemma-pullback-K-flat (0G7E). These distinguish representable roots, ordinary module tensors, and unbounded derived tensors. No new node sources require checking.

Step 1 uses the statement of lem-asd-finite-etale-twist-line only: Z/m is a finite commutative ring killed by m, and m is invertible on T. Its r=1 conclusion trivializes mu_m after the tensor-unit identification. The tensor and Hom definitions then give the displayed local bases for arbitrary A and every signed power. I do not use the primitive-generator construction buried in that node's proof. The scalar map exists exactly because mA=0.

Step 2 applies lem-sbc-root-split-away-cover-etale with g=1 and positive n=m; D(1) is the whole root spectrum. The affine-spectrum statement supplies ring-map correspondence. Polynomial-quotient maps are evaluated at t, whose image is automatically a unit. The representable-sheaf statement glues the local maps on arbitrary objects; fibre products identify their base changes. The inverse-image-representable statement applies because the root scheme is etale, not merely an arbitrary T-scheme. During self-review I noticed that its statement supplies an isomorphism without specifying its normalization; I added the existing general Yoneda evaluation node and the natural-Hom-bijection recognition node, and the explicit identity-point computation, so the invertible map is the actual roots comparison. Those two nodes state precisely these bijections/recognition facts, not merely full faithfulness.

Step 3 uses the algebraic-structures node to pass from sets to abelian inverse image with the same units. The cover-base-change node supplies the cover of T', the restriction node and composition-unit node identify the restricted comparison, and cover detection then proves invertibility. Each of those statements was opened and quoted. Composition is checked by equality of ring restriction maps on root sections, with the composition units explicitly identified; powers commute with those same ring maps.

Step 4 checks both hypotheses of the generic monoidal inverse-image node using the finite-limits and continuous base-change nodes. The sites are taken small in a universe below that of sheaf values, as required there. The constant coefficient exactness node supplies both constant-ring comparison and equality with module pullback. The generic monoidal node initially gives tensor over Z; the proof explicitly descends it through the balancing coequalizer to tensor over Z/m and A. This avoids silently treating its absolute tensor assertion as a relative tensor assertion.

Step 5 uses only the Hom and tensor definitions and previously established comparisons, plus the statements that the trivializing cover survives pullback and covers detect isomorphisms. The dual functional is evaluated on a single local basis, and the canonical Hom comparison sends that dual basis to the dual of its image. Thus internal Hom is pulled back only in this finite locally free situation. The inverse dual of c_{v,a} has the correct direction. Step 6 checks signed tensor maps under a change of basis e -> u e, where the scalar is u^a for every signed a, and checks composition of the negative comparison by its defining evaluation. This carries the argument itself, with no new node restating a clause.

Step 7 uses the exact constant-coefficient inverse-image statement and the unbounded tensor-pullback statement, not a bounded-below theorem. Exactness identifies Lv* with degreewise inverse image. The tensor-pullback node permits K-flat resolutions with flat terms and preserves them; the tensor-complex definition fixes direct sums and signs. The sheaf monoidal identity/composition assertion makes the total-complex diagrams commute, and additive inverse image preserves the shift sign. This checks actual derived maps rather than equality inferred from geometric stalks.

Step 8 is the arithmetic calculation inside a cyclic local trivialization supplied by Step 1 at Z/m'. The subgroup killed by m in Z/m' is q Z/m' for m'=qm. With the induced generator zeta^q of mu_m the power map is reduction of residues, so after tensoring with A its coefficient map is the identity, even when q is zero in A. The tensor and Hom definitions give the positive and inverse-dual extensions, and the cover-detection statement tests the original line comparison. This corrects the possible mistaken reading that the final line map is multiplication by q.

I tested m=1 (which forces A=0), the zero ring, empty schemes, the identity and a composite morphism, negative a, a=0, arbitrary shifts, and A=F_2 with m=2,m'=4. In that last case the map is indeed identity in compatible bases, not the zero map from multiplication by 2. No nonzero-ring, Noetherian, finite-A, boundedness, or constructibility hypothesis is used. Checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against the written argument: no new-node duplication or clause relocation, no appeal to another node's proof, no missing substantive fact hidden by a source tag, and no category switch to pro-etale or completed coefficients. The attached quotations cover each cited statement.

## Second reading by NG

- Item statement: checked 03PK (section-kummer), 040M (example-roots-of-unity), and 03Q1 (lemma-stalk-pullback), against the concrete-model description in WeilConjectures/EtaleCohomology/Purity/Smooth/Conventions.lean and blueprint prop-asd-smooth-base-change proof paragraph 2; PASS. The signed, arbitrary-coefficient and unbounded clauses are explicitly derived, not claimed verbatim from 03PK. No statement dispute or statement change.
- Step 1: opened lem-asd-finite-etale-twist-line, def-pur-sheaf-tensor-product and def-pur-sheaf-hom; PASS. The finite-ring hypothesis is met at Z/m only; the two tensor-unit maps extend to arbitrary A without flatness. Dualization is of a locally free line only.
- Step 2: opened all seven cited statements and 03Q1(4), 040M and the 03PL root-algebra calculation; PASS. The representing scheme is etale because m is invertible. Yoneda evaluation and natural-Hom recognition identify the actual comparison, with the identity point fixing its direction and normalization. Nonaffine objects are handled on affine refinements of overlaps; no affine-intersection assumption.
- Step 3: opened the algebraic-structures, covering-base-change, restriction, composition-units and cover-detects-iso statements; PASS. The underlying set comparison is promoted to abelian groups before applying abelian cover detection. The composition and power identities are the displayed identities of section restriction maps.
- Step 4: opened finite-limits, continuous-base-change, left-exact-site-inverse-image-tensor and exact-coefficient-inverse-image statements, and 03EL (lemma-tensor-product-pullback); PASS after making the larger value universe explicit. The balancing coequalizer gives relative tensor over Z/m and A from the cited absolute monoidal assertion; constant-ring comparison has exactly the required normalization.
- Step 5: checked both definition statements and both covering statements against 04TT (section-internal-hom) and 03EM (lemma-internal-hom); PASS. Evaluation sends the local dual basis tensor to 1, and the pulled-back functional sends the pulled-back basis to 1. The inverse dual has the required direction; no general internal-Hom pullback assertion is used.
- Step 6: checked the tensor/Hom definitions and the explicit change-of-basis calculation u^a for signed a; PASS. Coefficient multiplication proves the stated diagrams locally, and equality of sheaf maps glues. No derived equality is inferred from geometric stalks.
- Step 7: opened all four cited statements and 07A4 (lemma-pullback-tensor-product), 0G7E (lemma-pullback-K-flat); PASS. The cited theorem is unbounded and preserves K-flat resolutions with flat terms. Exact inverse image identifies derived pullback with degreewise pullback, preserves shift signs, and the tensor-complex formula supplies termwise coherence.
- Step 8: opened all four cited statements and checked the cyclic-kernel arithmetic; PASS. For m'=qm, the subgroup killed by m is q(Z/m'), while the power transition in the induced bases is reduction of residues. Scalar extension is therefore the identity on A even if q=0 in A; inverse dual gives the signed transition.
- New nodes: none; B1–B7, duplicate and Mathlib-leaf checks are vacuous. All 34 citation records were independently compared with the full current statements and agree verbatim. Independent Mathlib grep rootsOfUnitySheaf|Tate.*[Tt]wist|[Tt]ate.*[Tt]wist ran via msearch.py and returned zero hits; its actual output is in searches.jsonl.
- Attachments: read the actual source paths WeilConjectures/EtaleCohomology/Purity/Smooth/Conventions.lean and WeilConjectures/AlgebraicGeometry/Sites/RootsOfUnity.lean, including constantZModIsoRootsOfUnitySheaf. The former assumes the twist comparisons as fields; the latter requires a field and a supplied primitive root. Neither finishes this arbitrary-scheme item. The master and blueprint are reference statements, not finished-proof evidence.
- Edge cases: checked zero A, m=1 (forcing A=0), empty T and T', a=0, negative a, identity and composite maps, arbitrary shifts and unbounded K; PASS. For A=F_2, m=2, m'=4 the map is identity in compatible bases; no invertibility of q in A is assumed.

Changes: made the universe hypotheses of the monoidal site lemma explicit in Step 4; added this independent reading and precise attachment paths. Retained the mathematical statement, all other proof text, and all citations. Retained split_report.tool_uses as proposed tools: tools/review_split.py lines 99–101 explicitly authorize worker proposals there; no top-level maintainer approval was added. No new nodes or Mathlib leaves, and no Lean writing or compilation.

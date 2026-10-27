# Q132: lem-pur-finite-tate-scalar-source-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-finite-tate-scalar-source-normalization.json — statement, now split into seven proof steps; not a Mathlib leaf.
- citations.json — verbatim statements for every step/node citation.
- report.md — this report.

No new nodes, no Mathlib leaves, no unit-record edits, and no Lean changes. The sandbox also holds the actual searches.jsonl and the preparation script. The source statement, statement dependencies, import metadata, and inherited search records were retained.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, scalar/single, Tate/scalar, Tate balancing, and K-flat terminology. ModuleCat.derivedExtendScalarsSingleIso in CategoryTheory/DerivedCategory/ExtendScalarsLocalization.lean:121 concerns ordinary ring modules and assumes the coefficient ring map flat; it does not attach this ordinary-etale sheaf statement for nonflat coefficient maps. The other uses of that declaration do not supply the missing clauses.

## WANTED

None. All literature needed for this split is present. No SGA source was used.

## What changed and why

The imported item had a statement but no proof. I retained its statement and expanded the specified comparisons into calculations rather than introducing lemmas for its own clauses. The blueprint source is main-20261015, sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md, paragraph 2. I also read the chapter and the sk-prop-an unit record, including the old vector-bundle Step 7. The argument supplies only the finite Tate-source coefficient calculation; it does not invoke general smooth purity, a new trace, or a different coefficient category.

The full scalar adjunct formula was already in lem-pur-sheaf-ring-derived-coefficient-adjunction. Its normalized formula identifies q_M with the actual identity flat-resolution computation, avoiding a separate uniqueness or comparison lemma. Flatness of a single complex implies K-flatness directly from exactness, so it remains a step. Ordinary Tate balancing has an explicit inverse, and its tensor powers are checked on tensors; these also remain steps. The final source comparison is the composite of the existing tensorator, scalar/pullback identification, and the line map proved here.

No source or statement error was found. No STATEMENT-DISPUTED correction was needed. The formula with the root-of-unity factor on the right is interpreted using exactly the symmetry already stipulated in the item. At rank r the product formula has a single final A' coefficient; the tensorator accounts for this balancing, so it is not an unbalanced tensor over the original ring.

## Searches and reuse

The sandbox was initially empty except for dispatcher markers. I read the current repository node and retained its five inherited searches. My searches are recorded exactly in searches.jsonl and added to mathlib_searches where not already present: LeanFinder for flat sheaf singles and then for monoidal/inverse-image/shift scalar comparison, Loogle for TensorProduct and CategoryTheory.Sheaf, grep for Tate/twist/scalar, and LeanSearch for finite Tate normalized coefficient extension. The hits concern ordinary module adjunctions, flat ring maps, formally etale algebras, or general monoidal sheaf structure. None states all clauses for these normalized unbounded derived ordinary-etale sheaf functors. In particular the ordinary ModuleCat unit formula alone is not an attachment or a Mathlib leaf for this statement.

Whole-DAG searches covered flat singles, bounded-above flat complexes, scalar/pullback comparison, and tensor/shift normalization. Blueprint searches included scalar, K-flat, Tate, scalar single, Tate balancing, scalar/single, and ordinary Tate. The precise scalar/single and ordinary Tate searches returned no equal blueprint statement. Existing general nodes were used instead of creating specializations. blueprint.from retains its precise paragraph-2 place under cor-pur-vector-bundle-purity and same_as is empty. Generic off-unit tools are each declared in split_report.tool_uses; none replaces the unit's purity route.

## Not duplicates

There are no new nodes and therefore no new/existing same-tag pairs. In particular no duplicate flat-single, balancing, or scalar/pullback node was introduced.

## Review by Q132

I read the statements of every node in the seven steps before citing them, and read the relevant primary sources: Stacks sites-cohomology.tex, Definition 06YN (definition-K-flat), Lemma 06YY (lemma-derived-base-change), Lemma 07A6 (lemma-adjoint), Lemma 0G7E (lemma-pullback-K-flat), Lemma 07A4 (lemma-pullback-tensor-product); sites-modules.tex, lemma-adjointness-tensor-restrict and Tag 03EL (lemma-tensor-product-pullback); etale-cohomology.tex, Section 03PK (section-kummer) and Lemma 03RV (lemma-characterize-finite-locally-constant); groupoids.tex, Example 040M (example-roots-of-unity). These validate the existing interfaces, while the normalization calculations beyond the blueprint's short paragraph are explicitly recorded as agent-written.

Step 1 cites the definition of exact tensoring in def-pc-flat-sheaf-modules and of K-flatness in def-pc-kflat-complex, not a theorem that merely mentions these notions. It writes the total tensor with M[0] degreewise and proves acyclicity from exactness. The computation clause of lem-pur-derived-change-of-rings then applies to the identity resolution. No boundedness of a test acyclic complex is used.

Step 2 uses exactly clause (2) of lem-pur-sheaf-ring-derived-coefficient-adjunction: the adjunct of g is x tensor a mapped to a g(x), for a flat-term K-flat source. Step 1 establishes that hypothesis for M[0]. Taking g to be the ordinary scalar unit gives the identity on the ordinary tensor. The isomorphism assertion then comes from the K-flat computation clause of lem-pur-derived-change-of-rings. Thus q_M is identified as the specified map, not only as an abstract isomorphism.

Step 3 uses the definition of sheafified tensor for the multiplication and insertion inverse. It checks both composites by the balancing relation and uses the normalized unit formula of the coefficient-adjunction node. This proves the ordinary formula for u_T explicitly.

Step 4 uses the actual statement of lem-asd-finite-etale-twist-line for flatness for every r, including r=0. Its hypotheses N invertible and NA=0 are exactly present, also for A'. It does not take tensor flatness from a definition alone. The rest is a written inverse formula for the sheafified balanced tensors using def-pur-sheaf-tensor-product. The ring relation for Z/N is respected because the unital ring map commutes with the integer action. No primitive root or global frame is chosen.

Step 5 takes the canonical derived tensor isomorphism and K-flat preservation from lem-weil-pbc-ringed-topoi-derived-tensor-pullback, applied to the identity topos with the coefficient ring map. It spells out its ordinary tensorator and inverse on representative tensors. The shift equality is a direct equality of the shifted terms and their signed differentials. In particular there is no unproved assertion that an arbitrary natural isomorphism commutes with shifts. Even shifts account for the absence of a Koszul sign when line factors are regrouped.

Step 6 cites the tensor comparison and the introductory scalar/pullback identification in lem-pur-etale-scalar-mate-projection. I checked its statement carefully: that identification is stated on ordinary unbounded categories before its separate bounded-below assertion about a direct-image mate J. This step only uses the identification, never the mate theorem or its projection-formula conclusion. All displayed arrows have the indicated source and target over A', and each is already an isomorphism. The scheme morphism need not be proper, smooth, or finite type.

Step 7 takes existence of a flat-term K-flat resolution from lem-pc-kflat-resolution and preservation under ringed pullback from lem-weil-pbc-ringed-topoi-derived-tensor-pullback. It uses the same canonical scalar/pullback comparison as Step 6. The two claimed unit compatibilities are checked as equations of balanced maps in each degree, with scalar coefficient phi(a)b written on both paths; they are not left as an unexplained transport assertion. These representative equations descend to the specified derived comparisons. The arbitrary complex can be unbounded because both cited resolution and pullback statements are unbounded.

I tested M=0, r=0, r=1, the identity coefficient map, the zero target ring, and the empty scheme. The formulas and inverse formulas still apply. For N=1 every unital coefficient ring killed by N is the zero ring, so all module categories and line formulas are the corresponding trivial case. For the genuinely nonflat example Z/4 to Z/2 on Spec(C), the flat source line still has its identity flat resolution, so extension has no negative Tor terms on that source; no step treats Z/2 as flat over Z/4. An arbitrary unbounded K is handled with a K-flat representative rather than assuming its cohomology or its scalar extension bounded. A unital map from the zero ring to a nonzero ring is not an allowed extra case.

Against delivery-errors B--E, this delivery creates no statement-only sublemmas, does not restate its clauses as new nodes, and quotes no theorem merely from another node's proof. Every citation has a verbatim statement in citations.json. All seven steps are below 2000 characters. A dependency traversal found no cited node depending back on the item. I did not run any compiler, Lake tool, or local DAG/preflight checker. The required dry run is performed only through deliver.py on the server.

## Unfinished work

No part of the one-level split is unfinished. Existing cited nodes remain separate DAG work; this delivery does not claim they are Lean-closed. The maintainer's independent review remains the mathematical acceptance step.

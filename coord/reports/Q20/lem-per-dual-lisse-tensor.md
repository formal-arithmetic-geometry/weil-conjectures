## Worker report

Files written: dag/nodes/sec-deligne-laumon-a1/lem-per-dual-lisse-tensor.json (statement, split, no Mathlib match). The seven proof steps reuse existing nodes. No new nodes and no Mathlib leaves were created. citations.json records every step/node pair; searches.jsonl contains the actual item searches and results.

Attachments: none. I read WeilConjectures/SixFunctors/Etale/Perverse/Operations.lean, especially lines 90–107. AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_verdierDual_tensor is sorry-free in its own body, but its coefficient category is generic discrete small-etale sheaves, and it assumes IsDualizable L. The node concerns the adic common-stage rational category and a classical lisse sheaf; this declaration alone does not supply that interpretation or discharge dualizability. IsLisse later in that file includes dualizability among its hypotheses. It is not an exact attachment of this item under the item's hypotheses.

WANTED: none.

The statement is retained verbatim. I corrected its statement dependencies: the imported constructible-complex definition is finite-coefficient only; the rational common-stage category, classical adic lisse notion, coefficient operations, common-stage Verdier duality and linear-dual interpretation are now named. The smooth notion and the chapter's standing geometric finite-field setting are explicit dependencies. The statement is read in that standing separated finite-type geometric scheme setting, as is the six-functor category; no connectedness, nonzero rank, perfectness of K, finite monodromy or extra bound is added.

## Source error

The main-20261015 proof of this item has three C4 faults. Its fin2-lem-lisse-trivialized-finite-etale has a finite ring hypothesis, so cannot trivialize a rational lisse sheaf. For example, over an algebraically closed field of characteristic different from ell, the ell-power Kummer tower of G_m gives a quotient of its fundamental group onto Z_ell. Compose this quotient with a continuous injective character Z_ell -> 1+ell Z_ell (1+4 Z_2 if ell=2). The resulting rank-one adic sheaf has infinite monodromy; restriction to any open subgroup still has infinite image. No finite etale surjection trivializes it. This refutes the imported proof's inference, not the item's duality formula. Second, fix-lem-tensor-adjunction states an Rf_*/Rf_! exceptional adjunction, not the ringed-site currying formula used in the first display. Third, def-trf-dualizing-complex now defines finite A_{E,n}-duality only. It cannot define rational duality here. The final paragraph also asserts an uncited Hom/second-variable tensor interchange. The repair uses actual currying with the lisse factor outermost, followed by evaluation for its perfect integral lattice. The statement itself is not disputed.

The unit and chapter routes remain unchanged: this is the auxiliary lisse-tensor argument used by the curve perverse unit, not a replacement of the Fourier argument. The generic coefficient and ringed-site tools listed below supply the details the node's proof omitted.

## Searches and reuse

I searched the project source by the blueprint id and by dual/lisse/tensor notions, read the Operations declaration, and searched the whole DAG for dualizable, lisse, perfect and internal-Hom comparisons. blueprint_refs.py ancestor identifies this item itself as the blueprint ancestor; searches for dual, dual-lisse and ringed-site-perfect found no alternative blueprint node stating the same item. Existing prop-sf-dualizable-hom has a site-perfect first argument but a six-functor finite-Tor domain; the more general existing lem-sfb-ringed-site-perfect-duality applies directly to the integral ambient ringed site. No node was created for either that evaluation fact or currying: the latter is already lem-weil-pbc-ringed-internal-hom-exact-restriction. The existing adic-lisse-cohomology-calculus gives the degree-zero linear dual, but its statement does not assert a free integral lattice; the proof therefore cites representation equivalences, the stable-lattice lemma and the completed-system comparison separately.

The actual msearch commands tried the item in its geometric wording and again in closed-monoidal wording. LeanFinder first returned condensed monoidal structures and ordinary module duals; the second query returned closedOfHasLeftDual and the exact-pairing Hom equivalences. LeanSearch returned tensorLeftHomEquiv, tensorRightHomEquiv, internalHom and ihom.adjunction. Loogle on MonoidalClosed and ExactPairing had no hits. The two registered source greps found ihomCurryIso and rigid Hom equivalences. These are useful abstract tools, but none is the adic lisse Verdier-dual assertion with the given coefficient categories. The queries, returned names and verdicts are retained exactly in the item and in searches.jsonl; no unavailable response was represented as absence.

## New nodes

None.

## Not duplicates

No new nodes. All existing supporting statements were reused.

## Review by Q20

I read the main-20261015 statement and all three paragraphs of lem-per-dual-lisse-tensor.proof.md, the perverse unit and chapter records, and the chapter's conventions. For the repaired argument I read Stacks sites-cohomology.tex, lemma-internal-hom (08J9), lemma-dual-perfect-complex (08JJ), and lemma-symmetric-monoidal-derived (0FPT). The first curries three arbitrary ambient complexes; the second allows arbitrary second argument but requires only the first to be site-perfect. This is why K is never assumed perfect. I read Bhatt–Scholze, pp. 49–50 (6.5.1–6.5.5) and pp. 58–62 (6.8.3–6.8.4, 6.8.11, 6.8.14 and 6.8.15), and Stanford Weil II L19, p. 3, Proposition 1.1.9's lattice and reduction bullets. There are no new-node source claims to audit.

Step 1 cites the actual common-stage pair definition for a finite field of definition, the actual lisse definition for its finite-stage representative, and the coefficient-operations definition for the raw rationalized integral representative. The Noetherian and dimension lemmas have finite-type-over-field hypotheses, satisfied in the chapter's geometric setting. The use of the completed ring B is written explicitly; it is never confused with the discrete constant R-sheaf. The underlying def-weil-finite-field-fiber citation supplies k and ell, rather than a generic scheme definition being used to infer the finite-field setting.

Step 2 uses only the statements of the component lemma, both clauses of the lisse/representation equivalence, and the compact-group stable-lattice theorem. The latter requires continuous finite-dimensional monodromy over a finite extension and a compact group; these hold at the chosen finite coefficient stage with profinite fundamental group. The finite-clause scalar compatibility supplies the quotient transitions; their formula is written out. Disjoint open components allow the finitely many systems to be combined without any overlap gluing theorem. The classical lisse notion in the item, not an arbitrary pro-etale E-local system, is essential here.

Step 3 uses the completed-system comparison's actual inverse-limit construction and reduction statement, not any assertion from its proof. The integral-stratified characterization explicitly identifies the two integral category conventions and retains the etale-origin witnesses. A single stratum and one-term finite-free local complexes satisfy its condition (ii). The ordinary dual is locally the dual of a finite free module, so Hom into an acyclic complex is a finite sum of that acyclic complex; this checks the ordinary-to-derived-dual identification. The existing perfect-duality node states the global evaluation comparison; no hidden choice of local isomorphisms is made.

Step 4 uses integral Verdier duality's formula and output constructibility, the adic lisse calculus's assertion that the rational tensor is constructible, and the ordinary/completed tensor comparison. The comparison is not asserted merely from a definition of completion: its node states exactly that the ordinary tensor is complete and its canonical comparison is invertible. Its qcqs hypotheses hold for separated finite-type X. N and its dual were put in the integral category in Step 3, and C_R in this step.

Step 5 uses the symmetry theorem and the precise currying sentence of the ringed internal-Hom node. Substituting (N,K_R,W_R) yields RHom(N,RHom(K_R,W_R)), so the next evaluation theorem applies to the proven-perfect argument N. This repairs the original citation of the unrelated exceptional adjunction. The ambient categories impose no boundedness or small-index-colimit assumption on this substitution.

Step 6 uses perfect evaluation with second argument C_R and then tensor symmetry. The entire asserted isomorphism is composed in the step, rather than delegated to a new node restating the item. The two cited statements give precisely those maps. Their evaluation construction means local checks of perfectness do not require an unstated gluing/transport theorem.

Step 7 uses the coefficient-operations definition to apply rationalization to the already constructed integral isomorphism, and the rational and common-stage Verdier theorems to identify the resulting duality. Their statements expressly assert these coefficient passages. The adic lisse calculus's last paragraph identifies the coefficient internal dual with the linear dual in degree zero, including finite scalar compatibility. This is the linear dual, with no (d)[2d] inserted. The completed tensor comparisons already proved in Step 4 are used before passage, not assumed after it. All cited statements were opened, and citations.json copies the exact relevant text, including separate tensor and dual excerpts of the adic calculus.

Small cases: for rank zero both sides are zero; for rank r constant lisse sheaves the evaluation formula is the finite-sum identity; disconnected X permits varying local rank because all constructions are componentwise on finitely many open components; for a geometric point the result is finite-dimensional linear duality for a bounded complex; K=0 and arbitrary shifts give the same isomorphism. Infinite monodromy is permitted by the lattice construction and does not require finite-cover triviality. Empty X has no components and all the displayed objects are zero. No SGA route or purity/trace theorem was introduced. No proof step exceeds 2000 characters or hides a new comparison lemma. I checked B1–B9, C1–C8, D1–D5 and E1–E7 against the actual files: no new-node placeholders, no duplicated notions, no unsupported citation, no moved copy of the item, no hidden added hypothesis, and no silent statement correction remain. The corrections described above are my own rereading and repair for this direct-delivery brief.

## Tool uses

The split_report declares generic off-unit tools for the component/lattice construction, exact integral-category membership, ordinary/completed tensor comparison, ringed currying and perfect evaluation, and the three coefficient stages of Verdier duality. These nodes are not replacements for a step of the perverse unit's Fourier proof. There is no within-unit node giving their more general coefficient and ringed-site statements. The maintainer-owned root tool_uses field was not edited.

## Unfinished work

None in the one-level split. Existing dependencies retain their own proof status. No Lean was written and no compiler, Lake or build command was run. Delivery validation follows below.

## Dry-run repair

The first server dry run rejected an introduced four-node cycle through rem-dl-a1-conventions, which bundles an intermediate-extension assertion depending on this item via the perverse-heart theorem. I removed that convention-bundle citation from both statement and proof dependencies and cite its underlying def-weil-finite-field-fiber for precisely the base-field and coefficient conventions used. The convention text remains source context, not a dependency on its later curve conclusions. citations.json was updated with the actual finite-field definition. The proof and statement formula did not change.

# Stage-1 report: lem-pur-integration-transpose-base-change

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-integration-transpose-base-change.json: statement item split into six explicit steps; Mathlib has its abstract adjunction tools, but not this ordinary-etale integration assertion.
- citations.json: one entry for every step/node citation, quoting the cited statement verbatim.
- report.md: this report.

New nodes: 0. Mathlib leaves created: 0. The sandbox also retains write_split.py and the real msearch.py search log as working evidence, not DAG delivery files.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by integration/transpose and projection/base-change terminology found constituent declarations only. In particular AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap in SixFunctors/Etale/Derived/LowerShriekProjectionExchange.lean gives the projection square, not every clause of this item. I read that file, including its finite commutative coefficient assumptions and its final theorem, rather than treating its existence as an attachment. AffineSpaceAdjunction.lean concerns the affine-space adjunction, not this arbitrary compactifiable map with arbitrary trace data.

## WANTED

None. No external source was downloaded or used.

## What was wrong or missing

The item had a statement but no proof. Its essential missing argument was the projection/base-change square needed before transposing the trace equation. The existing lem-asd-compact-projection-exchange states exactly that square, in the coefficient-first convention and ordinary unbounded etale categories; there is no need to create a second version. No statement, blueprint field inherited from the import, unit record, or target was changed. No statement dispute was found. The report does not claim an arbitrary mate of an isomorphism is invertible: the proof solves explicitly for e using the two gamma isomorphisms.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their own states. No Lean was written and no compiler, Lake or build command was run.

## Searches and duplicate review

I searched the whole DAG and blueprint before considering new nodes: blueprint_refs.py ancestor identified cor-pur-vector-bundle-purity; searches for projection, adjunction, integration transpose and compact projection exchange and DAG searches for projection/exchange and adjunction transport identified the existing tools. In particular lem-asd-compact-projection-exchange gives the missing geometric compatibility; lem-amb-mate-unit-counit, lem-weil-pbc-adjunct-counit-identity, lem-sfb-adjunction-transpose-square and lem-weil-pbc-adjunction-of-natural-bijection supply the categorical operations. The more general-looking lemma-weil-pbc-projection-formula-base-change-naturality has a pro-etale ringed base-change clause, so I did not substitute it for the ordinary-etale compact-support square. The coefficient-stage or constructible projection nodes have narrower domains and were not used.

The required msearch.py calls actually ran, with two leanfinder phrasings, Loogle, LeanSearch and Mathlib grep. Their exact query strings and returned names are retained in searches.jsonl and appended to the item's mathlib_searches. The pre-existing search records were preserved. The searches found abstract Hom equivalences, adjunction transport, ordinary tensor/sheafification and algebraic base-change facts; none states the whole item. I read Mathlib/CategoryTheory/Adjunction/Basic.lean lines 265–312, 350–370, 432–457 and 480–535 to check the relevant square, counit, natural-bijection and transport interfaces. In particular ofNatIsoRight transports only the categorical adjunction and does not discharge the geometric projection/trace equation.

## Not duplicates

No new node was created; there are no new/existing pairs to distinguish. The cited compact projection/exchange node was reused rather than duplicated. Each of the two elementary inverse cancellations and the two triangle calculations stays in the item's proof.

## Review by Q63

I read the current main-20261015 cor-pur-vector-bundle-purity.proof.md in full, the chapter record and the full sk-prop-an unit record. The source asks for the actual counit and for transposing the specified integration equalities, and unit Step 5(c) explains this same normalization and base-change mechanism. The split expands that mechanism; it does not use the forbidden SGA trace route or change the model-purity route. I also read Stacks categories.tex, definition-adjoint (Tag 0037), including the explicit unit and counit characterization, and sites-cohomology.tex, lemma-pullback-tensor-product (the source of the existing inverse-image tensor node). Since the blueprint is agent-written and the detailed calculations here were supplied by this worker, proof_origin.by is agent.

For step 1 I opened the statements of lem-amb-proper-coproducts-projection, def-kun-projection-formula-map and lem-pur-etale-open-derived-tensor. They identify the proper counit projection and the natural open tensor comparison used by this item's P. The proper formula is natural by the naturality of its displayed unit, counit and tensor factors; composing with the open natural comparison and inverting the square proves the displayed c-naturality. I opened lem-weil-pbc-adjunct-counit-identity and lem-sfb-adjunction-transpose-square; the former gives exactly epsilon F(gamma)=c and its uniqueness criterion, and the latter transposes the coefficient naturality square. Thus naturality is proved before it is needed for transport, and the same reasoning applies to the primed family.

For step 2 I read the full statement of lem-asd-compact-projection-exchange. Its Q is K, its M is W, its v is g and its v_X is g'. Its coefficient-first projection and tensor source comparison have precisely the directions required in the displayed equation. I also read lem-amb-unbounded-compact-support-comparisons: its exchange is normalized as proper exchange followed by open extension comparison, so it is the C chosen by the item, including after choosing the base-changed compactification. The lemma says this works on every unbounded complex. I read lem-kun-inverse-image-monoidal: its bifunctorial tensor isomorphism supplies mu and its naturality at the trace. Postcomposing the projection square with F'(1 tensor l), then with inverse P' and the trace, gives the actual c equation written in the proof. The naturality in l is immediate from the same two projection factors used in step 1. I checked that the compactification and Noetherian hypotheses match; X' is Noetherian since it is of finite type over Noetherian Y', and the base-changed compactification is available. No hypothesis that g is flat, proper or of finite type is used.

For step 3 I read lem-amb-mate-unit-counit with L_1=F, R_1=R, L_2=F', R_2=R', G=J, H=H and alpha=C inverse. It supplies exactly epsilon' F'(e)=H(epsilon) C inverse. Naturality of the exchange, explicitly included in lem-amb-unbounded-compact-support-comparisons, moves F'(J gamma) past C inverse. The adjunct-counit identity from the cited Mathlib leaf then identifies both transposes. This is equality of specified maps, not equality inferred from their source and target objects. Step 4 only solves that equality for e and uses functoriality on inverses; creating an isomorphism-mate node would be both unnecessary and misleading.

For step 5 I read lem-weil-pbc-adjunction-of-natural-bijection. Its statement includes naturality in both Hom variables, the identity formulas for the unit and counit, and both triangles. Composing the original Hom bijection with gamma inverse gives such a bijection, and the displayed inverse has the direction Hom(M,G0 K) to Hom(FM,K). Evaluating it at identity gives exactly the requested counit. Evaluating the forward bijection at identity gives gamma at FM inverse followed by eta_M, exactly the requested unit. The adjunct-counit identity fixes the normalization c. Step 6 also calculates each triangle: the first cancels F(gamma) with F(gamma inverse), and the second uses naturality of gamma at c_K and of eta at gamma_K before the original right triangle. There is no hidden adjoint-existence or geometric comparison lemma here.

I checked small and degenerate cases against the formulas: identity f and g reduce to the Hom transpose and tensor trace identities; zero W and W' give zero transposes and only the conditional isomorphism conclusion; zero ring, empty X or Y, and zero input complexes introduce no cancellation of a non-invertible map. No assertion needs t to be invertible. The proof cancels only the projection components assumed invertible, the canonical pullback/tensor and l comparisons, and gamma when the corresponding conditional clause permits it. No boundedness, constructibility, finite Tor amplitude, invertibility of the coefficient characteristic, or pro-etale completion is inserted. Every cited node statement was opened, and citations.json retains verbatim quotes with all hypotheses. Every step is below 2000 characters; none hides a separate comparison claim. I checked the delivery-errors B–E issues: no new-node schema or duplicate problem, no definition substituted for a theorem, no mismatched etale/pro-etale category, no clause moved into a new node, and no unsupported “transport” assertion.

## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-derived-mate-counit-reduction.json (statement, split; no Mathlib match), citations.json, and this report. The sandbox also holds the actual msearch log searches.jsonl and the script used to write the JSON. No new nodes; zero new Mathlib leaves.

Attachments: none. I searched lean/WeilConjectures for the blueprint tag, counit-reduction names, and derived mate terminology. CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac, PlusAdjunction.lean:419, is sorry-free in its own source, but states the larger underived-mate comparison-unit factorization, not the intermediate reduction in this item. Its local `key` calculation is not a separately declared theorem. Thus this is not an exact attachment. The existing bounded-below adjunction node already records derivedPlus_counit_app_fac, so that fact is reused rather than duplicated.

WANTED: none.

The item had no proof. Its statement is well typed and true as written; I retained every hypothesis and the entire conclusion. I supplied five short steps, totaling 1742 characters, using existing nodes only. The proof never uses the parent mate-model theorem or the sibling derived-transpose theorem, so introduces no circularity. It does not assume the square or either right-derived comparison is invertible. It does not choose a resolution or assume that H preserves injectives.

Nothing remains unfinished in this one-level split. No Lean was written or compiled; the shared repository and launcher were read only.

## Sources and searches

I read the chapter sec-trace-formula and unit sk-i-curve-zero records, the three blueprint levels of SETUP.md, GOAL.md, and the latest blueprint at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its proof. COMMITS.txt identifies the current snapshot as main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345. The ancestor's normal-cone specialization argument is realized through the existing comparison/descent chain; this purely categorical calculation does not replace that geometric route.

The direct source for the item is lean/WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean, derivedPlus_mateEquiv_app_fac:419–484, particularly hmate:439–446, h₁/h₂/h₃:450–452 and the key equality:467–482. I also read derivedPlus_counit_app_fac:154–160 and the source definition of CategoryTheory.mateEquiv in Mathlib/CategoryTheory/Adjunction/Mates.lean:84. The proof is marked agent: it expands and reorganizes the project's calculation rather than claiming a human-written Stacks proof of this intermediate statement. No SGA source is used.

The existing searches from the item were retained, including the historical invalid Loogle query and unavailable LeanSearch result as such. I ran and read new logged LeanFinder searches with two phrasings, Loogle for mateEquiv_apply and derivedε_fac_app, LeanSearch for the complete comparison identity, and msearch grep in Mathlib/CategoryTheory. I read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:95–133. The hits give the component definition of a mate or a single derived counit/unit factorization, not this combined two-adjunction calculation involving an arbitrary exact square and its localization comparisons. Consequently the item is split, not labelled a Mathlib leaf.

I searched the whole DAG for mateEquiv_apply, counit/naturality and the exact item, and searched the whole imported blueprint with blueprint_refs.py search for `mate`, `mate counit`, and `derived mate`; no exact blueprint statement was found. blueprint_refs.py ancestor returns lem-trf-local-term-locality. All existing blueprint provenance was retained and same_as is []. No new node was proposed, so there is no new-node duplicate or elementary-node question.

## Not duplicates

No new nodes.

## Review by Q48

I checked the statement against the displayed morphisms in PlusAdjunction.lean with the node and source open. Here L has target A, L' target A', and the enough-injectives assumptions concern exactly A and A'. N=K(R)P is bounded below since additive termwise functors preserve the zero terms. Z=qK(G)N lies in D+(B'), and t has source Z and target TU(qP). Both sides of the asserted identity therefore go from Z to U'(qK(H)P). Exactness and enough injectives are used for the given canonical data, not to invert a comparison on P. No assumption on injectives in B or B' is introduced.

Step 1 uses the actual component formula in the statement of def-weil-pbc-adjunction-mate, with L1=E, R1=U, L2=E', R2=U', G=T, H=S. Its first arrow is the primed unit at TU(X), and its last arrow is U'S of the unprimed counit. Naturality at t gives the displayed expression inside U'; this is the defining naturality square, with functoriality and reassociation only. It is therefore elementary relative to the cited definition.

Step 2 writes naturality of the assumed transformation theta at u=alpha_P explicitly. Its equation has source E'(Z) and target SEU(X). Substituting t=T(u)a^{-1} requires no fact about invertibility of u. No hidden lemma is used in this elementary substitution.

Step 3 cites the statement of lem-trf-bounded-below-derived-adjunction: its second displayed identity is exactly epsilon^D_X E(alpha_P)=q(epsilon^K_P) phi_{L,N}. I checked exact L, additive R, the specified adjunction, enough injectives in A, and bounded-below P against that statement. It needs no primed comparison, no injectivity of P, and no enough-injectives hypothesis on B. This step is marked non-elementary because it uses the normalized derived-adjunction theorem.

Step 4 cites the natural localization isomorphism stated by lem-weil-pbc-exact-functor-derived-factorization. The bounded-below homotopy comparison used here is already specified as natural in this item's hypotheses; I use just its naturality at the counit class e, not an additional restriction/descent theorem. The formula h S(q(e))=q(K(H)e) f is precisely that naturality square. Expanding A_N and B_N in the item's assumed equality then gives the second formula. Cancellation is only E'(a)E'(a^{-1}), permitted since a is explicitly an isomorphism. Combining the two q-images is ordinary functoriality. These are elementary computations, written out rather than hidden behind a transport claim.

Step 5 substitutes the result in Step 1 and expands U' of a composite. This gives exactly the asserted formula, with no alpha' term introduced. The absence of alpha' from the calculation confirms that its invertibility is irrelevant. There is no suppressed injective-resolution argument.

I read every cited node's statement and put a verbatim part of each in citations.json, separately for its proof step. The three cited statements supply precisely the component mate formula, the normalized unprimed counit, and naturality of the exact localization comparison. All remaining steps are the defining naturality equations, associativity, and functoriality; none is a new non-elementary fact. Every proof step is under 2000 characters; no long step hides a comparison lemma.

For edge cases I checked sigma=0 in additive categories: theta's assumed component equality forces the relevant component to be zero and both displayed composites vanish. With all functors and adjunctions identities, the formula reduces to theta_{qP}=q(sigma_P); with P=0 it is an equality of the unique maps between zero objects. More generally the equations are valid with an arbitrary noninvertible u because no cancellation of u occurs. These checks exposed no statement dispute. I corrected no source statement, added no hypotheses, and created no clauses masquerading as new lemmas. This review checks delivery-errors B–E in the actual proof, including cited-statement scope, rather than relying on the imported dependency list.

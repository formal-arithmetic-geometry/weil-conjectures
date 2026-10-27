## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-exact-square-right-derived-unit.json — statement, split; no exact Mathlib match. The statement, hypotheses and conclusion are unchanged.
- citations.json — one checked verbatim statement excerpt for every proof-step citation.
- searches.jsonl — actual searches performed by the prescribed msearch command. The inherited item's searches remain in its record; this run's queries were appended.

New nodes: none. Mathlib leaves created: none.

Attachments: none. Searched the project source for the exact blueprint tag and the notions. CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_fac in WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusBaseChange.lean:84 proves the bounded-below comparison equation, not the unbounded assertion here. Its PlusExact input likewise has bounded-below categories. The FromJoel K-injective derivability structure assumes monomorphic K-injective resolutions; the item only assumes a quasi-isomorphism to a K-injective complex. Neither is an exact attachment.

WANTED: none.

Problems found: the item was statement-only, not an erroneous statement. The blueprint ancestry command returns None for this existing item, whose inherited from.node is already null. Its full existing via chain and precise paragraph description were retained. The read chapter is sec-six-functors-basics; the recorded unit is sk-thm-sf-ctf-stability, whose direct-image step this coefficient-comparison tool serves. No chapter or unit route was changed.

Unfinished work: none for this stage-1 split. No Lean was written, compiled or built. Repository and launcher files were only read.

## Sources and searches

Read Stacks derived.tex, Tag 070I, label lemma-K-injective (the Hom bijection); Tag 070Y, label lemma-K-injective-defined (computation on K-injectives); and the adjoining Tag 070K, lemma-enough-K-injectives-implies. Verified the tags against literature/stacks-project/tags/tags. Read the current blueprint def-sfb-right-derived-functor.md and sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). The source proves K-injective computation; the explicit inverse on natural transformations here is an agent argument, and proof_origin says so.

The msearch commands tried both the postcomposition description and the exact-square/unit description. Read Mathlib CategoryTheory/Functor/Derived/RightDerived.lean:51–98 (definition, rightDerivedDesc, rightDerived_fac and rightDerived_ext), and Localization/DerivabilityStructure/PointwiseRightDerived.lean:49–83. Loogle additionally returned an instance named instIsRightDerivedFunctorCompCompWhiskerRightHomAssociatorOfIsLeftAdjoint; a further logged grep and a read of the full pinned RightDerived.lean found no such instance in this project version. The name of the online hit indicates a left-adjoint hypothesis, which the item does not assume. The generic comparison declarations require an already established postcomposed right-derived pair. Exactness alone is not a left-adjoint assumption. Thus these are candidates for the final assembly, not a one-line proof of the whole item. The split proves the missing universal property explicitly.

Searched all DAG statements and source fields for 070Y, K-injective computation/universality, postcomposition and comparison. Searched the entire imported blueprint using blueprint_refs.py search with K-injective, right derived, exact coefficient square and 070Y. The general Hom and localization statements already exist and are reused. lem-sp-kinjective-computes adds Grothendieck, left-exactness and bounded-below hypotheses. lem-weil-pbc-kinjective-exact-square-comparison assumes preservation of K-injectives and concludes an isomorphism. Neither applies with the present hypotheses. The existing exact finite-total comparison concerns another construction. No additional duplicate nodes were created.

## Review by Q126

I checked the statement against the unbounded right-derived definition and the K-injective computation source. F and G need only be additive; U and V are exact additive functors. Every complex of A and A' has a K-injective replacement, without requiring a monomorphic replacement. No preservation of K-injectives by U and no invertibility of the final comparison entered the proof. The chosen localization can have objects other than literal complexes, so step 2 uses representatives up to isomorphism instead of assuming objectwise equality.

Step 1 uses lem-weil-pbc-exact-functor-derived-factorization for the canonical termwise identification under V. Its statement explicitly provides that identification without resolutions. def-sfb-right-derived-functor explicitly states both the natural unit and its invertibility on every K-injective complex; functors preserve isomorphisms, giving alpha_I invertible. I opened both statements and copied the relevant clauses into citations.json.

Step 2 uses lem-trf-localization-essentially-surjective, whose statement explicitly supplies a representative and isomorphism for every object of a universal-property localization. Composing with the assumed resolution gives e_X. The statement of lem-weil-pbc-kinjective-hom-derived gives bijectivity for EVERY source N and a K-injective target I, so it gives the unique lift of e_Y a e_X inverse. No source K-injectivity is needed. Its assertion is also the verified Mathlib KInjective.lean:41–50 Hom-bijection theorem.

Step 3 is the displayed naturality calculation. Each intermediate object is specified; alpha and tau are transformations with the same source E. The identity alpha_J inverse H(Qf) = E(f) alpha_I inverse follows by multiplying the naturality square by the two invertible alpha components. The equality for tau then gives the required beta_Y H(a) = T(a) beta_X. This is a calculation with the data already constructed, not an uncited existence or comparison theorem.

Step 4 again cites the Hom-bijection node with arbitrary source P and target I_(QP). It lifts e_(QP) itself; no conservativity inference or quasi-isomorphism representative for that map is needed. The two written naturality identities give the factorization at every complex P, not just on K-injectives. Step 5 cancels alpha_I and uses naturality at e_X to force the sole possible beta_X. This proves injectivity and choice independence. Neither step imports the proof of a node instead of its statement.

Step 6 cites the exact-factorization statement for U and the natural-unit clause of the right-derived definition for G. Whiskering the natural units and the given c makes tau natural. The bijection established in steps 3–5 then gives the exact required gamma equation and uniqueness, so this step is only assembly of proven data. All canonical exact-localization identifications are retained; there is no unsupported claim that c is an equality of functors.

I tested identity U,V and c (recovering the canonical comparison), zero F and zero V (the universal pair is the zero one), a K-injective input (where alpha cancels directly), and an arbitrary non-K-injective input (covered by step 4). The construction never uses inverse eta^G_(UP), so it also covers failure of K-injective preservation by U. Existing-node citations do not create a cycle: the Hom leaf and localization leaf have empty proof dependencies, and the right-derived definition and exact-factorization node do not depend on the item. No new statements required additional edge-case testing.

Checked delivery-errors B–E against the actual JSON and open sources: no new statements or proof sketches in unsplit nodes; no missing non-elementary fact is hidden by a tag or by a definition citation; the only non-elementary inputs are the explicit existing statement clauses named above. The argument is written in the item and not moved into a replacement clause node. Every non-elementary step is below 2000 characters (all steps are below 700). No correction to the imported statement was needed.

The off-unit Hom-bijection and essential-surjectivity citations are existing Mathlib leaves. The right-derived definition is a definition, and the exact-factorization node is an existing Mathlib leaf; none replaces a unit proof route.

Validation: the first required deliver.py --no-push finished successfully, printing OK (not pushed) at 2f26bb2c6e2. After clarifying the online-versus-pinned Mathlib search result, the required dry run is repeated on the final report.

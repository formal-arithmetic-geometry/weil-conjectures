# lem-sfb-qcqs-integral-finite-model-completeness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-integral-finite-model-completeness.json: statement, split into eleven proof steps; no Mathlib match.
- citations.json: verbatim statement excerpts for every step/node citation.
- searches.jsonl: actual msearch.py query log, retained unchanged.
- report.md: this report. write_split.py is sandbox-only preparation, not a DAG delivery file.

There are **0 new nodes and 0 Mathlib leaves**. No unit realization changes are needed: this is a supporting node of the compactification-coherence unit, not its key statement.

## Attachments

None. Searched WeilConjectures for the exact blueprint id and for completeness, finite models and integral constructible inputs. The project source has no declaration giving this entire arbitrary-qcqs statement. Its ordinary finite-coefficient constructibility and coefficient-category declarations do not establish the integral completion assertion.

## WANTED

None. The literature used is available in the read clone.

## Corrections and scope

The statement is unchanged, including the ordinary unbounded ambient category, strict completion unit, torsion models, every positive finite quotient and arbitrary qcqs V. Removed the unused statement dependency sk-def-localizing-closure; neither the statement nor this proof uses a localizing closure.

The imported node was statement-only. In particular, its reference to Sections 6.5--6.6 was not itself a proof. The existing lem-sfb-integral-cohomological-adic-criterion and det-prop-integral-criterion-reductions assume a Noetherian scheme, and lem-sfb-integral-constructible-completion-bridge assumes still more geometry. They are not used. Bhatt--Scholze Proposition 6.6.11 is topologically Noetherian and concerns perfect complex models; the present hypothesis instead supplies finite scalar models for each cohomology sheaf. The proof explicitly handles those cohomology sheaves and then their bounded truncation triangles. It does not assert an equivalence between the two kinds of local model.

The qcqs open/closed tree avoids assuming that an arbitrary finite locally closed partition has an open stratum compatible with its scheme structures. Leaf-to-stratum maps come from the refinement lemma, not merely from containment of underlying sets. No geometric stalk conservativity is assumed for arbitrary pro-etale complexes.

## Unfinished work

None at the requested one-level stage-1 split. All non-elementary tools already have DAG nodes; no new statement-only obligations are necessary.

## Mathlib searches

Read the inherited five searches and ran actual fresh msearch.py searches in the sandbox log: LeanFinder twice, Loogle for DerivedComplete, grep for derived completeness and adic constructibility, and LeanSearch for reconstruction from finite quotients. All services answered. The first semantic query returned BDeRhamPlus, IsAdicComplete and AdicCompletion.map_exact; these concern ordinary module/ring completion, not the module-object derived category on a scheme's pro-etale site. The second returned abstract derived-category support, K-projectivity and K-injectivity interfaces, not this coefficient theorem. LeanSearch returned profinite group/space inverse-limit constructions. Loogle and source grep had no hits. These results do not state the item or a one-line specialization of it. The actual query strings, tool names and returned names are recorded in the node and searches.jsonl; inherited records were retained.

## Not duplicates

No new nodes. Whole-blueprint searches for complete, completion, finite constant, and integral finite, and the DAG searches by those concepts, located the existing tools used here. The narrower integral criteria are distinguished above and not duplicated.

## Sources and route

Read the current chapter and sk-prop-sf-comp-coherence unit, the item's nearest blueprint ancestor det-sf-comp-coherence-cocycle (Refinement isomorphisms), and the parent closed-base-change node. This split supplies the integral-input completeness and finite-classical-reduction part of that proper-base-change argument and leaves the compactification route intact.

Read Bhatt--Scholze Lemma 3.5.7, the completeness/stratification discussion in Proposition 6.6.11 and Example 6.6.12, and Hemo--Richarz--Scholbach Proposition 7.6 and Theorem 7.7. HRS gives the qcqs comparison context; it is not invoked as an unsupported substitute for the present finite-cohomology-model argument. Read the scalar-resolution/locality proof in the current blueprint det-def-localizing-closure-ctf-equals-bc and the strict cone/Roos argument in sk-lem-pe-derived-nakayama-first-reduction. Read Stacks proetale.tex at Tag 09AA (lemma-closed-immersion), Tag 09AI (lemma-compare-constructible), Tag 09B5 (lemma-constructible-serre), and Tag 09AL (lemma-compare-constructible-derived), verifying that scheme Noetherianity is absent. This is an agent assembly of these tools, recorded as such in proof_origin.

## Review by NC

I checked the statement and every cited node's actual statement, rather than importing assertions from their proofs. No new-node literature checks are needed because no nodes are created. The statements used as tools have the following roles and hypothesis checks.

1. The module-object/ringed-site derived comparison explicitly uses the exact section-action equivalence, leaves the underlying sheaves and maps unchanged and takes its tensor comparison from lem-pe-internal-section-tensor-comparison. The latter really preserves flatness, K-flatness and tensor complexes. Equivalences preserve products by their universal property, so this identifies the specified strict quotient tower and its augmentation, not merely the class of complete objects. The size convention covers the chosen sites and countable products.

2. I checked that immersion-limit-preservation allows arbitrary schemes and coefficient transport along an isomorphism; alpha-iso supplies precisely that isomorphism. The slice localization and object-inverse-image statements concern underlying abelian sheaves and ring sheaves, not just constant module coefficients; module limits are sectionwise. I made exactness explicit using the abelian inverse-image and lifted-module exactness statements. Applying these functors to the written scalar-cone transition and the written Roos augmentation identifies the canonical completion unit. Tensor/pullback comparison is stated for arbitrary ringed topoi and supplies the finite-reduction compatibility. No claim that a general inverse image preserves all limits is made.

3. The resolution node has the exact sequence for every scheme and every positive n. Its cone-to-quotient maps commute with the diagonal identity/pi transitions and take the cone inclusion to the quotient projection. The coefficient-limit node gives the actual quotient cone on B_T. Milnor-epimorphic has no Noetherian hypothesis and identifies the ordinary limit with the derived limit for this epimorphic tower; the cone/Roos lemma preserves levelwise quasi-isomorphisms. This proves the actual completion map invertible. Finite powers use only finite products and the same formulas.

4. The two-term finite-constant-model resolution expressly permits arbitrary schemes and torsion scalar modules; it produces an exact scalar sequence and its exact extended sequence. Completeness of the cokernel follows from its two free terms using the morphism-of-triangles clause of completion-triangle-comparison and the cohomology long exact sequence. Cover conservativity is stated for condensed coefficients, and step 2 checks that the map being tested restricts to exactly this one. I did not replace a finite presentation over the scalar ring by a variable matrix over B_T.

5. The constructibility definition gives a finite constructible locally closed partition. The qcqs refinement theorem provides a finite tree with qc open children and actual morphisms from leaves to strata, which is stronger than just a set partition. Base-changing the trivializing cover and finite scalar presentation gives the needed models at each leaf. This is where qcqs is used; the individual covering schemes in step 4 need no qcqs or Noetherian assumption.

6. Open/closed detection is a statement about sheaves. I apply it to each H^q of the completion cone, using exact restriction, and only then conclude that the derived cone is zero. Each internal vertex satisfies the required quasi-compactness of the open child by the refinement theorem. The induction is finite upward induction from the leaves and does not use a dimension bound or Noetherian induction.

7. The truncation theorem supplies the actual successive cohomology triangles, and completion-triangle-comparison includes both shifts and their canonical completion maps. The induction starts with zero below r and ends at J above s. Finite Tor amplitude is an allowed extra hypothesis, but is not needed to prove this stronger bounded-constructible completeness assertion.

8. The local-field and finite-quotient nodes give the finite scalar quotient, with no scheme condition. Reducing the exact scalar free resolution gives a two-term finite-free k_n complex. Derived change-of-rings computes it and the exact constant module functor identifies its kernel and cokernel with constant finite modules. The finite-discrete coefficient equivalence has exactly these coefficients. I explicitly checked finite presentation of those scalar modules using finiteness of both a free source and its relation kernel, so both senses of constructibility are satisfied without a scheme Noetherianity assumption.

9. Tensor/restriction compatibility from step 2 identifies the local reductions. The finite-coefficient constructibility definition is a finite constructible stratification with finite locally constant values, which is exactly what step 8 yields on each trivializing cover. The degree bound is checked by cover conservativity and the finite open/closed tree, not by an assertion that ordinary geometric stalks are conservative on the entire pro-etale derived category.

10. Derived change-of-rings is explicitly an exact triangulated functor. The finite-coefficient Dbc-triangulated lemma allows every scheme and a finite commutative ring. Applying it to the reduced truncation triangles gives J_n constructible, while the cohomology long exact sequence gives the common bound [r-1,s]. No normalization of cohomology towers is asserted; for a torsion scalar model the negative-degree transition can be zero.

11. The constructible comparison theorem requires a qcqs scheme and a discrete Noetherian coefficient ring, not a Noetherian scheme. V is qcqs and k_n is finite, hence Noetherian. Its bounded derived equivalence supplies an actual antecedent and isomorphism, which I retain as the pair required by the etale-origin witness definition. It is not merely a sheaf-level comparison, and no inverse-limit or completion claim is borrowed from it.

I tested the proof on V empty, J=0, a single constant free model, torsion A/pi and A/pi^a models, and a finite constructible partition whose leaves require refinement. In the torsion case the reduction has two cohomological degrees; the argument retains both, consistent with the familiar zero transition on the negative-degree part. Ramified extensions and schemes of characteristic ell use the same scalar resolution and no invertibility of ell. All eleven steps are under 2000 characters, and their comparisons have their coordinate maps written out or are cited statements. The dependency closure was inspected for a return to the item and has no cycle; cited nodes are unmerged. All off-unit uses are generic foundational tools declared in split_report.tool_uses. No SGA route is used, no Lean was written, and no compiler or build was run.

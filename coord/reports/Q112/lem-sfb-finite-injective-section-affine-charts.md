# Stage-1 report: lem-sfb-finite-injective-section-affine-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-injective-section-affine-charts.json: statement, split into six steps; no exact Mathlib match for the whole assembly.
- citations.json: eleven verbatim statement quotations, one for every proof-step citation.
- report.md: this report. searches.jsonl was produced by the required search command.

No new nodes; no new Mathlib leaves. The statement is unchanged. Added def-weil-affine-spectrum to stmt_deps because the statement explicitly uses Spec and coordinate rings. Preserved source, creation metadata, existing searches, null blueprint ancestor, precise from.place and via chain.

## Attachments

None. Searched the exact blueprint tag and the finite/injective/section notions in lean/WeilConjectures, including its AlgebraicGeometry and Mathlib/AlgebraicGeometry trees. No project declaration states all clauses of the item. The current item has no attached Lean or finished audit state. General section-injectivity lemmas for sheaves and the finite-map characterization do not establish this item.

## WANTED

None. The proof uses the local Stacks source and current blueprint; it does not require the ILO PDF to establish an additional theorem. The existing ILO ancestry is retained as context, not claimed as a newly read source.

## Corrections and limitations

The imported statement is true, including empty schemes and zero rings; no STATEMENT-DISPUTED correction was necessary. Its source.place left the scheme inputs unspecified. The proof now records their precise Stacks tags and labels, and supplies the open-cover argument rather than asserting descent of quasi-compactness. It explains the identification of A with its image in B rather than treating an injective ring map as a literal inclusion.

The field is not assumed algebraically closed, the schemes are not assumed separated, and q is not assumed flat. No such hypothesis is used. In particular we never infer finite type of an arbitrary open by assuming its open immersion is quasi-compact. Instead the affine-pair characterization applies directly to each affine inverse image. No normality, group action or quotient construction is needed here.

All work is finished subject to delivery validation. No Lean was written and no compiler, Lake or build was invoked.

## Search results and reuse

Read the current chapter and unit records and the latest blueprint unit at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This item is a below-unit prerequisite for the existing finite-quotient route; neither chapter nor unit was changed. blueprint_refs ancestor returns None, matching the retained metadata. Whole-blueprint searches for Artin.Tate, injective section, affine pairs and finite type.*subalgebra found no equivalent blueprint node; the broad Noetherian search located the existing general inputs. DAG searches included 00IS, 01T2, 01T6, 01WH, Noetherian affine rings, finite affine covers and finite-type charts. Read the existing lem-sfb-artin-tate-subalgebra-finite-type in full: it is already an exact Mathlib leaf, so it is cited rather than duplicated. The invariant-subalgebra transfer lemma assumes an action and is not needed.

Six required msearch calls were run and their actual logged queries and hit summaries appended to the item. Both LeanFinder phrasings returned finite-map and affine-pair inputs. Loogle returned finite implies locally finite type and related characterizations. LeanSearch returned finite-map definitions and locally finite-type inputs. The grep hits included Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean:35, whose descent assumes flatness, and Finite.lean:40, whose finite_app is just module finiteness. Read those files and FiniteType.lean:38-55. Read fg_of_fg_of_fg at Mathlib/RingTheory/Adjoin/Tower.lean:145-154: it is Artin--Tate, already represented by the existing cited leaf, not a one-line proof of the entire item.

## Not duplicates

No new nodes were created. All general-purpose inputs already exist and were reused, including the finite affine cover, affine-pair finite-type criterion, finite-morphism definition, finite-type affine Noetherianity and Artin--Tate.

## Review by Q112

I read Stacks morphisms.tex Tag 01T2 (lemma-locally-finite-type-characterize, at line 2673), 01T6 (lemma-finite-type-noetherian, at line 2765), 01WH (definition-integral, finite clause, at line 10957), algebra.tex Tag 00IS (lemma-Artin-Tate, at line 12297), and Tag 00FN (lemma-Noetherian-permanence, at line 5991). I also read properties.tex Tag 01OV (definition-noetherian). The proof is marked agent-written because it assembles these inputs with two explicit elementary arguments, not because the cited individual theorems are unverified. For the existing affine-algebra input I read the current blueprint statement and proof under latest/blueprint/sec-algebraic-groups-lie-algebras/sk-p-geometry/lem-wf-affine-noetherian-components: it gives exactly Noetherianity of any finite-type algebra over any field. No new-node sources require review.

Step 1 uses def-weil-finite-type-morphism for exactly its locally finite type and quasi-compact clauses. Since the whole target Spec k is affine, the definition gives quasi-compactness of X. I read lem-pqf-finite-affine-cover-qc-open: it applies to the whole open of any quasi-compact scheme, without separatedness or Noetherianity. Its finite cover therefore exists here. I read lem-weil-pbc-lft-affine-pairs: it quantifies over EVERY affine source open and affine target open whose images lie in the target open. Applying it to each W_i and the whole Spec k supplies precisely the finite-type algebra claimed.

Step 2 cites lem-wf-affine-noetherian-components only for the ring-Noetherian clause, after step 1 has supplied its field and finite-type hypotheses. pqf-def-locnoeth defines locally Noetherian by an affine cover with Noetherian coordinate rings, exactly the cover just constructed. The remaining conjunction with quasi-compactness is the definition in the item and 01OV, not a new theorem. Empty X has the empty cover.

Step 3 is genuinely elementary: given a cover, pull it back, take a finite subcover using the established quasi-compactness of X, and lift each z through the surjection to show that its image lies in a chosen open. I read def-weil-surjective-morphism: its statement is exactly the point-lifting assertion used. Continuity is part of the scheme morphism data. The argument uses no closed-map, proper-map or fpqc descent lemma.

Step 4 applies the same finite-cover lemma to the whole open of Z, now proved quasi-compact, and then considers ANY affine V, not only a selected member of the cover. I read def-weil-finite-integral-morphism: its finite clause explicitly gives affineness of q and finite generation of B as an A-module on every affine inverse image. This is definitional unpacking, not a theorem cited from a definition. The same affine-pair lemma applies to U=q^{-1}V inside X and the whole Spec k, since a is locally finite type and U is affine. Thus B is finite type over k, with no quasi-compact-open-immersion assumption.

Step 5 cites lem-sfb-artin-tate-subalgebra-finite-type. I checked its statement against 00IS: the base must be a commutative Noetherian ring, the ambient algebra must be finite type over it, and the subalgebra must make that ambient algebra a finite module. The field k is Noetherian by the explicit ideal argument in the step. The relation bq=a gives the scalar compatibility by functoriality of the structure-sheaf maps. Injectivity identifies A with its actual image T; the displayed replacement of coefficients checks module finiteness over T. Step 4 supplies finite type of B. Artin--Tate then gives finite type of T; lifting its generators proves finite type of A. No unproved descent theorem or invariant-theory assertion is hidden here.

Step 6 uses precisely the Noetherian-ring clause of lem-wf-affine-noetherian-components for A with its now-established finite-type k-algebra structure. This yields the final clause for every affine V. It does not claim that arbitrary subrings of Noetherian rings are Noetherian: Artin--Tate is essential in the preceding step.

I checked all eleven citations against the FULL statements of their files and recorded those statements verbatim in citations.json; every cited node exists and is unmerged. All proof dependencies are exactly the union of the step uses. Every non-elementary input is a cited node. Every step is shorter than 2000 characters. There is no newly created clause standing in for the item, and no cycle through the parent quotient theorem.

Small cases checked: X=Z=empty forces both coordinate rings of an empty chart to be the zero ring; a k-algebra may be zero, so Artin--Tate applies without any domain or nontriviality hypothesis. When X is empty, surjectivity forces Z empty and the cover can be empty. For q an identity, this specializes to arbitrary affine opens of a finite-type k-scheme. For an injective integral finite map of affine rings A subset B, it reduces to the usual Artin--Tate statement. A finite nilpotent thickening still satisfies the proof when its section map is injective; a finite surjection killing nilpotents can fail injectivity, and is correctly outside the hypotheses. None of the arguments use irreducibility, connectedness or characteristic restrictions.

Checked delivery-errors B--E: no new unsplit statements or missing notion definitions; no invented searches; no source tags used as substitute dependencies; no proof of a cited node used as an interface; no elementary node manufactured; no hidden flatness, separatedness or nonempty hypothesis; no assertion of a comparison without its coefficient argument; no prohibited SGA source.

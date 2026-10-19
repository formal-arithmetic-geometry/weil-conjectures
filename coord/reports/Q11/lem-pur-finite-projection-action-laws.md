# Q11: lem-pur-finite-projection-action-laws

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-projection-action-laws.json`: statement, split into eight proof steps; no exact Mathlib match for the package. Its statement, hypotheses and coefficient categories are unchanged.
- `citations.json`: 21 records, one for each step/node citation, copied verbatim from the current cited statements.
- `report.md`: this report. `searches.jsonl` records the actual Q11 search calls. `write_split.py` is sandbox-only preparation, not a project file.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

No attachment for the item. Searching the project source by the exact blueprint tag and by projection/action/associativity/counit terminology did not find a finished declaration covering every clause. `CategoryTheory.Adjunction.rightAdjointProjectionMap_assoc` (ProjectionMapAssoc.lean:45) and `CategoryTheory.Adjunction.projectionMap_assoc` (:71) provide generic associativity ingredients, but do not state this whole item with its open counit, compactification, and two coefficient sites. I read both proofs and the generic projection-map definition in ProjectionMap.lean. The etale `hasProjectionFormula_comp` in Derived/ProjectionFormula.lean:350 is an invertibility statement, explicitly documented there as the objectwise shadow of coherence rather than equality of maps. It is not an attachment for this item.

## WANTED

None. The relevant Stacks source is available locally.

## What was wrong or incomplete

The item was unsplit and had no proof. Its source and blueprint ancestry mention an “Expanded Step 6”. I read the current main-20261015 projection-purity-agreement proof: it is the shorter Kummer/diagonal/DNC comparison and has no such numbered expanded step. The current DAG parent also has a rewritten proof. I retained the creation metadata and recorded a precise thematic ancestry, without claiming that the absent expanded text is a human proof. This proof is therefore marked `proof_origin.by = agent`, with the actual Stacks definitions used.

There is no statement dispute. All displayed compositions are well typed after their specified associators and inverse-image tensor comparisons. The final ordinary-etale assertion is proved separately on its own site; no etale/pro-etale equivalence is assumed. The compactification assertion is for the chosen composite, so no independence theorem is needed. In particular `lem-amb-unbounded-compact-support-comparisons` remains a statement dependency of the inherited formulation but is not used in the calculation.

## Source and search record

Read the chapter and unit records, the main-20261015 model proof and current DAG parent, and these actual Stacks sources:

- sites-cohomology.tex Tag 0B56, `equation-projection-formula-map`: the counit-defined map, without invertibility assumptions; Tag 07A4, `lemma-pullback-tensor-product`: K-flat tensor/pullback representatives; Tag 0GL1, `lemma-j-shriek-and-tensor`: unbounded derived open tensor comparison.
- sites-modules.tex Tag 0E8I, `lemma-j-shriek-and-tensor`: the open comparison constructed through the natural Hom adjunctions. The preceding section's open adjunction is represented in the cited existing nodes.
- The tag table identifies these labels exactly. The tensor reassociation used here is the conventional one in Tag 0FPT, as stated in the cited generic derived-monoidal node.

I searched the whole DAG by projection, monoidal, adjunction, open tensor and normalization terminology; inspected the cited statements and their dependency lists; and searched the whole imported blueprint with blueprint_refs.py for “projection formula”, “tensor-action”, “pullback associativity”, and “j-shriek-and-tensor”. None states the full package in another form; `same_as` stays empty. Existing normalizations were reused rather than making new versions of the item's clauses.

The Q11 searches in searches.jsonl include two LeanFinder phrasings, Loogle, Mathlib grep and LeanSearch. The latter services returned results, so none is recorded as unavailable. I read the relevant generic adjunction and monoidal matches: Mathlib/CategoryTheory/Monoidal/Functor.lean supplies the lax-right-adjoint and monoidal-counit formulas; Adjunction/Basic.lean supplies adjunction and counit naturality. These are formal ingredients, not an exact or one-line specialization covering the named derived maps and their open/compactification identifications. Existing Mathlib adjunction node lem-weil-pbc-adjunction-of-natural-bijection supplies the bijection and triangle identities actually used. The unrelated coalgebra, augmented simplex and cartesian-product results do not concern this projection transformation. The five inherited Q21 search records were preserved; Q11 records append only the queries that Q11 actually ran.

## Review by Q11

I checked B through E of delivery-errors.md against the completed JSON, the cited statements and the Stacks constructions, not just against the schema. There are no new statements to leave underspecified and no new nodes whose searches, sources or definitions could be missing. The nontrivial facts below are all statements of existing cited nodes; the elementary portions are the displayed transpose calculations.

Step 1 uses the finite-level, ambient-unbounded clause of lem-pur-derived-pullback-tensor-iso, including its explicit associativity and composition clauses. I do not use its integral or rational assertions. The etale comparison and preservation of K-flat flat-term representatives are stated in lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The canonical associator on such representatives is stated by lem-sf-ringed-derived-closed-symmetric-monoidal. The localization equivalence stated by lem-weil-pbc-site-derived-tensor-descent permits checking equality on representatives; applied to each of three factors it gives the three-variable check. The displayed pure-tensor formula verifies the comparison normalization, with no permutation or Koszul sign. The sites are taken in the fixed universe of the ambient category, so the small-site hypotheses are met.

Step 2 reads the actual projection-mate formula from def-exchange-projection and, independently for etale objects, def-kun-projection-formula-map. Both allow arbitrary unbounded inputs. The Hom bijection and inverse formula in lem-weil-pbc-adjunction-of-natural-bijection give the counit identity. I wrote the naturality and triangle cancellation out, so no projection-formula invertibility is presumed.

Step 3 uses that same adjunction statement, and the formulas established in Steps 1--2. Both transposes are explicitly e_M tensor the two identities. M_1 and M_12 lie in the ambient categories even when their tensors are unbounded; properness adds no restriction needed in the argument. This is a few-line formal argument, not a new proper projection-action lemma concealed in a node.

Step 4 uses exactly the statement of lem-sf-open-tensor-normalization: its inverse gamma is the open-unit adjunct, and its last constant-finite clause identifies gamma with lem-cbc-extension-zero-projection-formula. Our A is a finite commutative ring, and the scheme open immersion gives the localized ringed site required there. I used no part of that node's proof. The adjunction bijection statement gives the equation for Q(kappa) followed by the unit.

Step 5 checks the etale map without borrowing a pro-etale normalization. The statement of lem-pur-etale-open-derived-tensor says explicitly that its canonical map is induced by the sheaf tensor identity and totalization and allows all unbounded objects. The sheaf-adjunction statement lem-weil-pbc-extension-by-zero-adjunction specifies its counit on sections over the open. The inverse sheaf tensor map therefore has the displayed unit transpose, which persists under totalization with a K-flat representative of the base tensor factor. The cited generic derived-pullback/tensor node guarantees that its restriction remains K-flat; lem-weil-pbc-extension-by-zero-exact provides exact degreewise zero extension. These hypotheses are met for the ordinary etale open and our commutative A. I did not infer equality of derived arrows from equality of their cohomology or their geometric stalks.

Step 6 uses only the established open-transpose formula, the fixed tensor comparisons, and the bijective adjunction statement. Its two transposes are explicitly the same unit tensored with two identities. Reversing the equality of the inverse maps gives the required order of the two forward delta maps.

Step 7 uses the same adjunction statement and its triangle identities; after cancellation of delta, both transposes are explicitly the inverse tensor comparison. This checks the actual open counit and the actual mu inverse appearing in the item, not an unspecified replacement counit. No faithfulness of Q on arbitrary objects is used.

Step 8 expands the exact chosen-compactification definition in def-exchange-projection. Naturality of pi moves the open tensor map through the proper projection, after which Steps 3 and 6 give the two equalities written there. The composite-pullback tensor compatibility is explicitly supplied in the finite clause of lem-pur-derived-pullback-tensor-iso, and in the etale statement of lem-kun-derived-pullback-composition-monoidal. The ordinary etale functor is exactly Rr_* Dj_! in def-amb-etale-compact-support, and its proper map is the counit mate in def-kun-projection-formula-map. Finite-type schemes over our field are Noetherian, as required by the compact-support definition; the chosen compactification in the hypothesis supplies j and p. I never use a compactification-independent transformation or invertibility of a proper projection map. The equality is natural in M, N_1 and N_2 by the specified transformations.

All off-unit theorem citations used as generic tools are declared in split_report.tool_uses with their reasons. They supply only ambient tensor structure, open-map normalization and exactness, or pullback comparison data. They do not replace any diagonal/DNC argument in sk-thm-smooth-purity and use no SGA source.

Edge cases checked: u and j identities give identity maps under the unit identifications; U empty gives zero-source open maps and the unique equal composites; any zero input makes both composites zero; N_1 or N_2 equal to the tensor unit gives the one-factor formula; odd-degree shifted inputs introduce no additional sign because no factors are interchanged. A may be nonregular (so derived tensors of bounded objects can be unbounded); using the ambient categories throughout preserves all types. A compactification of the empty morphism and the proper case j = identity reduce to the same computations.

No proof step exceeds 2,000 characters (maximum 1,259). I read each whole step for hidden subclaims: all comparison/normalization facts are cited, while the remaining subcalculations are displayed formal adjunction or representative tensor calculations. No clause was offloaded to a new node. Every quote in citations.json was checked as a verbatim substring of the corresponding current statement.

## Not duplicates

No new nodes; there are no new/existing-node pairs to distinguish.

## What remains

Only the required server dry run and delivery remain. There is no unfinished mathematical clause in this split.

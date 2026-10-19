# Stage-1 report: lem-coef-finite-direct-image

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-direct-image.json`: existing statement retained and existing expanded proof divided into twelve steps; status split. Mathlib verdict: no match.
- `citations.json`: a verbatim statement quotation for every node cited in each step.
- `searches.jsonl`: actual logged Mathlib searches; the inherited searches in the item were retained, and this run's searches appended.

No new nodes and no new Mathlib leaves.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, the item id and `finiteCoefficientDirectImageMap`, and the master reference tree for the same names. There is no matching project declaration there. The inherited `lean` field records a separate Sheaf module and is not evidence of a finished declaration in the named source checkout. I did not compile or edit Lean.

## WANTED

None for this split. The current main-20261015 blueprint statement and proof and the relevant Stacks ringed-topos material are present locally.

## Not duplicates

No new nodes, hence no new-node duplicate pairs. Blueprint searches for `finite direct image coefficient`, `coefficient change`, and `finite coefficient`, and DAG searches for finite coefficient change, found this item, coefficient definitions, broader scalar-six assertions and other operations. None is an alternative node giving this same specified ordinary finite-ring map with both coherence identities and its pro-etale assertion. In particular the condensed coefficient-change nodes concern a different coefficient category; they were not silently substituted.

## What was wrong or changed

The shared item was `unsplit` but already contained a detailed four-paragraph proof and historical review/Lean records. The sandbox initially contained only brief marker files. The first dry run therefore reported no node files. I copied the shared item and retained its statement, source, existing citations/searches and historical metadata. I separated its long paragraphs into independently reviewable steps and updated the internal step references, proof dependency union, split report and current search records. No statement correction or route change was needed. Its imported blueprint identity has `from: null`, not an unspecified ancestry; `same_as: []` was confirmed by the searches.

## What I could not finish

Nothing remains in the stage-1 split. This delivery asserts a complete natural-language split, not closed Lean proofs of its dependencies.

## Review by Q40

I read the item's historical master blueprint text, its current main-20261015 statement and proof, the fixed chapter record, and the `sk-prop-sf-biduality-general` unit record. The route remains finite-coefficient projection via uniform etale cohomological dimension, followed by counit computations and etale-origin pro-etale comparison. I also read Stacks `sites-cohomology.tex`, label `lemma-pullback-tensor-product` (07A4), `lemma-adjoint` (07A6), and `lemma-derived-pushforward-composition` (0D6E), which give the tensor/adjunction/composition conventions used here. No SGA source is used. For every cited node I opened and read its statement and recorded that exact statement as the quotation in citations.json; I do not use an argument hidden inside another node's proof.

Step 1 uses the coefficient datum's DVR factorization and finite quotient, the finite-dimension node, the etale direct-image vanishing theorem and the direct-image Tor-amplitude theorem. I checked the finite-type hypotheses, the prime-to-characteristic annihilator, and the requirement that the vanishing bound be uniform for all module sheaves. The empty source is treated separately with d=0. This also verifies that Rf_*K is a permitted bounded constructible finite-Tor input to the comparison for g.

Step 2 uses exactly the finitely-presented-constant projection theorem with M=B; finiteness of A gives Noetherianity and a finite presentation of B by the explicit finite-kernel argument. K is bounded, hence bounded above as required. The ordinary tensor and projection-map definitions specify the same K-injective derived functor and counit map as the bounded-below definition. Step 3 uses derived change of rings, the ringed-topos adjunction and pullback/tensor comparison to construct the map in D(B) before forgetting scalars. These statements provide an actual adjunction and natural tensor identification, not only the existence of an unspecified isomorphism.

Step 4 uses the etale constructible flat-model clause of lem-sf-flat-model and both bounded-below restriction-of-scalars comparison nodes. The model is bounded, so the comparison hypotheses apply even when B is not flat over A. Their explicit counit identity identifies this particular B-linear mate with the A-linear projection map. Restriction detects a zero cone because it keeps the underlying cohomology sheaves; no faithfulness of derived restriction is claimed. Step 5 writes out constructibility under finite tensor on a common stratification and the injection calculation proving that P tensor B is B-flat. It applies the same reasoning to a flat model of Rf_*K. Since B is finite as a set, it is Noetherian; the restriction comparison gives the same uniform N for all B-module sheaves. Thus the finite-constant projection theorem also applies over B to a further finite algebra C. No assumption that K_B has finite Tor amplitude over A is used.

Step 6 uses the actual adjunction and scalar-extension functor to write the defining transpose identity and derive naturality by the counit's naturality and injectivity of the Hom bijection. Step 7 uses the direct-image composition node's etale clause (all commutative coefficient rings) and writes the pasted counit, then computes both B-transposes. Step 8 computes both C-transposes for a coefficient chain and supplies the elementary balancing maps for tensor reassociation; the pullback/tensor comparison and restriction counit node specify compatibility. These are calculations in D(B) and D(C), not deductions from equality after restriction.

Step 9 uses quasi-compactness and quasi-separatedness from finite type and separatedness to apply the bounded-below etale/pro-etale direct-image comparison with both finite rings A and B. Its canonical-mate node states the required counit normalization. Exact comparison pullback, preservation of flatness and the ordinary module pullback/tensor isomorphism give the tensor identification on the bounded flat models; the displayed composite therefore consists of isomorphisms. Step 10 takes the pro-etale B-adjunction transpose of that composite and successively uses the two canonical-mate normalizations and Step 6 to identify it with the specified pro-etale coefficient map. Step 11 computes both transposes for composition and for a coefficient chain in the pro-etale adjunction. Step 12 uses the comparison Tor-amplitude theorem only for the A_{E,n} objects to which it applies; B-constructibility comes instead from the bounded constructible B-model and exact pullback. Thus no A_{E,n}-only theorem is applied to an arbitrary B.

I checked identity morphisms, A=B, the zero complex, empty schemes and a nonflat quotient B of A. The proof does not assert that a finite B has a finite free A-resolution, and all the maps remain the ordinary uncompleted ones. I checked delivery-errors B–E: no new elementary or duplicate nodes, no circular restatement, no missing non-elementary theorem in a step, no use of a definition as if it asserted invertibility, and no unsupported transport of a named morphism. The old long steps contained several applications and coherence calculations; these now appear as separate short steps, and the remaining elementary balancing/stratification calculations need no new lemma node.

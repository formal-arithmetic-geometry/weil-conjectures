# Worker report — Q99

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-universal-translation-multiplier.json: statement, split using existing nodes; no new nodes and no new Mathlib leaves.
- citations.json: 18 entries, one for each step/node pair, with literal excerpts of the live statements.
- searches.jsonl: five actual searches for the item, recorded by msearch.py. The item retains its inherited Q88 searches as historical records and adds the five Q99 searches.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, universal translation/multiplier names, and translation/trace in the six-functor etale source. No project declaration stating this item was found. The upstream sorry declarations are not treated as finished proofs.

## WANTED

None. The proof follows the available current blueprint and Stacks sources. Its origin is agent because the blueprint itself was written by agents; no SGA source is used.

## Corrections and route

Process correction: my first resume inspection mistakenly included a read-only git status in the shared repository, contrary to the brief. It made no changes. I stopped using git there; all subsequent repository access was direct file reading and permitted searches.

The live item was statement-only, with no proof or proof dependencies. The sandbox contained dispatch markers only, not a previous split, report, search log or delivery process. I retained the statement, its statement dependencies, source, creation record and blueprint ancestry. Seven proof steps now realize the coefficient-line paragraph of current sk-prop-sp-orientation-vector-bundle.proof.md Step 1, as used in sk-thm-smooth-purity's Agreement on the model. The connected-fibre argument belongs to the parent lem-pur-affine-translation-trace and is not repeated here.

There is no statement dispute. In particular, the arbitrary finite commutative coefficient ring and arbitrary Noetherian base are retained. The existing lem-pur-lisse-rank-one-aut is NOT used: it assumes the chapter's special residue coefficients, separated finite-type schemes over k, and the pro-etale site. The existing generic derived-single full-faithfulness node and the direct evaluation-at-1 calculation give exactly what is needed without those extra hypotheses.

The only off-unit facts are generic tools, declared individually in split_report.tool_uses: affine coordinate geometry, Noetherian quasi-separatedness and topology, Nagata compactification, canonical Tate inverse image, compact action coherence, the normalized affine trace, bounded-below/unbounded compact-support comparison, the constant-section description, and exact inverse image of constant-ring modules. The derived-single node is already a Mathlib leaf. None replaces a step of the unit's purity route.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own proof obligations. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes. DAG and blueprint searches for translation, unit multiplier, rank-one automorphisms and constant-sheaf endomorphisms found the parent, the linear-action analogue, and the special-coefficient pro-etale rank-one node. Those do not state this general ordinary-etale multiplier lemma. I reused lem-weil-pbc-derived-single-fully-faithful instead of creating a degree-zero Hom node. The elementary evaluation-at-1 and unit calculations stay inside the proof.

## Mathlib searches

All five Q99 queries were run with msearch.py and their logged results were read. The first semantic query returned affine-coordinate composition, inverse-limit identities and a locally-constant presheaf restriction, not a compact-support translation theorem. Loogle returned general derived-category quasi-isomorphism and fraction lemmas. Grep returned only tactic translation traces. LeanSearch returned locally-constant comap, condensed constant-sheaf units and continuous linear automorphisms of a scalar ring, none identifying this etale action. The second semantic phrasing returned generic sheaf global sections and constant-sheaf interfaces; these are not the normalized compact-support action with the stated exchange equations. The established full/faithful singleFunctor Mathlib leaf was read at Mathlib/Algebra/Homology/DerivedCategory/FullyFaithful.lean, lines 37 and 45. The generic global-sections interface was also inspected; it does not supply this whole item.

## Review by Q99

I read the current main-20261015 vector-bundle orientation proof Step 1 in full, the unit sk-thm-smooth-purity including Agreement on the model, and the chapter record. I also read the affine-space-top-trace proof and linear-trace-invariance proof under sk-prop-an, Stacks derived.tex Tag 06XS (lemma-negative-exts, part 2), etale-cohomology.tex Tag 03P5 (remark-constant-locally-constant-maps), sites.tex Tag 00YV (proposition-functoriality-algebraic-structures-topoi), properties.tex Tags 01OY and 01OZ, and more-etale.tex Tags 0F7H/0F7I/0F7L. For compactification existence I read the current blueprint thm-nagata-compactification statement and proof. I opened the live statement of every cited node and checked the following uses against it.

Step 1 uses def-amb-affine-trace-tower's actual statement: it explicitly gives Noetherianity of the stages, separated finite-type projections, coordinates and persistence of N-invertibility. No geometry theorem is inferred from a mere name of a definition. The quasi-separatedness node applies since the finite affine Noetherian cover implies local Noetherianity. The finite cover supplies quasi-compactness. Thus the stated hypothesis of thm-nagata-compactification is met. I initially left the Noetherian topology implication implicit, then repaired it: the closed-subsets-minimal node supplies the minimal complement of a finite union in a cover, and the step writes the two-line covering argument. This ensures that the chosen open compactification part is quasi-compact, as the action node requires. The translation and its inverse are the displayed inverse polynomial substitutions, so no group-scheme translation theorem is being assumed.

Step 2 uses all four cited statements precisely: the Tate node supplies an actual isomorphism and its composition compatibility; the action node supplies the automorphism for f=q_P with the given theta; the trace node says the specified coordinate counit is an isomorphism; the unbounded-comparison node explicitly says that its exchanges restrict to the same bounded-below normalization. The input is a single sheaf shifted by 2d, so it is bounded below. The coefficient hypotheses finite A, NA=0 and N invertible are those of the trace node. This does not invoke smooth purity or trace invariance to prove itself.

Step 3 uses the Hom bijection of lem-weil-pbc-derived-single-fully-faithful for the abelian category of module sheaves, not a restricted constructible category. Applying it to alpha and alpha inverse gives h and k, and faithfulness gives both inverse equations. Step 4 then writes the complete scalar argument on every etale object: A-linearity implies h_U(x)=x h_U(1), and naturality identifies h_U(1) with the restriction of h_P(1). Applying the same calculation to k constructs the inverse section. Uniqueness is obtained by faithfulness followed by evaluation at 1. This is elementary and creates no auxiliary node restating a clause of the item.

Step 5 uses the constant-section node only for its actual statement, an additive-group isomorphism taking constant sections to constant functions. That suffices: apply it separately to b and its inverse c; on constant open neighbourhoods the ring equation bc=1 forces unit values. The compatibility with multiplication is verified on these opens and glued, rather than falsely attributing a ring-isomorphism assertion to a node that states only an additive-group isomorphism.

Step 6 takes the first displayed exchange equation exactly from the compact-action statement and the second exactly from the normalized-trace statement. Their coefficient/Tate normalizations coincide by step 2 and the explicit bounded-below restriction clause of the unbounded-comparison statement. I wrote the conjugation calculation, inserting the exchange and its inverse, so no unexplained 'transport' hides the naturality assertion. The constant-left-module-inverse-image node states preservation of the constant ring, algebraic operations and exactness for arbitrary geometric morphisms. Applied termwise, it identifies pullback of multiplication with multiplication by the pulled-back section; no flatness of u is assumed. T Noetherian suffices; the argument makes no finite-type hypothesis on u.

Step 7 uses the identity/composition clauses of Tate pullback and the explicit rho_(1,1)=1 clause of the action node. At zero the polynomial translation is the identity. Faithfulness of the same single functor and evaluation at 1 then give e*b=1 as a section, not just a stalkwise or cohomological assertion.

I checked d=0, empty S and T, disconnected and nonreduced bases, the zero coefficient ring (including N=1), and composite annihilating N. In the zero ring the sole element is also the unit, so evaluating at 1 still proves uniqueness; on the empty scheme there is a unique section. No step needs connectedness, reducedness, a field, a prime coefficient ring, positive d or an actual base point. Every proof step is below 2000 characters and contains no hidden separate comparison theorem. No new node needs a small-case check or duplicate-tag justification. The proof-dependency list is exactly the union of uses, and every citations.json quote was checked as a literal substring of its node's statement. The required server dry run is the final delivery check.

## Verification

The server review_split check passed, followed by the full deliver.py --no-push preflight (OK, temporary commit 3a115a41ec9). The report was updated to record the initial read-only git inspection error while that first snapshot was being checked, so the final sandbox snapshot is dry-run again before pushing. Direct JSON checks confirmed the live statement and stmt_deps are unchanged, all 18 citation excerpts remain verbatim, and no proof step exceeds 2000 characters.

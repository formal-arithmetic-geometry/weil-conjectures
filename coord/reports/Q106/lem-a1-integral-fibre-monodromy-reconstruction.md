# Stage-1 delivery: lem-a1-integral-fibre-monodromy-reconstruction

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-integral-fibre-monodromy-reconstruction.json: statement item, now split in seven steps; no Mathlib match for the whole assertion.
- citations.json: one verbatim statement quotation for every proof-step citation.
- searches.jsonl: actual msearch.py results, retained as emitted.
- report.md: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The existing Mathlib leaf lem-sc-dvr-fg-torsionfree-free supplies the freeness theorem. In particular, neither finite-free reconstruction nor continuity was repackaged as a new node that merely restates a clause of the item.

## Attachments

None. The exact blueprint tag was absent from lean/WeilConjectures, and searches there for integral reconstruction, monodromy and lisse fibres found no declaration giving all clauses of this item. The rational Qbar-valued LisseMonodromy interface is not this integral finite-E fibre reconstruction. The existing closed general adic-limit algebra node is cited as an input, not offered as an attachment of the item.

## WANTED

None for this split. The inputs concerning local-field integers already have their own source and search records. I created no new local-field result.

## What changed and why

The live node had a statement and searches but no proof. I kept its statement, source, statement dependencies, provenance and blueprint ancestry. I added a proof that uses only existing nodes plus explicit coordinate calculations. The proof does not identify a pro-etale geometric stalk with an inverse limit of stalks: it defines Lambda as the inverse limit of the finite *etale* stalks. This avoids an unjustified exchange of stalks with infinite limits.

The whole-item searches used all four prescribed msearch modes, and a second semantic phrasing. Loogle returned no hits; the first LeanFinder phrasing returned unrelated integral-scheme normalization results; the second returned adic completion and condensed constructions. LeanSearch returned finite-set Galois, locally constant/condensed and profinite-group results, none giving the sheaf statement. The grep hits in Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean and Proetale.lean define coefficient sheaves and sites. I read the former's coefficient and cohomology declarations; they do not reconstruct normalized lisse module towers or identify the specified J_X. The actual queries and names returned have been appended to the inherited search records, without changing the inherited entries.

The source, Bhatt–Scholze Proposition 6.8.4(1), leaves the integral equivalence to the reader, while the proof of Corollary 6.8.5 invokes the finite-free integral representation equivalence. The seven steps give the reconstruction details needed here. Lemma 7.4.7's first sentence is consistent with the integral result, but its rational pro-etale-fundamental-group equivalence is neither used nor conflated with an etale fundamental-group equivalence. In particular no normality condition, finite-image rational action, or global lattice for an arbitrary rational lisse sheaf is inferred.

## Tool uses and route

The item inherits unit sk-p-real-rankin and its ancestry from the lattice argument serving lem-a1-affine-hc0. I read that unit and chapter and the current main-20261015 ancestor text. This item does not realize a unit's key proposition, so no unit fields were edited. The existing finite-monodromy, adic-limit, coefficient-DVR and integral reduction/realization results are generic tools; the exact uses are declared in split_report.tool_uses. The realization lemma is used only for the normalization already assumed in the item, not to replace the prescribed J_X by a different functor. No SGA source is used.

## Not duplicates

No new nodes. Searches of the whole DAG and blueprint for monodromy, inverse limits and lattices located the existing generic results used here. In particular lem-pod-adic-limit-finite-modules states finite generation, quotient recovery and the required topology; lem-sc-dvr-fg-torsionfree-free states precisely the freeness implication after torsion-freeness has been proved. The larger equivariant-adic-fibre realization node has additional pro-etale descent data as hypotheses and was not used to assert their existence here.

## Review by Q106

I read delivery-errors sections B–E in full, including their repeated archived version, and checked the node against those content requirements. The main source read was Bhatt–Scholze pp. 59–60 (Definition 6.8.3, Proposition 6.8.4 and Corollary 6.8.5), together with p. 70, first sentence of the proof of Lemma 7.4.7. For the general algebra input I read Stacks algebra.tex, lemma-limit-complete (Tag 09B8) and lemma-finite-over-complete-ring (Tag 031D); for the freeness leaf I read more-algebra.tex, lemma-dedekind-torsion-free-flat (Tag 0AUW), including part (3). There are no new-node sources to review.

Step 1 uses the statement of lem-per-lisse-completed-system-comparison for the normalized finite locally free etale tower. The statement of cor-galois-lisse-representations(1) explicitly supplies the continuous discrete action, equivariance of maps, and finite-ring scalar-extension compatibility. Therefore applying it to A/varpi^(n+1) -> A/varpi^n gives the required quotient transitions, not just arbitrary maps of fibres. The base is connected with a geometric point, the rings are finite, and the etale local free trivializations make the stalk modules finite free.

Step 2 uses exactly part (1) of lem-pod-adic-limit-finite-modules: its finite-module and normalized-transition hypotheses were obtained in Step 1. It concludes finite generation, the canonical quotient isomorphisms, and equality of the inverse-limit and adic topologies. The action and equivariance of the quotient maps are established by the displayed coordinatewise formula, not borrowed from the algebra lemma's proof.

Step 3 does not claim that an inverse limit of torsion-free modules is torsion-free (the finite quotients are not torsion-free). It proves injectivity of varpi by looking one level higher and calculating its annihilator in a free quotient module. The statement of lem-weil-l-adic-extension-integers-dvr gives a domain DVR and uniformizer factorization, so this suffices for torsion-freeness under every nonzero scalar. Then the statement of lem-sc-dvr-fg-torsionfree-free applies with finite generation from Step 2. No freeness theorem is taken from a definition node.

Step 4 cites cor-galois-lisse-representations(1) only for its continuous finite actions. The rest is the definition of the product/subspace inverse-limit topology: inverse images of basic open sets are finite intersections. This explicitly proves continuity on Pi times Lambda. Step 5 gives an independent coordinate check for scalar extension: an A-basis gives A^d inside E^d; the valuation-factorization statement identifies the topology and the open cover by varpi^(-r)A^d. On each member the action is the conjugate by scalar homeomorphisms of the already continuous integral action. The open cover proves joint continuity for V, and the coordinate inclusion proves injectivity and the lattice property. These are short elementary calculations, not uncited analytic comparison theorems.

Step 6 uses the full faithfulness of the *finite-coefficient* equivalence. Each fibre identification lifts to a sheaf isomorphism, and faithfulness proves its compatibility with the actual transitions by comparing the two composites on fibres. It does not use merely an isomorphism of objects and silently assume compatibility of diagrams.

Step 7 uses the normalization formula written in lem-sfb-etale-local-monodromy-realization and assumed for the specified J_X, with simultaneous normalization data explicitly introduced in def-sfb-monodromy-realization-data. The stable finite free lattice and jointly continuous representation needed for that formula were proved in Steps 3–5. The level indexing n+1 in that data is reindexed to positive n. Step 6 gives an isomorphism of the full normalized diagrams, whose limit isomorphism and inverse are induced from those diagrams. The inverse-limit comparison in lem-per-lisse-completed-system-comparison identifies that integral module with M. The coefficient identification is exactly the one asserted in lem-sfb-integral-lisse-reduction-equivalence; the DVR factorization of ell with positive uniformizer exponent shows ell and varpi yield the same localization. Thus the concluding isomorphism is for the given J_X. No unproved essential-surjectivity or normality assertion is used.

I copied every proof-step citation from the cited node's statement into citations.json and checked each quoted substring. I also checked that none of these input nodes reaches the item, so the new proof edges do not introduce a dependency cycle. Each proof step is under 2000 characters and contains one routine argument; there is no hidden long-step lemma to extract. B1–B10 do not require new nodes here: existing sources and the existing Mathlib leaf are reused, statement and blueprint meaning are preserved, and search records are actual calls. C1/C4 are met by the precise statement-level uses described above; the elementary topology and coordinate calculations are fully written out. D1/D2 are avoided by creating no replacement clauses or omnibus node. E's hypothesis, object and compatibility checks were made at the actual finite etale levels and for the stipulated realization.

Small-case checks: for the zero module all quotient stalks, Lambda and V are zero and every step still applies; for a geometric point and M=B_X^d the construction is the usual system (A/varpi^n)^d, with Lambda=A^d and V=E^d; nontrivial finite quotient monodromy is retained because all quotient isomorphisms are equivariant. A constant tower A/varpi with identity transitions would have torsion, but is excluded by the finite-*free over A/varpi^n* hypothesis at n>1. No empty-base case is asserted since the item assumes nonempty connected X. The proof uses no normality, so a nonnormal connected base introduces no additional unsupported inference.

## Unfinished work

None in the stage-1 split. Delivery validation and push results are recorded below after the required tool completes.

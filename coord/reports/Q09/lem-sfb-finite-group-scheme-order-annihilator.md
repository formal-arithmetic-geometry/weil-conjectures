# Stage-1 delivery: lem-sfb-finite-group-scheme-order-annihilator

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-scheme-order-annihilator.json: the item, now split into seven steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-commutative-group-local-constant-product.json: statement, unsplit; the local/constant structural decomposition over an algebraically closed field and its coordinate description. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-faithful-regular-matrices.json: statement, unsplit; closed regular matrix representation, including its coordinate surjectivity. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-additive-group-card-annihilator.json: statement, Mathlib leaf, card_nsmul_eq_zero' in Mathlib/GroupTheory/OrderOfElement.lean, generated at lines 1185-1187 (Fintype variant at 1190-1192).
- citations.json: verbatim statements for each citation of each numbered proof step.
- report.md: this report. searches.jsonl was retained and extended by the required search command. The interrupted attempt's milne-iAG.txt source extraction is retained as scratch material.

## Attachments

No attachment for the item. I searched the live WeilConjectures source both for the exact node tag/id and annihilation/order/multiplication terminology. GroupScheme/Finite.lean proves the connected-order, prime-to-characteristic etaleness and finite-etale point-count results, but no declaration gives the item's equality on arbitrary test algebras. The existing closed lem-sc-connected-finite-order is cited rather than recreated. No Lean was written or compiled.

## WANTED

None. Milne's Algebraic Groups PDF is present in literature/. Its retained text extraction was read. Stacks source for Nakayama and affine fibre products is also present.

## Corrections and route

The item is true with its original hypotheses; no statement dispute or weakening. Milne Proposition 11.32, printed p.221, proves a more general noncommutative assertion, and we use only its commutative case. The argument keeps its etale/connected reduction and regular-representation route. Base change to an algebraic closure makes the finite commutative scheme a direct product, so the extension assembly does not require surjectivity on arbitrary algebra-valued points.

The current blueprint was read under literature/blueprint/latest/: the six-functor chapter, sk-thm-sf-ctf-stability/_section.md and the direct-image proof, plus the connected-order and prime-to-characteristic-etale statements. The item's provenance is a supporting input deep in the alteration, stable-curve level, and abelian-isogeny chain. blueprint_refs.py ancestor reports a null blueprint ancestor for this inherited chain. I preserve that ancestry and its explicit place, and prepend the item to each new node's via list. This changes no chapter or unit route. The three off-unit statements declared in split_report.tool_uses are group-scheme tools needed for Milne's argument, not replacements of a six-functor unit step. The other off-unit proof inputs are existing Mathlib leaves.

## Source error

In the paragraph before Proposition 11.32, p.221, Milne identifies the entries of the matrix (U-I)^p with the entrywise p-th powers of T_ij-delta_ij. That identification is false. For example in characteristic two take U=[[1,1],[1,0]], an invertible matrix. Then V=U-I=[[0,1],[1,1]], and V^2=[[1,1],[1,0]], whereas entrywise squaring leaves V unchanged. The weaker claim actually needed is correct: each entry of the matrix power V^p is a sum of products of p entries of V, so belongs to the p-th ideal power. Step 6 uses exactly this containment; it never asserts entrywise Frobenius. The target statement needs no correction.

## Not duplicates

lem-sfb-finite-commutative-group-local-constant-product vs lem-sfb-group-neutral-component-translates: the existing statement gives open-and-closed identity components and translations but no constant group scheme, group-scheme product isomorphism, local augmented coordinate algebra, or order factorization. The new statement is the finite commutative structural splitting of Milne 11.3, not another translation lemma.

lem-sfb-finite-commutative-group-local-constant-product vs lem-sc-connected-finite-order: the existing statement says the order of a connected finite group scheme in positive characteristic is a characteristic power; the new statement decomposes an arbitrary finite commutative group scheme over an algebraically closed field and does not assert a characteristic power.

lem-sfb-finite-commutative-group-local-constant-product vs lem-wf-algebraic-component-cosets: the existing statement concerns classical closed matrix groups and their abstract component quotient; it does not treat nonreduced finite group schemes or the coordinate-ring product needed here.

lem-sfb-finite-group-faithful-regular-matrices vs lem-sfb-gm-representation-weight-basis: the latter decomposes a specified representation of the multiplicative group into weights; it neither constructs nor proves faithfulness of a representation of an arbitrary finite group scheme.

lem-sfb-finite-additive-group-card-annihilator vs lem-sfb-injective-hom-finite-group-order: the existing statement bounds the order of a group admitting an injective homomorphism to a finite group; it does not assert that the cardinality annihilates each element. The new node is an exact Mathlib leaf.

All three new ids were searched across the full DAG before creation. Whole-blueprint searches included regular representation, connected finite, local algebra, component group, semidirect, local Hopf, matrix representation, finite-dimensional representation, order annihilates, finite group order and annihilates. No node states either new geometric input or the abstract-group identity. The existing connected-order and finite-etale-algebra nodes were opened and reused. The commutative decomposition is not a clause of the item (it contains no annihilation assertion), and the regular representation applies even without commutativity and contains no annihilation assertion. The new inputs are therefore genuine smaller structural tools, not relabellings of the conclusion. Each new node has a statement only and no proof sketch.

## Review by Q09

I read Milne Proposition 11.32 and the preceding matrix calculation on printed pp.220-221 for the item, Theorem 4.9 and its proof on printed p.87 for the faithful regular matrix node, and Proposition 11.3 with its proof on printed p.210 for the local/constant product node. For the latter I also read Propositions 11.1-11.2 on pp.209-210 and Proposition 2.37 on pp.51-52: the identity factor is a local Artinian component, its residue field is the algebraically closed base field, and the split connected-etale sequence becomes a direct product because the group is commutative. The point group is finite and nonempty; component translation gives n=dq. For the Mathlib node I read the actual to_additive attributes and pow_card_eq_one' proof at lines 1185-1192; card_nsmul_eq_zero' has the required arbitrary additive-group hypothesis. Search hits for Tannaka finite groups, ordinary regular representations and Galois-category decompositions were read and rejected because they do not describe a nonreduced group scheme and its closed regular representation. Logged searches from the interrupted attempt were retained and reused; repeat queries in the appended log were to recover full hit signatures absent from the earlier retained summaries. Every recorded query was actually run.

For Step 1 I opened def-sc-group-scheme, which explicitly says a finite group scheme is the spectrum of its finite-dimensional global coordinate algebra. Its identity section supplies the nonzero augmentation. def-weil-algebraic-closure supplies existence of the extension; lem-weil-pbc-fibre-product-affine-spectra explicitly gives Spec(A tensor_k K), its coordinate ring and the maps on projections. Tensor products use def-weil-pbc-module-tensor-product. The remaining dimension preservation and injection are checked on a basis, so no general fpqc descent theorem is invoked implicitly.

For Step 2 I read the new product node and checked that it states every property taken: the local coordinate ring, exact augmentation ideal, group product, and n=dq. The Mathlib leaf asserts qh=0 on the finite group H itself; it is not applied to the generally infinite group G(R). The scheme equality on H_K follows by checking its copies of Spec K. For Step 3 I opened lem-sc-fg-order-prime-etale, whose parenthetical p=0 clause applies to every finite flat group scheme over the algebraically closed field in use. Its finite-flat hypothesis is automatic over a field. lem-sc-finite-etale-algebra-criterion explicitly gives the finite product of separable extensions; algebraic closure collapses these to K, and locality permits only one factor. For Step 4 I opened lem-sc-connected-finite-order and verified connectedness, positive characteristic and flatness for C. It gives exactly d=p^r, including r=0.

For Step 5 I opened lem-weil-pbc-nakayama-jacobson and Stacks algebra.tex lemma-NAK, Tag 00DV, part (2). Each power ideal has a finite K-basis and hence finite B-generators. The maximal ideal of a local ring is precisely its Jacobson radical. Equality of adjacent powers therefore forces that power to vanish; otherwise each drop is strict and lowers finite vector-space dimension. This is a short elementary consequence of the cited Nakayama statement, not an uncited length theorem or a new node.

For Step 6 I checked the new matrix node supplies coordinate surjectivity, identity values and multiplication of matrices for points over every algebra. These imply generation of I by the entries of U-I, also for the inverse determinant generator as written. The two commuting matrices U and I satisfy the usual binomial identity in characteristic p. Matrix powers produce products lying in I^p, as corrected under Source error. Commutativity of C guarantees [p] is an endomorphism, so iterating its coordinate homomorphism gives the displayed ideal-power induction and [p^r]. Killing I and fixing K gives exactly the augmentation followed by the scalar inclusion. Step 7 assembles n=dq on the two factors, uses the explicit coordinate injection to return to k, and evaluates at the universal algebra-valued point to verify the equivalence with a scheme equality. No surjectivity of G(R) to component-valued points over an arbitrary R is assumed.

I tested the statements and assembly on the trivial group (n=d=q=1), constant cyclic groups in any characteristic, alpha_p and mu_p over an algebraically closed characteristic-p field, alpha_(p^r), products of connected and constant factors, nonperfect original fields (the product is invoked only after algebraic closure), and the zero test algebra. These cases confirm that rank rather than geometric point count is essential, that r=0 is handled, and that no reducedness or invertibility is being introduced. The source-error matrix example tests the exact inference repaired in Step 6. All steps are below 2000 characters, so no long step hides a standalone lemma.

Against delivery-errors B-E I checked self-contained statements and inline meanings, unchanged target hypotheses, single TeX escapes, complete source places, actual search records, exact Mathlib file/lines, all cited statements and verbatim quotations, source-dependent hypotheses, no restated conclusion, no definition used as a theorem, no circular dependence, and the distinction between scheme points and arbitrary algebra-valued points. The new nodes have no proof or proof dependencies. I corrected the source's matrix entry assertion and added the existing affine-fibre-product node to Step 1 after the citation audit exposed that implicit comparison.

## Unfinished

No part of the one-level split is left unfinished. The two new unsplit structural statements deliberately join the stage-1 queue. The final required dry run and push are performed with deliver.py; no local DAG/preflight script or compiler is run.

## Dry-run repairs

The first dry run reported two metadata omissions on the abstract-group leaf. I added its finite-set definition dependency (the group operations remain explicitly defined inline), and the dedicated mathlib_match.line field 1186 for the generated declaration. The source attribute and lines were reread. Citations were regenerated from the statements. No mathematical assertion or proof route changed.

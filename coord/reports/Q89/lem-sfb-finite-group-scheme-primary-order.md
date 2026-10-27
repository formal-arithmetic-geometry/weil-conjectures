# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-scheme-primary-order.json`: item split into five steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-sylow-subgroup-cardinality.json`: statement, Mathlib leaf, `Sylow.card_eq_multiplicity`, Mathlib/GroupTheory/Sylow.lean:761.
- `citations.json`: one verbatim statement quotation for every node cited by every step.

One new node, one Mathlib leaf. No Lean files or library files written, no compilation.

## Attachments

None for the item. Searches of the project by its blueprint tag, group-scheme/order terminology and primary-cardinality terminology found no declaration asserting all its clauses. Read `WeilConjectures/AlgebraicGeometry/GroupScheme/Finite.lean`: its `exists_finrankΓ_eq_pow`, `etale_of_not_dvd_finrankΓ` and `card_points_eq_finrankΓ` supply separate structural inputs, not the primary-order statement. Existing nodes already carry these facts. In particular, a proof of the scheme-theoretic comparison cannot be replaced with an abstract finite-group theorem alone.

## WANTED

None. The necessary sources are present.

## Corrections and scope

No statement dispute or change. The starting item was unsplit, with no proof. The source's connected-order input is characteristic-sensitive: in characteristic zero the proof instead uses the explicit characteristic-zero clause of the existing etaleness node, then the finite-etale point-count node. In positive characteristic it uses the existing connected-order node, with flatness supplied explicitly by `lem-pc-flat-field`. No assumption of reducedness or etaleness was added to the item.

The imported blueprint ancestry is null in the current record and `blueprint_refs.py ancestor` confirms null. The inherited exact place and via chain are retained, with the item prepended in the new leaf's via list. The latest blueprint (`literature/blueprint/latest`, main-20261023-1620) was read at `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3). This input is far below that clause through the inherited level-rigidity/isogeny chain; it does not change the unit route or claim to realize the unit's key theorem.

## Not duplicates

The new Sylow cardinality leaf has no Stacks tag. Whole-DAG searches for `Sylow.card_eq_multiplicity`, Sylow/cardinality and primary-torsion statements, together with blueprint searches for Sylow, maximal p-subgroups and order of a Sylow subgroup, found no existing node asserting this cardinality formula.

lem-sfb-sylow-subgroup-cardinality vs lem-weil-pbc-sylow-subgroup-prime-index: the existing node gives existence and prime-to-p index, not the exact cardinality of a specified maximal p-subgroup.
lem-sfb-sylow-subgroup-cardinality vs lem-sfb-sylow-conjugate-containment: the existing node gives conjugate containment, not subgroup cardinality.
lem-sfb-sylow-subgroup-cardinality vs lem-sfb-finite-group-prime-power-exponent: the existing matrix-subgroup lemma says its order is some p-power, without identifying that exponent from the ambient group's order.
lem-sfb-sylow-subgroup-cardinality vs lem-sc-coprime-torsion-decomposition: the existing node decomposes modules for coprime annihilators, without a cardinality formula for a maximal p-subgroup of a general finite group.

The new node is a generic finite-group theorem, not a clause about group schemes or a relocation of the item's primary-torsion assertion. Packaging its stated maximality as `Sylow.mk` is definition unfolding. Its mathematical result is exactly the Mathlib declaration at line 761. All searches in its record were actually run with msearch.py, and their hits were read. Both natural-language phrasings led to that declaration; Loogle also found it; grep confirmed its current file and line. I read lines 52-55 and 759-767, and the definition of `IsPGroup` in PGroup.lean, so no extra normality, commutativity or index theorem is needed to use the match.

## Review by Q89

I read Milne, *Algebraic Groups* (2017), Proposition 11.3 on printed p.210 and Corollaries 11.30-11.31 on printed p.220, including their adjacent proofs. Proposition 11.3 gives the perfect-field connected–etale splitting, and the existing local–constant product node states its commutative algebraically closed specialization with the precise rank product and finite point group needed here. Corollary 11.30 gives characteristic-exponent-power connected order; the reused positive-characteristic node gives exactly the case we use. Corollary 11.31 supports the separate characteristic-zero etaleness route. For the sole new node, I read Mathlib/GroupTheory/Sylow.lean at the maximal-subgroup definition and the cardinality theorem, rather than attributing the formula to Milne without proof.

For step 1 I opened the local–constant product node and checked that its statement supplies C as a finite connected commutative subgroup, H finite, d and q positive, and N=dq. This avoids separately assuming a reduced scheme or counting closed points with multiplicity one.

For step 2 I opened all four cited nodes. `lem-pc-flat-field` states every scheme over a field is flat, which supplies the otherwise unstated flatness hypothesis of `lem-sc-connected-finite-order`. That theorem applies to C only when the characteristic p is positive. The characteristic-zero parenthetical in `lem-sc-fg-order-prime-etale` applies to G without an added restriction; `lem-sc-finite-etale-points` then gives q=N by taking the permitted algebraically closed extension to be k itself. In positive characteristic d=p^r is prime to ell, so removing that factor from N=dq does not change the exponent of ell in its integer factorization. This last statement is just the definition of the integer valuation already in the item's statement.

For step 3 I opened `def-sc-group-scheme`. It makes the point functor group-valued, and commutativity of G makes H abelian. The step proves closure under addition and inverse by writing the annihilating powers explicitly. Its maximality assertion is direct set containment: every element of any other elementwise ell-power-annihilated subgroup lies in P. No Sylow conjugacy or primary decomposition theorem is hidden here.

For step 4 I reread the new node's statement. Its hypotheses are elementwise prime-power order and maximality, precisely those just proved; finiteness comes from step 1. Passing from additive to multiplicative notation introduces no object change. The formula gives ell raised to the exponent in q, which step 2 identifies as e. This is the only non-elementary group counting result and is a cited Mathlib leaf.

For step 5 I opened the finite-additive-group cardinal-annihilator node. Its statement applies to the finite subgroup P, not only to H. Its order is ell^e by step 4, so the annihilator assertion gives ell^e x=0 directly. Multiplication by ell^(n-e) proves one inclusion of the stabilized kernel; the other inclusion is literally the existential definition of P. This is an elementary step with the needed annihilator theorem cited.

I tested the item on the trivial group (N=1 and e=0), a constant cyclic group of ell-power order, a product of constant factors of coprime order, and the nonreduced examples alpha_p and mu_p in characteristic p. For the latter two, q=1 while N=p, so ell different from p gives e=0 as required; their products with constant ell-groups give N=p ell^a and q=ell^a. This verifies why the primary comparison is restricted to ell different from the characteristic. The stabilization bound handles e=0, and no cyclicity of the full primary subgroup is used (e.g. (Z/ell)^2 has order ell^2 and is already killed by ell). For the new leaf, the trivial group and primes not dividing the ambient order give e=0 and P={1}; an arbitrary nonabelian ambient group is allowed because only the maximal p-subgroup hypotheses enter Mathlib.

I checked delivery-errors B–E against the files: the one new node has a self-contained statement and no proof; every proof use has a statement quotation; no proof uses another node's internal argument; non-elementary structural steps have cited nodes; the elementary subgroup and stabilization arguments are written out. No step exceeds 2000 characters. The connected-order and etaleness nodes from another unit are declared generic tool uses in split_report, because they provide structural finite-group-scheme inputs not replaced by any statement of this unit. All other reused tools are in-unit, Mathlib, or Lean-closed. The preflight checks will verify graph acyclicity and current node availability on the server.

## Unfinished work

None in the authorized split. Existing unsplit structural dependencies remain queue items; the new leaf itself requires no further split.

## Dry-run repair

The first preflight required an explicit notion-node citation in the new leaf despite its inline group definition. I added def-sfb-finite-infinite-set for finiteness, after reading its statement, and updated the step-4 quotation. The mathematical statement and proof are unchanged.

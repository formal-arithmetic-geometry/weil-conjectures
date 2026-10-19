# Worker report

## Files written

- `dag/nodes/sec-poincare-duality/lem-weil-local-frobenius-conjugacy-class.json`: statement; seven-step split; no Mathlib match for the item. No new nodes and no new Mathlib leaves.
- `citations.json`: a verbatim-statement audit of every dependency of every step.
- `searches.jsonl`: searches actually performed by the required wrapper.

## Attachments

No finished attachment. Read `WeilConjectures/WeilSheaf/LocalFrobenius.lean:76-136` in the read-only slopmaster2 checkout. `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAtGeometricFiberPoint` at line 86 has `sorry` at line 93. The complex analogue at line 128 calls that sheaf theorem at line 136. Moreover these declarations use `PadicAlgCl l` coefficients, whereas the item is at a fixed finite extension E/Q_l; identifying these coefficient settings is not an exact attachment. The imported `lean_audit` fields are preserved rather than claiming closure from a sorry-free wrapper.

## WANTED

None. The item proof is agent-written, with the master blueprint proof available and the current main-20261015 statement checked. All substantive input statements already have DAG nodes.

## Corrections and source issues

STATEMENT-DISPUTED: the phrase “two embeddings” must mean k_0-embeddings. The construction invoked in def-weil-local-frobenius-trace explicitly requires k_0-embeddings. This is a typing issue if arbitrary field embeddings are allowed: take k_0=F_{p^2}, Y_0=Spec(k_0), and y its only point. The p-power embedding k_0 -> k fails to commute with the fixed structure map k_0 -> k. Its composite Spec(k) -> Spec(k_0) and the identity map into the second factor do not form a cone for Y_0 times_{k_0} k, so it defines no associated k-geometric point of Y. The statement now explicitly says k_0-embeddings, faithfully recording the construction's existing meaning; no valid residue embedding is excluded. Added direct definition references for the finite-field datum and coefficient extension.

The imported proof's assertion that the two points are related by a power of g_Y omits the source reparametrization. Corrected it to z_i=g_Y^i z_0 Spec(gamma)^{-i}, so every z_i remains a k-morphism; the true return is g_Y^r z_i=z_i Spec(gamma)^r. The automorphism alone gives a comparison to a pullback stalk, not a stalk isomorphism of an arbitrary sheaf. The proof now explicitly applies the Weil isomorphism and the specified point transport. The original “intertwines” sentence has been replaced by a naturality induction and a cyclic-product equation.

Read the chapter and sk-lem-finite unit records. This lemma is an auxiliary local-operator comparison, not that unit's key finiteness statement. No unit realization fields are changed. Its original blueprint ancestry and import metadata remain. The external-unit statements used as generic tools are declared in split_report.tool_uses; no unit proof route is replaced.

## Not duplicates

No new nodes. Searched the whole DAG by Frobenius/embedding/stalk/conjugacy concepts and the blueprint with blueprint_refs.py searches “conjugacy” and “embeddings”; checked its ancestor command. Existing lem-trf-local-frobenius-conjugacy has finite A_{E,n} coefficients and a strict finite-Tor Weil complex on a separated scheme; it cannot be applied to this E-coefficient item. Existing lem-trf-rational-local-frobenius-powers assumes separatedness and an integral representative with finite-Tor reductions; neither is assumed here. Neither statement is recorded as a same_as exact duplicate. Existing finite-field Galois and point-transport tools are reused instead of making new nodes.

## What remains

Nothing left unfinished in this one-level split. The dependencies' future proofs remain their own items. No Lean was written or compiled, no git command was run in the shared repository, and no live project file was changed.

## Review by Q118

I read the item's master blueprint file, including its complete proof, and its corresponding main-20261015 file (same statement, no proof text). I read the statement of every dependency used by each of the seven steps and checked the actual clauses copied into citations.json. The statement keeps arbitrary finite-type Y_0, arbitrary Weil structure over E, every closed point and every integer cohomological degree; the only wording correction is the required base-field linearity of the embeddings, with the explicit typing test above.

Step 1 uses lem-kun-closed-point-field(a) to obtain a finite residue extension. Finite-dimensionality over the finite field makes that field finite (a basis writes its elements as finite tuples). Lem-sfb-finite-field-galois-frobenius says both normality and that the q-power automorphism has order r and enumerates the Galois group; normality makes both embedded images the same, and then the displayed automorphism enumeration really does compare e and e'. The affine formula in def-weil-frobenius-detailed gives the sign of the reparametrization and the orbit equation. I checked the case r=1, where the embeddings coincide, and the sign on a tensor a times b.

Step 2 uses the *specified* transport of def-weil-frobenius-point-transport, the rational point functor in def-weil-local-frobenius-trace, naturality clause (2) of lem-weil-frobenius-point-transport-natural, and invertibility clause (1) of lem-weil-frobenius-cohomology-transport-iso. The last node has a separated auxiliary Y_0 in its statement; I checked that clause (1) quantifies over every N on Spec(k), independently of that Y_0. Taking the auxiliary scheme Spec(k_0) meets its hypothesis, and places no separatedness condition on the Y_0 of this item. Lem-pod-integral-pullback-composition states both naturality and the triple-composition associativity equation, not merely existence of an isomorphism. Def-weil-derived-pullback-tensor-hom explicitly defines the rational pullback by linear extension of the integral functor; applying localization to the integral comparisons preserves their equalities and inverses. Thus this step neither silently changes coefficient categories nor assumes an integral Weil lattice.

Step 3 checks the return normalization, using those same naturality and associativity statements. I checked all sources and targets: Q_{i,n} starts at J_{i+n}(N), ends at J_i(G^nN), and in the induction the additional point transport is iota_{L(h^n)^*B} after the stated comparison. It composes with I_B^{[n]} to exactly I_B^{[n+1]}, which is how def-weil-local-frobenius-trace defines the return. This is a routine induction evaluating the definitions and already-cited natural transformations; it does not import an unstated arbitrary transport-coherence theorem.

Step 4 checks the second induction. Naturality for theta^{[n]} has precisely source G^nM and target M, so tau_i(M) J_{i+1}(theta^{[n]}) equals J_i(G theta^{[n]}) tau_i(G^nM). Expanding theta^{[n]} gives theta G(theta) ... G^{n-1}(theta), proving the alternative recursion used there without citing the finite-coefficient cocycle lemma at rational coefficients. Each A_i is invertible because both its factors are. The calculation concerns the actual specified transport, not just an existential isomorphism class.

Step 5 uses only def-weil-local-frobenius-trace and the preceding two calculated identities to identify the product with the actual r-fold local operator. Step 6 is an elementary multiplication of r maps with the correct order: F_i A_i=A_i F_{i+1}, hence F_0 T=T F_t; the inverse T^{-1} has the direction required in the conclusion. I checked r=1, t=0, and the two-map product A_0 A_1 versus A_1 A_0. A_i are periodic because the points and chosen comparison formulas are periodic; the partial products T are not asserted to be periodic. Step 7 cites def-weil-coefficient-cohomology-modules for the cohomology functor and def-weil-local-frobenius-trace for the precise identification of H^j of the point complex with the stalk notation. It only uses preservation of composition and inverses, so also covers zero stalks and degrees outside the support of K.

I checked B-E of delivery-errors against these files: there are no new unsplit statements, no hidden new object definitions, no uncited tag-based assertions, no finite-coefficient theorem applied at E coefficients, no unsupported separatedness or finite-Tor hypothesis, no relabelling of the item as a new lemma, and no circular use of this conjugacy statement. Every proof dependency was traversed in a read-only DAG check to ensure no path back to this item. All seven steps are below 2000 characters; the two inductions write out the comparisons and equations rather than hiding lemmas behind “standard” or “transports”. Searches were performed with msearch.py, and all actual results were read. In particular isConj_arithFrobAt in Mathlib/RingTheory/Frobenius.lean:274-281 has a finite ring-action group and invariant subring; it gives no Weil-complex stalk statement. Two distinct semantic phrasings both failed to find the item, and the direct stalk/Frobenius source grep was empty. No fabricated or unavailable search result is recorded as a success.

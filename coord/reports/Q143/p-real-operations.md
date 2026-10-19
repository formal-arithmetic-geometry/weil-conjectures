Files written:

- `dag/nodes/sec-purity-real-sheaves/p-real-operations.json`: repaired seven-step proof; statement retained exactly.
- `dag/nodes/sec-purity-real-sheaves/lem-real-lisse-path-fibres.json`: statement-only child, unsplit; no Mathlib match. Natural, coefficient-compatible path transport on lisse fibres, with the ordinary/framework fibre comparison specified.
- `dag/nodes/sec-purity-real-sheaves/lem-real-weil-twisted-paths.json`: statement-only child, unsplit; no Mathlib match. Coefficient-free twisted-loop description of the Weil group, including the residue-field return path.
- `dag/units/sk-p-real-operations.json`: only `realized` and `realized_by` filled for the unit's key proposition.
- `citations.json`: whole statements quoted verbatim for every use by every item step.

Attachments: none. The source declaration `AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj`, `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Weights.lean:135`, has a closed proof of conjugacy invariance for an already-given representation and its representation-defined local polynomial. Its hypotheses contain no lisse Weil sheaf, framework point fibre, or descent operator. It does not attach this item. Searches of the source for the item tag, path/fibre comparisons, local Frobenius and Weil-sheaf terminology found no declaration stating the complete item or either child.

WANTED: none. All sources used are available locally. No SGA source is used.

The returned head's Step 2 repeated the blueprint's omitted comparison as though it followed from definitions. The return is correct: neither the local-operator definition nor the definition of the fundamental representation compares these maps. The retained report's claim that its citations supplied the whole comparison was incorrect. The initial required dry run of the retained sandbox also found that `citations.json`, mentioned in that report, was absent. I repaired both the mathematical gap and that missing artifact. The existing item agrees with the returned version except for its unsplit base metadata; no already-reviewed live replacement supersedes this work. I kept its statement, all original statement dependencies, blueprint_update and import metadata. I read both the master and main-20261015 proposition/proof; moving the conjugacy parenthetical into the proof changes no assertion.

I split the comparison into two different mathematical inputs. The first child is a statement about geometric path functors on lisse coefficient models; it contains no Weil structure or local Frobenius. The second child describes arithmetic group elements using geometric paths and constant-field descent; it contains no coefficient representation or operator. Their statements cannot independently conclude the item. The item itself evaluates the descent action, verifies the group law, identifies its geometric restriction and degree-one generator with the prescribed representation, and writes the naturality square conjugating the actual local composite. The finite coefficient model is chosen before this calculation, including a model of the inverse descent isomorphism and its inverse equations. It never assumes an integral lattice preserved by Weil Frobenius.

The common-stage and normalized-realization lemmas are used through their public statements. The only off-unit nondefinition tool needed by the item's proof is `lem-tw-lisse-rational-realization`: it supplies the ordinary model of the specified framework pullback, fibre and point transports. The declaration is in `split_report.tool_uses`, for independent approval at review; the worker has not set maintainer `tool_uses`.

Mathlib searches are the actual `msearch.py` calls in `searches.jsonl`. No earlier search log survived in this sandbox, so I did not manufacture records for the previous report's claimed searches. The repaired comparison changes the search question, and I ran and read fresh searches for the item and both proposed children. Each has LeanFinder, Loogle, grep and LeanSearch records. Both children have a second semantic phrasing and a focused source grep. The first child's generic Galois-category hits (`FiberFunctor.reflectsIsos`, `autIsoFibers`, fundamental-group action infrastructure) do not provide the adic, scheme-point, pullback and framework-realization assertion in one specialization. The second child's hits concern topological fundamental groups, abstract Galois-category groups or Frobenius of finite field extensions, without the twisted path/arithmetic group comparison. The item's hits concern ordinary characteristic polynomials and Witt-vector Frobenius, without the local operator comparison. No Mathlib leaves were created. The later splitting of the children can reuse those generic facts individually.

## Review by Q143

I read the actual chapter record `sec-purity-real-sheaves`, unit `sk-p-real-operations`, the current and master item proof, Deligne's *Weil II* (1.1.1), (1.1.6)-(1.1.13), and Stacks `pione.tex`, Tags 0BND (`theorem-fundamental-group`), 0BN5 (`lemma-functoriality-galois`), 0BTV (`lemma-limit`) and 0BTX (`lemma-ses-field`). I also read Bhatt--Scholze Proposition 6.8.14 and Remark 6.8.15 and the proofs of Lemmas 7.4.7 and 7.4.10. The first child's smoothness hypothesis ensures the classical profinite etale paths govern its pro-etale lisse modules; the nonnormal counterexample in Example 7.4.9 is excluded. Its adic extension and normalization package is explicitly identified as an agent formulation, rather than claimed to be one verbatim theorem of Stacks. The second child formulates the finite-cover groupoid implicit in constant-field descent and Deligne's definition of the Weil group. Its group multiplication and degree conventions are written explicitly. Both children are statement-only, self-contained, in the item's chapter/unit, and have the nearest blueprint ancestor and precise `from.place` supplied. I searched the whole imported blueprint using `blueprint_refs.py` for path, fibre functor, descent datum, transport, Frobenius and lisse, and searched the full DAG for the same notions and the cited tags. The shared-tag candidates are distinguished below.

Step 1 uses the finite coefficient model of `def-pod-lisse-l-adic-sheaves`, the representative/equality rule of `def-weil-algebraically-closed-coefficients`, and the fibre/pullback/point-transport compatibility actually stated by `lem-tw-lisse-rational-realization`. It cites `d-real-setup` for the smooth connected finite-type curve hypotheses of the new path lemma. I checked that theta and its inverse both descend, then their two inverse equalities, after enlarging E. This avoids assuming that a Weil isomorphism exists at the field of definition of the underlying object without enlargement.

Step 2 uses exactly the pair multiplication and geometric kernel of the new twisted-path lemma and the naturality/pullback/composition formulas of the new path lemma. I checked the order: for w=(n,p) and v=(m,q), the path of wv is g^m(p) composed with q, and the resulting operator is theta^[n+m] g^m(p) q. The displayed naturality equation is the one required for multiplying theta^[n] p and theta^[m] q. Positive iterates concatenate, while negative iterates cancel inverse factors. This is the elementary verification from the two cited statements, not an additional uncited theorem about Weil sheaves.

Step 3 opens `def-wf-fundamental-representation` and uses its actual formula rho(delta s^n)=rho_geom(delta) T_s^n. The path lemma identifies geometric loops with their fibre-functor actions. The stalk transport for s is specified as theta_b p_s, so both geometric generators and s act by the prescribed operators; Step 2 then gives the action on every element. An arbitrary abstract equivalence would not suffice, and is not used to infer this equality.

Step 4 uses the new path lemma for the E-linear isomorphism u from the closed-point fibre to V_E, its naturality for theta^[e], and the new twisted-path lemma for the actual path of the decomposition Frobenius. I checked the domains in u theta_a^[e] = theta_b^[e] (g^e tau): both are maps from the fibre at g^e a to V_E. Substitution gives rho(f_x)=u(theta_a^[e] c)u^-1 with the displayed order. This explicitly gives equivariance for the integer-degree part of the decomposition group, which is the part on which a general Weil sheaf acts. The underlying paths give the full profinite decomposition-group conjugation on finite covers; the proof never applies rho to arbitrary elements outside W.

Step 5 uses the precise composite in `def-weil-local-frobenius-trace`, not a vague reference to its name. I checked its source Fib_s(La^*M), the iterated point transport, the return g^e a = a Spec(gamma^e), and its last theta^[e] arrow. The realization lemma explicitly identifies point transport and its iterates with restriction and coprojection in the ordinary model. On finite covers this is the map z -> z Spec(gamma^e) in the new groupoid lemma; natural transport through the finite module models and the adic coefficient extension is exactly the first child's statement. Consequently every arrow, including its scalar normalization, agrees, and F_x is theta_a^[e] c. This is the E5 repair: 'transport' now denotes the specified map and its formula.

Step 6 keeps the accepted elementary conjugacy calculation, spelling out deg h=n+e_x t and w=h f_x^-t. Its sources are the twisted-path identification of the decomposition image, `def-wf-weil-group` for the integer-degree subgroup, and `lem-wf-weil-group-constant-extension` for normalized degree. The profinite power is taken in pi_1(x), before evaluating a representation. Thus no continuity of a general Weil representation on the whole arithmetic group has slipped in.

Step 7 uses the exact tensor equivalence only for the operations, the operation definition for the listed actions, and `def-wf-iota-real` for the determinant formula. Equality and conjugacy invariance of determinants are the explicit elementary change-of-basis calculation over E[T] and then Qlbar[T]. It does not use a new child to repeat the desired equality.

For B1--B9 I checked that children have no proofs or hidden proof sketches in their statements, every referenced notion has a statement dependency, TeX is singly escaped in the decoded strings, source tags and labels were read, and each search record matches an actual logged query. For C1/C4 I read every cited node's entire statement and regenerated `citations.json` using those exact statements. The new nodes are smaller inputs, not clauses of the local-polynomial proposition; the local comparison remains derived in Steps 2--5. For E1--E6 I checked geometric connectedness, smoothness, separated finite type, ell different from p, finite E, the source reparametrization of geometric points, the degree convention and the source/target of every displayed composite. I tested rank zero, rank one with arbitrary nonunit Weil eigenvalue, e_x=1, a constant rank-one sheaf with descent scalar lambda (the answer is lambda^e_x), n=0, n=-1 and m=-n in the twisted multiplication. Constant finite-field covers test the geometric versus arithmetic Frobenius sign; the return map acts by gamma^e, not gamma^-e. No step exceeds 2000 characters.

The return's C1 and C4 gaps are addressed by the two sourced child statements plus the existing normalized realization. E5 is addressed by the actual path and composite formulas. D3 is addressed by carrying the descent-action construction and generator comparison in the item's own steps. No statement dispute or route replacement is necessary. The old two-step proof and report are preserved below as the historical returned attempt; the preceding review supersedes their unsupported conclusions.

## Not duplicates

lem-real-lisse-path-fibres vs lem-wf-finite-etale-weil-transport: the existing statement supplies one Frobenius-twisted bijection on finite-cover fibres and a conjugation rule; the new statement concerns arbitrary paths acting on module and adic/rational lisse stalks, with pullback and coefficient-model compatibilities.

lem-real-lisse-path-fibres vs lem-weil-pbc-connected-torsor-subgroup-quotient: the existing statement constructs subgroup covers of a given finite torsor and their degrees; it asserts no transport on lisse stalks.

lem-real-lisse-path-fibres vs lem-galois-pi1-functoriality: the existing statement concerns pullback of finite covers along a morphism of schemes; it does not extend arbitrary paths between fibre functors to lisse adic sheaves or identify framework point fibres.

lem-real-weil-twisted-paths vs lem-wf-finite-etale-weil-transport: the existing statement provides a twisted fibre bijection for an element of W and a conjugation identity. It does not identify all twisted paths with W as a group, specify their multiplication, or identify the residue-field return path with a decomposition Frobenius. Its existential bijection is insufficient for those normalizations.

lem-real-weil-twisted-paths vs lem-weil-pbc-connected-torsor-subgroup-quotient: the existing statement constructs subgroup torsors and their indices, without a constant-field Weil group or twisted loops.

lem-real-weil-twisted-paths vs lem-galois-pi1-functoriality: the existing statement gives a homomorphism from scheme pullback and compatibility on finite-cover fibres; the new statement identifies the arithmetic degree extension with twisted geometric paths and normalizes its local Frobenius path.

lem-real-weil-twisted-paths vs lem-sbc-galois-cover-base-change: the existing statement is stability of finite G-torsors under base change, with no Weil or path-group identification.

lem-real-weil-twisted-paths vs lem-sbc-galois-cover-stage-descent: the existing statement descends a finite G-torsor in an inverse system; it does not identify the arithmetic group or its Frobenius elements.

lem-real-weil-twisted-paths vs lem-sbc-pointed-section-stage-descent: the existing statement descends a morphism into a locally finitely presented scheme, without twisted loops or constant-field arithmetic.

lem-real-weil-twisted-paths vs lem-sbc-pointed-galois-cover-limit-descent: the existing statement descends a finite torsor together with a point over an inverse system; it does not state the group law or arithmetic normalization here.

lem-real-weil-twisted-paths vs lem-wf-finite-etale-field-limit-descent: the existing statement descends covers, maps and equalities to finite intermediate fields; it is a possible input to the future proof of the new child, not the identification of twisted loops and W.

Both children vs p-real-operations: neither child mentions the local characteristic factor or asserts the equality of the descent-defined local operator with rho(f_x). Those conclusions are obtained by the item's explicit action calculation and naturality square.

Other nearby statements read: `lem-weil-local-frobenius-conjugacy-class` and `lem-trf-local-frobenius-conjugacy` compare local operators at different lifts; `lem-rp-local-frobenius-models-agree` compares two local operator models; `lem-fd-local-weil-model-trace-independence` compares isomorphic coefficient models. None identifies the generic fundamental representation's action with the local operator. `lem-a1-normal-proetale-monodromy` provides a single-base-point representation equivalence with lattice normalization; the new path lemma states its natural extension between fibre functors and under pullback.

What I could not finish: no stage-1 obligation remains in the proposed split. The two children are deliberately unsplit, as required by the one-level rule. Independent maintainer review and landing remain outside this delivery.

## Historical returned report (superseded)

Files written:

- `dag/nodes/sec-purity-real-sheaves/p-real-operations.json`: statement item, split into two proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for each cited node in each step.

Attachments: none. I found no sorry-free project declaration tagged `(blueprint: p-real-operations)` or stating the item exactly.

WANTED: none.

The imported proof followed the current main-20261015 blueprint update. I retained the item statement and all statement dependencies. The first paragraph is a group calculation, so I cited the existing Weil-group definition and constant-extension degree lemma rather than creating a duplicate child. The second paragraph is the tensor-equivalence transport and local determinant identification. No statement error or route replacement was found.

## Review by Q143

I read the chapter `sec-purity-real-sheaves`, unit `sk-d-real-operations`, the item, and the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-operations/p-real-operations.proof.md`. I also opened the full statements of `def-wf-weil-group`, `lem-wf-weil-group-constant-extension`, `prop-wf-weil-sheaf-representation-equivalence`, `def-real-weil-representation-operations`, `def-weil-local-frobenius-trace`, and `def-wf-iota-real`.

Step 1 uses exactly the Weil-group degree-subgroup description and the constant-extension statement. The displayed decomposition $g=wF_x^t$ and the commutation of the procyclic power with $F_x$ give the conjugacy calculation; I checked the degree-one and degree-$e_x$ cases and the edge case $e_x=1$. Step 2 uses the exact tensor equivalence for transporting direct sum, tensor, dual, exterior and determinant operations; the local-Frobenius definition supplies the iterated stalk operator; and `def-wf-iota-real` states the local factor as the determinant. The remaining invariance of a characteristic polynomial under conjugation is the standard one-line linear-algebra calculation. Every cited statement says the fact used, and each quotation in `citations.json` is verbatim.

I searched the whole DAG and blueprint for a duplicate conjugacy or local-polynomial node. `lem-weil-local-frobenius-conjugacy-class` concerns conjugacy of stalk operators for two residue-field embeddings, not the Weil-group decomposition used in Step 1, so no new node was created. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item via `msearch.py`; the hits were unrelated finite-field/Witt-vector declarations or generic characteristic-polynomial facts, and no Mathlib declaration states this Weil-sheaf assertion. The item is therefore a project statement, not a Mathlib leaf. No SGA source, Lean file, compiler, Lake, or build tool was used.

Small checks covered the zero-dimensional representation (both determinants are $1$), a rank-one representation, and degree-one closed points. The proof dependencies equal the union of the step uses, there is no cycle, and no step exceeds 2000 characters.

What I could not finish: nothing for this stage-1 split; the maintainer must perform the independent review and landing.

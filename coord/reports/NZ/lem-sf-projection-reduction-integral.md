# Worker report: lem-sf-projection-reduction-integral

## Files written

- `dag/nodes/sec-six-functors/lem-sf-projection-reduction-integral.json`: statement; eight proof steps; no Mathlib match. The imported statement and statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for each of the 23 step/dependency pairs.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by msearch.py; the sandbox also contains my construction script.

No new nodes and no Mathlib leaves. No unit file, repository file, launcher file or Lean file was changed. No compiler, Lake, library build, local preflight, local review_split or local check_dag was run.

## Attachments

None. I searched `lean/WeilConjectures/` by the item id and projection/reduction/tensor-action concepts. `AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc` in `LowerShriekProjectionAssoc.lean` proves the ordinary etale constant-coefficient identity, not the specified completed integral one. Its reductionModIdeal specialization likewise does not attach this item. The item's exact allocated declaration, `WeilConjectures.sixFunctorProjection_reduction_integral`, at `lean/Sheaf/Paper/ProjectionFormulaCoherence.lean:1140`, contains `sorry` at line 1145. I read its whole predicate and docstring, not just its name. It quantifies over all integral K,L,N, exactly as this item does.

## WANTED

None.

## Problems and corrections

The live item had no proof. Its source note retains useful construction material but is not proof certification. In particular a finite-coefficient action equation, or equality after every finite evaluation, would not suffice to prove equality of completed derived morphisms. This split proves the equation in the derived category of coherent systems and applies the total-limit functor to that equation. It never asserts faithfulness of derived evaluation or uniqueness of a map from its reductions.

The existing `lem-sf-projection-tensor-coordinate-action` is for derived sheaves in one coefficient category. I read its statement and did not silently identify its coefficient category with a varying-ring semilinear system category. Instead I reused the genuinely ringed single-mate associativity theorem and the already existing generic open/composite action laws, on the simultaneous ringed-diagram-site models. No duplicate or restatement node is introduced.

Integral D^b_c inputs need no new hypothesis: `lem-coef-integral-residue-tor` supplies their uniform finite-level Tor amplitude. This is used to establish a known property of the inputs, not to restrict the quantifiers. The source's phrase “constant quotient” is interpreted inside the original completed coefficient category as its quotient coefficient object: the zero ideal gives the completed tensor unit, the unit ideal gives zero, and a nonzero proper ideal gives the usual finite constant quotient. The general action identity is proved before specializing N. There is no reduction of a rational object here.

No statement dispute or change of proof route was needed. The unit and chapter records were read, and their route is preserved. All off-unit uses are declared in split_report.tool_uses as generic categorical/realization/domain tools.

## Earlier attempts and search provenance

The exact prescribed Python archive listing returned no matching directories, including other groups. The active sandbox contained only dispatcher markers and no item node or prior report/search log. I copied the live unsplit item before writing its proof. There was no item repair note in the named repository locations.

The item's five pre-existing Mathlib searches belong to its NB creation on 2026-10-27. They remain unchanged and are not represented as my searches. My seven additional searches are exactly those logged by msearch.py, with their returned names and service notes recorded in the item. All services answered. The initial Loogle query for the project-specific name was rejected as unknown; that record is inconclusive and was followed by a valid adjunction/tensor query. The initial Mathlib grep used a project-style `Sheaf` subdirectory and returned nothing; it is inconclusive and was followed by a genuine `CategoryTheory` search. The substantive semantic searches returned general algebraic completion, monoidal-adjunction and right-action facts, not the completed integral compactification identity. I read the candidate monoidal-adjunction declarations in Mathlib/CategoryTheory/Monoidal/Functor.lean; their counit/lax-monoidal equations are not a one-line statement of this item.

I searched the DAG by projection/tensor/counit/open/associativity words, by the existing named candidate nodes, and by upstream declaration names. Whole-blueprint searches for “tensor-action” and “projection associativity” found no equivalent blueprint node; ancestor identifies prop-sf-pf-coherence. The pre-existing generic tools are reused. There is no same-tag new/existing pair because there are no new nodes.

## Not duplicates

No new nodes. In particular, neither the finite-coefficient action lemma nor its general coefficient-coordinate version has been recreated, and no new node restates an integral clause.

## Review by NZ

I read the current `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, the unit and chapter records, the live item's retained source argument and exact Lean predicate/docstring. The blueprint's final sentence gives the coefficient-compatibility obligation; the imported source note makes explicit the proper counit/open unit action calculation to be carried through systems. The proof_origin is correctly marked agent, since the blueprint and its expansion are agent-written. I also read the actual generic ringed projection-associativity statement and proof in `lean/Sheaf/Paper/RingedProjectionTensorAssociativity.lean`. No SGA source was used. There are no new-node sources to certify.

I opened every cited node's statement, checked its quantifiers and read what it actually gives:

1. The domain step uses integral residue-Tor equality, integral pullback/tensor preservation, and the completed compactification realization. The latter explicitly says that j_!K and Rp_*j_!K are complete constructible and compares the strict tower with the specified compact-support object. Iteration covers K tensor UL, K tensor U(L tensor N), and both triple products, not only the original K. A compactification here has finite-type ambient scheme (p proper over finite-type Y); its open is quasi-compact in this Noetherian setting. The origin equivalence holds for arbitrary schemes and finite coefficients. Choosing one inverse equivalence on the reduction diagram preserves its transitions and composition relations. Uniform cohomology comes from the definition of integral D^b_c, and uniform Tor bounds then apply to each intermediate complete constructible object. There are finitely many such words. No separatedness of X/k or Y/k was inserted.
2. The system-realization node really supplies simultaneous ringed-diagram-site models, actual adjunctions, canonical tensor/pullback compositors and open maps, not just matching evaluated objects. The generic ringed monoidal comparison theorem applies on these small ringed diagram sites with their varying coefficient ring. The coherence-data definition fixes the total-complex associators. The projection definition fixes the proper/open composite. This is why these citations, rather than the narrower generic constant-coefficient action lemma, were used.
3. The cited single-projection associativity theorem has arbitrary E,Q,T and no projection invertibility or boundedness hypothesis. I checked the equation's orientation: its source inverse associator is cancelled by precomposition with alpha_Y, giving exactly the right-tensor action form. Its constraints are the representative-normalized constraints of the cited coherence-data node; at every triple of objects choose their K-flat presentations and cancel the presentation isomorphisms to identify them with the canonical reassociation. Nothing is taken from a proof of a node instead of its statement.
4. The open-normalization statement explicitly includes arbitrary strict inverse coefficient systems, arbitrary structural ring maps, full faithfulness, invertible delta and its inverse's precise unit-adjunct formula. It therefore identifies kappa in the generic unit-adjunct action theorem. I inverted the displayed equation by hand: the inverse of J((1 tensor mu^{-1}) alpha) is J(alpha^{-1}(1 tensor mu)). This yields delta twice in the required order. No unsupported extension from finite to completed coefficients is used.
5. The composite-relative-action statement says exactly that the two action laws paste for R(delta) pi. Its explicit naturality expansion resolves the middle interchange. The separate ringed monoidal-composition statement identifies QP with P_f compatibly with tensor; hence the actual compactification pullback-composition factor is retained, rather than dropped by notation.
6. The whole-expression realization statement explicitly compares morphisms and their whiskerings, units and counits. The tower-substitution statement explicitly compares associators and actual reduction-limit counits before taking limits. The completed-pullback comparison definition specifies the same system comparison with both Roos coordinates fixed. Writing c_W L(m)=m_int c_V for each constituent shows precisely how every internal comparison cancels. This verifies the maps, not merely their finite reductions.
7. I read the operation-datum and projection definitions. The datum's maps are the specified proper/open maps and its associator is conjugation by tensor normalization; there is no independent arbitrary projection whose compatibility is assumed. Replacing a map by h_target m h_source^{-1} and cancelling adjacent h factors is elementary. This step invokes none of the six-functor datum's projection-isomorphism axiom. The normalized mu is already fixed in step 6.
8. Separating F's image of a composite uses only preservation of composition. Specializing a universally quantified N gives the claimed quotient case. The inverse target associator appears before the two projection routes are compared, and the final images under F occur separately, as required by the exact predicate.

I checked sections B–E of delivery-errors against the actual files: no new-node data or sources are missing, no duplicate or clause-restatement node was introduced, every non-elementary tool is a cited existing statement, and the proof-dependency list is exactly the union of uses. Citations preserve the statements verbatim, including the formal interface hypotheses when those are used together. No new statement was added requiring a separate small-case test. I tested the item calculation at f=id, j=id, the empty open/empty scheme, K=0, L=0, N=0, N=the tensor unit, and N=R/(varpi^r) in degree zero. The action equation has the correct source and target in all cases. The finite quotient is allowed to have non-flat torsion; no inverse projection was used except the always invertible open tensor comparison. All eight proof steps are shorter than 2000 characters, so there is no hidden long-step lemma. A read-only dependency traversal found no path from any proposed cited tool back to the item.

The preliminary server `review_split` passed with zero new nodes and the declared tool uses. The final delivery dry run follows this report.

## Unfinished work

None at stage 1. This delivery does not claim a Lean proof or transitive sorry-freeness of its dependencies.

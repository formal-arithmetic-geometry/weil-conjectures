# Stage-1 delivery: thm-pod-derived-poincare-duality

## Files written

- dag/nodes/sec-poincare-duality/thm-pod-derived-poincare-duality.json — statement, split into seven proof steps; no exact Mathlib match.
- citations.json — statement quotations for every step citation.
- searches.jsonl — actual msearch.py search records, retained without rewriting.
- report.md — this report.

No new nodes and no Mathlib leaves are introduced. The item proof and its statement dependencies now use existing nodes only. All seven steps are below 2000 characters.

## Attachments

None for the full item. I searched the slopmaster2 project under WeilConjectures for the exact item tag and Poincare/Poincaré terminology and read EtaleCohomology/PoincareDuality/Pairing.lean:128–135 and SixFunctors/Etale/Derived/PoincarePairing.lean:426–436. AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing and AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing prove the finite-coefficient abstract-orientation clause. They do not state all four coefficient stages, the point-perfectness conditions, all coefficient comparisons, and the precise inverse/naturality package of this item. Accordingly they do not satisfy the brief's full-item attachment criterion. No Lean was written or compiled.

## WANTED

None. This is explicitly an agent proof following the available main-20261015 blueprint proof and the existing DAG statements. It does not pretend to be a proof read from an unavailable human source. No SGA source is used.

## Corrections and source issues

The original two paragraphs collapsed six logically distinct stages, left stmt_deps empty, and attributed truncation compatibility to statements that only provide naturality, shifts, and coefficient comparisons. I separated the stages and gave explicit comparison equations. The all-stage point-perfectness theorem already asserts perfectness of C and its dual, so the proof no longer tries to obtain an all-stage fact from the finite-level perfect-point definition. The new proof does not compare compact-support with ordinary cohomology and does not assume properness.

### STATEMENT-DISPUTED: unrestricted truncations

Read literally without a domain qualification, the source's 'compatible with ... truncations' cannot assert a duality theorem for every canonical truncation of every site-perfect K. At X_0=Spec(k_0), take E=Q_l, n=2 and A=Z/l^2. Let K be A --l--> A in degrees -1,0. This is a bounded finite-free, hence site-perfect constructible finite-Tor complex. Its canonical truncation tau^{>=0}K is A/l in degree zero. The infinite resolution of A/l with every differential multiplication by l shows Tor_i^A(A/l,A/l)=A/l for all i>=0, so this truncation is not perfect and is outside the stated finite-Tor domain. The same problem occurs with the other nontrivial truncation. This is an explicit counterexample to domain closure, not a reason to discard derived duality.

The statement now specifies that truncation compatibility concerns canonical truncation morphisms and connecting maps when their terms are in the theorem's constructible finite-Tor, site-perfect domain. It asserts no t-exactness or commutation of duality/cohomology with truncation functors. Step 7 proves the resulting squares directly by naturality on all three triangle arrows, including the connecting arrow to a shifted object. All other substantive hypotheses, all four coefficient stages, the inverse map, and the trace-cup pairing are retained. Numerical definition references were replaced by their node ids.

### Unit binding for maintenance

The repository unit sk-thm-derived-duality, and the current blueprint _section.md at that location, now state degreewise duality over a field. This item remains a derived-duality supporting theorem there, not the unit's key statement. Its global-duality, comparison, and point-perfectness neighbours are currently assigned sk-thm-sf-package. I retain the maintainer-owned chapter/unit and do not fill realized fields with a false claim that this derived theorem alone proves the degreewise corollary. The item follows its own current blueprint proof exactly in its two constituent maps and map-identification route. Its cross-unit ingredients are declared in split_report.tool_uses for review. No unit file is modified.

## What remains unfinished

Nothing in this one-level split is deferred to a new node. Existing dependency nodes retain their current states and will be handled by their owners. In particular this delivery is not a claim to have formalized the derived theorem in Lean or discharged the existing DAG leaves.

## Not duplicates

No new nodes. Before deciding this, I searched the whole DAG and tools/blueprint_refs.py for derived Poincare duality, inspected the existing global duality, dual-perfect, pairing identification, point-perfectness and coefficient comparison nodes, and used those. thm-sf-identification and thm-pod-identification-of-the-comparison state the identification constituent, not the entire point-perfectness plus all-stage compatibility package of this item, so same_as is empty. The nearest blueprint ancestor is the item itself; from remains null because this is an imported blueprint node.

## Review by Q93

I read coord/delivery-errors.md B–E in full, the stage-1 contract, GOAL.md, coord/dag-sync.md, the chapter record, and both the unit record and its current main-20261015 _section.md. For the item's source I read the current .md statement and .proof.md, following blueprint_update rather than assuming the old import proof was accepted. There are no new nodes requiring separate sources or searches. The proof origin remains agent-written. The shared tree and both Lean source trees were only read.

For Step 1, I opened def-pod-conventions and thm-pod-global-verdier-duality. The former supplies smooth separated finite type, descent from the finite field, dimension and orientation; the latter actually states F_K is isomorphic to RΓ(X,D_XK), natural and shift-compatible, and includes the site-perfect coefficient-comparison clause. No properness is inferred. This is the first constituent, not a citation to a merely definitional node for a theorem.

For Step 2, I read thm-sf-dual-perfect: it really states D_XK isomorphic to K^vee(d)[2d] for site-perfect K at all four stages, with evaluation, shifts and coefficient comparisons. I also read def-weil-ordinary-compact-cohomology to keep the coefficient complexes and the four coefficient units consistent. Applying the functor and its shift comparison gives h; the inverse of h g is explicitly g^{-1}h^{-1}.

For Step 3, I read thm-pod-point-perfectness in full. It explicitly includes both C and C^vee as perfect point objects at every stage, rather than merely claiming bounded constructibility; its finite stage has finite Tor amplitude. The only remaining operation is transport of a finite-projective model through the already constructed isomorphism to G. I read def-pod-perfect-derived-pairing and checked that it requires C and G perfect and the adjoint invertible, which the subsequent step supplies.

For Step 4, thm-pod-identification-of-the-comparison actually says that the adjoint of the specified cup/evaluation/trace pairing has inverse global duality followed by the smooth-purity identification. Its hypotheses match the descended smooth X, four stages and site-perfect K here. I read def-pod-derived-poincare-pairing, including the normalization of the trace as the exceptional counit through the orientation; consequently there is no silent change from an actual pairing to some abstract isomorphism with the right type. The two inverse identities are written in the correct directions.

For Step 5, the naturality used is explicitly present in global-verdier-duality and dual-perfect. I checked the variances: both F and G are contravariant, while C is covariant. The equality G(u)v_L=v_KF(u) gives b_KG(u)=F(u)b_L by multiplying inverses. I wrote the evaluation/precomposition identity to derive beta_K(1 tensor G(u))=beta_L(C(u) tensor 1). lem-pod-closed-uncurry-laws states the required expression for uncurrying as evaluation following 1 tensor b; its use here is confined to that formula.

For Step 6, the same two constituent statements supply the coefficient squares on site-perfect objects. I read lem-fix-operation-reduction, whose statement explicitly covers finite/integral reduction, rationalization, common-stage scalar extension, and preservation of evaluation. It does not assert ordinary finite-reduction comparison invertible in arbitrary domains; the required specialized comparisons come from the two duality theorems. Since C is point-perfect, its coefficient-dual comparison is in that lemma's permitted domain. Inverting r T(v)=v' l yields b' r=l T(b), and evaluation preservation then gives the pairing square. Shift compatibility is read through the canonical contravariant shift comparisons, including the usual shift signs. This avoids claiming a bare natural isomorphism automatically respects scalar extension.

For Step 7, I read def-weil-t-structure and the actual supporting statements: def-sbc-standard-tstructure-derived-category for ambient finite-level derived truncation, prop-weil-pbc-integral-tstructure for integral constructible truncation, and prop-constructible-truncations for both field stages. The integral theorem requires noetherian finite dimension with l invertible, all satisfied by this finite-type scheme over k of characteristic different from l. These statements supply the truncation triangles, but none is cited for the false assertion that truncation preserves site-perfectness. Naturality is applied to i, p, and the connecting map separately; shift compatibility treats its target A[1]. The transpose is the inverse adjunction operation by lem-pod-closed-uncurry-laws, with the defining pairing read from def-pod-derived-poincare-pairing.

I tested K=0, the dimension-zero point with a finite-free coefficient complex, n=1 (a field finite stage), n=2 with the nonperfect truncation above, the integral torsion/Ext case (no degreewise perfectness is asserted), and nonproper A^1. In the nonproper case C remains compact-support cohomology and G remains ordinary cohomology throughout. For Qbar_l all operations and coefficient comparisons are at a common finite extension, as stipulated by the cited theorems. These checks motivated the truncation correction and avoided a false finite-level-to-integral transfer.

The Mathlib searches were made only through msearch.py: two distinct semantic phrasings, LeanSearch, Loogle and two grep patterns, all logged. I read the returned types and checked the closest candidates in Mathlib/LinearAlgebra/PerfectPairing/Basic.lean:36–46, Algebra/Homology/DerivedCategory/TStructure.lean:178–195, and CategoryTheory/Monoidal/Closed/Functor.lean:128–135. Ordinary module perfect pairings, t-structure concentration lemmas, closed-functor comparisons and group cohomology do not specialize to this sheaf duality theorem. No candidate is recorded as an exact match. The final split uses no long step over 2000 characters, no new lemma restating a clause, and no hidden purity proof. Every proof citation has its statement copied verbatim in citations.json.

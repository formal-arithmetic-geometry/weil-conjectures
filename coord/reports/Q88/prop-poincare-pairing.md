# prop-poincare-pairing — Q88 stage-1 delivery

## Files written

- `dag/nodes/sec-poincare-duality/prop-poincare-pairing.json`: statement, split; Mathlib searches find no theorem matching the item. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement extracts for every node used by every proof step.

The sandbox also retains `searches.jsonl` and `prepare.py` as the search record and local preparation script. The statement is unchanged. No Lean was written or compiled, and no shared repository or source file was modified.

## Attachments

None. I searched the source tree by the item id and by Poincare/pairing terminology, then read `WeilConjectures/WeilSheaf/PoincareDuality.lean`, including the variables and implementation notes. `AlgebraicGeometry.WeilSheaf.exists_traceCup_poincarePairing` at line 241 has a proof without a literal `sorry`, but it does not state this item: its coefficients are `PadicAlgCl l`, and it asserts the existence of a `FrobeniusModule.TraceCup`, rather than the conclusion for the specified geometric trace and cup product over `Q_l`. Its proof uses `exists_traceCup_poincareDuality`, which uses the unfinished `exists_traceCup_isPerfect` (line 134, with `sorry` at line 139 in this checkout). Thus no attachment is claimed. The source explicitly acknowledges both the coefficient mismatch and existential form. I did not change the maintainer-owned `lean_audit` fields, which currently say `none`.

## WANTED

None. The item's proof and its two cited statements are available in the current blueprint. Milne's obtained lecture notes are available as supporting mathematical context.

## What was wrong or incomplete

The imported proof did not give sources for its steps, left `blueprint.same_as` unsearched, and omitted the trace–cup definition from its statement dependencies even though it introduces that particular pairing. It also named only the geometric Frobenius maps, without the global cohomological operator definition in `stmt_deps`. I added these two existing definition nodes.

The imported step 2 named an isomorphism by perfectness before checking equivariance, and step 3 asserted the contragredient description without a calculation. I now explicitly evaluate the pairing-induced map at an arbitrary `x` and apply the given similitude to `(F_i^{-1}x,y)`. The parity calculation in step 4 now writes the even difference of the exponents. The original mathematical statement needs no correction.

I retained the existing duality-interface route. I have not treated its imported proof's Q_l/Qbar_l transport as a proved identification: the interface's own **statement** is explicitly the Q_l theorem used here. Its proof and the choice of coefficient transport belong to its own later split. The present item neither changes coefficients nor uses an unstated scalar-extension theorem.

## Blueprint and duplicate search

Read `dag/chapters/sec-poincare-duality.json`, `dag/units/sk-thm-poincare-duality.json`, and both `prop-poincare-pairing.md` and `prop-poincare-pairing.proof.md` in `literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-thm-poincare-duality/`. The statement and four-step route agree with the imported master item. Steps 1–4 in this delivery realize those four steps in order. This proposition is not the unit's key theorem, so no unit realization fields were edited.

Ran the whole-blueprint searches `Poincare`, `graded-commutative`, `Frobenius similitude`, and `trace–cup`, and the ancestor lookup. I also searched the whole DAG for the item and searched the relevant chapter nodes for perfect pairings and duals. `thm-weil-poincare-duality` and `sk-thm-poincare-duality` contain a broader package (including finiteness, eigenvalues and base change); neither is an equal statement in another form. `thm-pod-qbar-coefficient-pairing` is a different coefficient-stage theorem. The existing `def-weil-poincare-trace-cup` gives exactly the cup-product formula and commutativity used here. Consequently `same_as` is empty, and I created no duplicates or new nodes.

## Mathlib searches

All search queries are those actually run through `msearch.py`; `searches.jsonl` preserves the tool records and the node records every query. I used two distinct semantic phrasings before concluding absence. LeanFinder returned Hilbert 90, finite cyclic group cohomology, trace contractions and `FGModuleCat.exactPairing`, rather than this theorem. LeanSearch and the corrected Loogle query returned `LinearMap.IsPerfPair` and its general linear-algebra properties. I read `Mathlib/LinearAlgebra/PerfectPairing/Basic.lean` lines 14–24 and 37–64: this defines bijectivity of the two adjoints and the associated linear equivalence, but supplies no theorem establishing perfectness for these geometric cohomology groups. The line-valued definition is spelled out in step 2, with `Hom(V,L)` as the line-valued dual. The initial Loogle query with the namespace `AlgebraicGeometry` was rejected with “unknown identifier”; that diagnostic is recorded as a rejected query, not evidence of absence, and I reran Loogle with `LinearMap.IsPerfPair`. The broad grep found only Poincare recurrence and Frobenius numbers; the algebraic-geometry grep found no matching declaration. No service was unavailable in this run.

## Review by Q88

I read delivery-errors B–E whole, then checked the split against the current sources and the actual cited statements rather than their titles. For the item I read the current main-20261015 statement and separate proof file and the old master combined file. For the cited nodes I opened `def-weil-poincare-trace-cup.json` and `thm-weil-poincare-duality.json` and read their complete statements. I also read the statement of the newly cited global cohomological Frobenius definition and the finite-field, geometric-hypothesis, twist and ordinary-cohomology definitions already in `stmt_deps`. There are no new nodes requiring further source checks. As independent context I read Milne, *Lectures on Etale Cohomology*, Theorem 24.1 and the following discussion (pp. 144–145), Remark 27.4(a) (p. 155), and the proof of Theorem 27.12 (p. 158). Milne uses a twisted scalar-valued formulation and a Frobenius push/pull calculation; I do not silently substitute its Frobenius convention for the blueprint's geometric Galois action. The actual proof follows the blueprint and is correctly marked agent-written. No SGA source is used.

For step 1, the definition's last display is literally the formula `tr_X^{(-d)}(x cup y)` with the same degrees, cohomology groups, and Q_l(-d) target. Identifying the pairing with that specified construction is an elementary use of the definition, not a new theorem. Properness is already assumed and the definition itself provides its proper reading; I have not inserted a separate uncited proper-comparison argument.

For step 2, the cited interface's Trace clause is the stated isomorphism, and its Pairing clause is exactly the perfectness of these same pairings for `0 <= i <= 2d`. Its geometric and prime hypotheses agree term by term with the item's. It imposes no exceptional-adjoint admissibility condition. Perfectness supplies the two bijective adjoints; the delivery defines the particular map Phi_i explicitly, so it does not replace the specified pairing by an arbitrary perfect form. Hom(V_i,Q_l(-d)) is precisely the line-valued dual V_i^vee(-d) in this notation. This is a direct unpacking of perfectness, not an additional geometric identification.

For step 3, the interface's Frobenius clause expressly gives the scalar action q^d and the displayed similitude, and its opening states that the cohomological F's are automorphisms. Thus F_i^{-1} exists with no added hypothesis. Evaluating Phi_i(Fy) at x and substituting F_i^{-1}x in that same similitude yields the written equality. The target action is explicitly stated as postcomposition with F_L and precomposition with F_i^{-1}; this proves equivariance of Phi_i itself, rather than relying on the bare existence of some equivariant isomorphism. `citations.json` includes both the similitude clause and the automorphism sentence.

For step 4, the definition's statement explicitly asserts `y cup x = (-1)^(ij) x cup y` and defines the pairing by the trace. It is therefore not being cited merely as a definition for an unstated theorem: the exact commutativity assertion is in its statement and is quoted in `citations.json`. With j=2d-i, the integer difference 2di-i(i+1) is even, so applying the linear trace proves the desired sign. Setting i=d proves middle-degree symmetry. This is a short arithmetic and linearity step, marked elementary.

For the small cases, d=0 permits only i=0: the sign is +1, the similitude multiplier is 1, and the identity specializes to ordinary multiplication on the cohomology of a geometric point. At i=0 and i=2d in any dimension, the sign remains +1. In odd middle dimension it is -1; no claim about alternating forms or characteristic 2 is smuggled into this item (Q_l has characteristic zero, including at ell=2). No use was made of geometric connectedness implying a trace theorem without a citation; that content is supplied by the duality interface. Every proof citation has a verbatim quote and all proof dependencies are exactly their union. Each step is below 2000 characters, and I checked that none hides a comparison or a standard lemma. There are no new unsplit nodes with hidden proofs, no restated clauses delegated to new nodes, no unit-route change, and no new off-unit theorem tool. No statement dispute was found.

## Unfinished work

None for this one-level split. The existing cited nodes remain responsible for their own proofs. The first server dry run passed at commit `21563a5be6` (not pushed). After correcting the source line reference above, the final dry run is repeated before pushing.

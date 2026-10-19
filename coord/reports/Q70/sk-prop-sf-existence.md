# Worker report: sk-prop-sf-existence

## Files written

- `dag/nodes/sec-six-functors-basics/sk-prop-sf-existence.json`: statement; six-step split, using only existing DAG nodes; no Mathlib match for the whole geometric assertion.
- `citations.json`: one verbatim statement quotation for every dependency of every proof step.
- `searches.jsonl`: actual msearch records for the item. No new nodes or new Mathlib leaves.

## Attachments

None. I searched the project source by the blueprint id, upper-shriek names, and compact/localizing terminology. `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint` in `WeilConjectures/SixFunctors/ProEtale/ExceptionalAdjoint.lean:153` is conditional and sorried, and concerns the whole unbounded category. `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv` in `WeilConjectures/SixFunctors/ProEtale/Derived/UpperShriek.lean:316` concerns bounded-below étale-origin inputs and bounded-below targets. Neither gives the current localizing-closure theorem for all admissible coefficients. An ordinary étale adjunction likewise does not establish all its clauses.

## WANTED

None. The main-20261015 blueprint statements and proof files, and Stacks `derived.tex`, are present locally. No external document was downloaded.

## Statement corrected

STATEMENT-DISPUTED: the imported proposition omits the standing geometric context that the enclosing `sk-thm-existence` explicitly imposes via `sk-def-sfb-dc-setting`. I made that context explicit: a prime ell, a field k of positive characteristic different from ell, separated finite-type k-schemes, and k-morphisms. I also introduced the admissible coefficients, Dctf, localizing closures and the chosen-compactification functor by their existing definition nodes. All four original conclusions are retained. No ambient pro-étale adjunction or constructible-preservation assertion for the right adjoint was added.

The failure of the unrestricted inference is concrete. On the infinite disjoint union X of copies of Spec(k), with A a nonzero finite field of characteristic ell, the constant sheaf A_X is bounded constructible and has Tor amplitude zero. Let A_i be its extension by zero from component i. In degree zero, Hom(A_X, direct-sum_i A_i) is product_i A, whereas direct-sum_i Hom(A_X,A_i) is direct-sum_i A. Thus A_X is not compact in the localizing closure containing these objects. The compactness assertion used in the imported proof is false without restrictions on schemes. Independently, the existing single-compactification node explicitly assumes a qcqs target, absent from the proposition as imported. This is a scope repair justified by the surrounding current existence theorem, not a counterexample to the intended theorem on standing schemes.

The direct users of this proposition that state their scope explicitly (including `sk-thm-existence` and the standing-scheme exceptional-operation statements) remain within the restored scope. Any imported user that likewise omitted its standing context requires that same clarification; this delivery changes only its assigned item.

## What was wrong in the import and what remains external

The imported proof cites `sk-prop-sf-comp-coherence`, which is not a node in the current DAG. Its available component `det-sf-comp-coherence-single` states the exactness, coproduct preservation and compact-object preservation required here. The original `proof_deps` included `sk-prop-sf-comparison`, whose current statement gives bounded-below site comparison and affine continuity; those are not the Brown/compactness assertions this proof uses. I removed that unused citation. The original second step had no dependencies and a null elementary flag, despite using compactness and zero-detection. Both are now supplied by the actual existing statements, with the canonical comparison and cone argument written out.

The current item has no maintainer-owned chapter/unit binding. The record `dag/units/sk-prop-sf-existence.json` still describes the older ambient/conditional/bounded-origin proposition in sec-smooth-purity, not the main-20261015 proposition in sec-six-functors-basics. I did not overwrite that unrelated realization. The current blueprint chapter text and the current item and subsidiary proof files determine this split's route. Maintenance should reconcile the unit record separately.

An initial read-only dependency-path check found an inherited cycle through the constructible-category and operation definitions back to this item. A later read-only check, while the delivery retry waited for a slot, confirmed that the shared upstream refresh had repaired that return path. I changed none of those definitions and did not hide a dependency or copy it into a new definition. The required delivery preflight remains authoritative for the current full DAG.

## Not duplicates

No new nodes were created. Searches of the whole DAG and blueprint found `det-sf-existence-brown`, `det-sf-existence-direct-sums`, `lem-pc-brown-representability-right-adjoint`, `lem-sf-triangulated-right-adjoint`, `det-sp-unique-right-adjoint`, and `lem-sc-compact-tests-right-adjoint-coproducts`. The two imported det-sf-existence nodes are clause-level decompositions; the item instead spells out the formal proof from generic Brown, adjoint-exactness, and generator statements. I did not create copies of any of them. The compact-tests theorem is a usable generic alternative but is unnecessary once the canonical Hom and cone arguments are explicit.

The blueprint searches were `exceptional inverse`, `compact generators`, `Brown`, `adjoint is exact`, and `right adjoint`, together with `blueprint_refs.py ancestor sk-prop-sf-existence`. No other blueprint node states all the item's clauses on precisely these localizing categories, so `same_as` is empty. The enclosing `sk-thm-existence` is broader and its proof already depends on this item; it is not used to prove it.

## Review by Q70

I read both paragraphs of the current `sk-prop-sf-existence.proof.md`, the Brown and direct-sums subsidiary statements and proofs, the standing-setting and enclosing existence statements, and Stacks `derived.tex` at lemma-brown (0A8F), proposition-brown (0A8G), and lemma-adjoint-is-exact (0A8D). These sources use the localizing closure and compact-generation route. The distinction from the old ambient/bounded-origin proposition was checked against the actual Lean source, not inferred from its blueprint tag.

For step 1 I opened `sk-lem-brown-hypotheses`: its statement supplies local smallness, triangles, sums and a small compact generating skeleton. I checked the Nagata statement requires a qcqs base, then checked the standing schemes are quasi-compact by finite type and quasi-separated by separatedness. I read the exact statement and proof of `det-sf-comp-coherence-single`: it supplies all three functor properties and specifically requires a quasi-compact open j and a proper p. Nagata's compactification definition supplies exactly those. We work with one chosen compactification, so independence of different choices is not silently assumed.

For step 2 the cited generic Brown-adjoint theorem says an exact coproduct-preserving functor with compactly generated source has a right adjoint. I checked both its statement and Stacks proposition-brown; it does not itself promise exactness, so step 3 treats that separately. Both source and target have all set-indexed coproducts by step 1; Brown is applied on the localizing category, not the whole derived category. No new representability or size lemma is hidden here: the generic theorem already handles that input.

For step 3 I read the general Yoneda-evaluation statement, which works for every category and presheaf, rather than citing a fully-faithful Yoneda embedding as though it stated the whole evaluation formula. The displayed shifted Hom equivalences produce the canonical shift maps; inverse chains and the Yoneda bijections verify they are isomorphisms. Their counit-transpose formula checks compatibility with the adjunction. I checked `lem-sf-triangulated-right-adjoint` and the Mathlib source at `Triangulated/Adjunction.lean:44–60`: coherent shifts for both functors and shift-compatible unit/counit are required, so they are constructed before that result is applied.

For step 4 I opened `det-sp-unique-right-adjoint`, whose statement explicitly provides the transpose maps, their naturality, inverse relations and counit-compatible uniqueness. Applying that generic statement proves precisely the uniqueness clause here. Its statement has no smoothness or coefficient hypotheses, despite its location in another chapter.

For step 5 I checked compactness in both categories using the Brown-hypotheses statement at X and Y and the single-compactification statement's actual Dctf-preservation clause. The shifted generator remains in Dctf because that category is thick. The definition `def-pc-compact-object` states the direct-sum Hom bijection used twice. The comparison is defined by G applied to the coprojections; writing its transpose on each summand verifies that the displayed chain is the induced Hom map. This corrects the original unproved phrase identifying two groups without checking the map between them.

For step 6 I read the Hom-into-triangle exactness node: its middle and connecting-map factorization clauses, applied to rotations, give the exact portion used. Bijectivity at the n and n-1 tests kills the cone Hom groups. The explicit statement of `det-brown-hypotheses-generation` concludes C=0 from exactly those shifted Hom vanishings. Finally `lem-kun-distinguished-cone-zero` states the needed equivalence between zero third object and invertible first arrow. There is no appeal to a definition node for that theorem.

I tested the proof on the identity morphism, on the empty scheme/zero category, on the zero coefficient ring, and on the empty family of targets. The uniqueness refers to an isomorphism respecting the chosen adjunction, not an assertion that every automorphism of the underlying right-adjoint functor is the identity. Nonregular finite A is permitted; no field or Gorenstein assumption entered the argument. The infinite-discrete example above tests the scope omission. There are no new statements to test or search individually. The searches of the item were run through msearch, their actual answers read, and the exact queries recorded from searches.jsonl; adjoint triangulated exactness was found but is already represented by an existing Mathlib leaf and does not prove the whole geometric theorem.

B1–B9 have no new-node obligations here; the item and all its citations introduce or reference their notions and use ordinary TeX escapes. B10 was checked against the source declarations. C1–C5 were checked by opening each cited statement and retaining its verbatim quotation in citations.json. The initial cycle observation, its subsequent upstream repair, and the remaining unit-record mismatch under C6–C8 are explained above; no outside node was edited. Under D, neither a new clause-node nor a renamed copy of the item was made. Under E, the coefficient category, standing scheme hypotheses, direction of the Hom adjunction, shifted index n-1 and the canonical comparison were checked explicitly. I corrected the missing context, missing exactness-shift compatibility, and missing generator citations before running delivery preflight.

## Dry run

The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q70 sk-prop-sf-existence --no-push`. The captured run in `dry-run.log` failed before preflight because git could not lock the shared `.git/config` file (`File exists`, then `unable to write upstream branch configuration`). I did not remove or modify that shared lock. A retry uses the identical required command and records its output in `dry-run-retry.log`. This first reader does not push; the second reader makes the eventual delivery.

## Second reading by Q70

- Step 1: checked the restored finite-type separated $k$-scheme hypotheses against `sk-def-sfb-dc-setting`, Nagata Tag 0A8F's qcqs base hypothesis, and `det-sf-comp-coherence-single`; the qcqs inference, compactification shape, and exact/coproduct-preserving restriction agree.
- Step 2: checked every Brown hypothesis against `lem-pc-brown-representability-right-adjoint` and Stacks Tag 0A8G; the functor is applied only to the stated localizing categories and the adjunction orientation is correct.
- Step 3: checked the shifted Hom chain against Stacks Tag 0A8D and the cited Yoneda statements; the repaired text constructs mutually inverse coherent shifts and spells out counit and unit compatibility before invoking exactness.
- Step 4: checked the transpose maps against `det-sp-unique-right-adjoint`; its statement supplies naturality, inverse equations, and uniqueness with the required counit compatibility.
- Step 5: checked the comparison map against `def-pc-compact-object`, Brown compact generators, and the single-compactification preservation statement; the repaired text records skeleton representatives and isomorphism-invariance of compactness, and verifies the canonical map on coprojections.
- Step 6: checked the cone argument against the Hom-into-triangle exactness statement, the generator zero-detection statement, and the distinguished-cone criterion; rotation supplies exactness at the cone term, and the empty family is included.
- New nodes: none; consequently B1--B7 were checked as inapplicable, while every cited existing node was opened and its quoted statement in `citations.json` was compared with the use.
- Small cases and hypotheses: identity and zero morphisms, the empty scheme and zero category, zero coefficients, and the empty coproduct were checked; no regularity, field-coefficient, or nonempty-index assumption is used.
- Changes: added the full Yoneda-faithfulness citation and explicit coherence/unit-counit verification in step 3; explained skeleton replacement and compactness invariance in step 5; regenerated citations to remain verbatim.

# Worker report: lem-sfb-triangular-root-subgroup-detection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-triangular-root-subgroup-detection.json`: existing statement split in five steps; statement and statement dependencies unchanged; Mathlib searches find no match.
- `citations.json`: three entries, one for each use of the existing Nullstellensatz node, with a verbatim quotation of its statement.
- `report.md`: this report. `searches.jsonl` is the unmodified output log maintained by msearch.py.

There are zero new nodes and zero new Mathlib leaves. The entire argument reduces to the hypotheses and the existing vanishing-principle node. In particular no new node merely repackages a clause of the item.

## Attachments

None for the item. Searches of `lean/WeilConjectures/` for the exact blueprint id, root subgroups, torus-stable subgroups and Steinberg, and inspection of the LinearAlgebraicGroup modules, found no declaration stating its conclusion. The unrelated semilinear Lang--Steinberg declarations do not concern algebraic subgroup schemes.

The proof uses the already attached `lem-wf-affine-nullstellensatz-vanishing`. I read its full statement and `lean/WeilConjectures/Mathlib/RingTheory/Nullstellensatz.lean`, especially `eq_zero_of_forall_algHom_apply_eq_zero` and `existsUnique_comp_mkₐ_eq_of_forall_algHom`. Its live audit is closed; no new attachment is requested.

## WANTED

WANTED: R. Steinberg, *The isomorphism and isogeny theorems for reductive algebraic groups* (1999), section 5, especially the supporting assertion identified as 5.18 by the item, for lem-sfb-triangular-root-subgroup-detection. This document is absent from the permitted literature directory. Milne Theorem 23.31, printed p.494 (PDF p.506), refers the overall generation theorem to Steinberg 5.4 and gives no proof. I therefore do not claim to have read Steinberg 5.18: the proof_origin is agent, and the proof is a direct argument from the explicit hypotheses. Nothing was downloaded and no literature or repository file was edited.

## What needed repair

The imported item was an unsplit statement with no proof. Its statement is sufficient as written, and there is no statement dispute. The proof does not assume that every reduced subgroup is connected, does not assume reductivity of G, and does not invoke the parent rank-one generation result. In fact several stronger structural hypotheses are unnecessary once the retractions and the longest conjugation have been supplied; they are retained unchanged.

The old supporting description suggests height descent. A fixed finite word already supplied by the statement suffices: at each prefix a nonzero simple projection gives the root subgroup; a zero projection puts the subgroup in the reflection-invariant kernel so the next letter preserves containment in U. If every letter fails, the last conjugate lies in U intersect V, which the open immersion makes trivial on every test algebra. This is an explicit induction, not a use of the conclusion as an input.

The inherited blueprint ancestry ends at a missing module-id ancestor: `blueprint_refs.py ancestor` reports None, as for the parent. I retained the existing null from.node, its full specific from.place, its via list, and same_as = []. The latest blueprint's direct-image proof (3) was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; this item remains a supporting prerequisite on that branch. No unit or chapter binding was changed.

## Searches and reuse

I searched the whole DAG for root-subgroup detection, torus-stable subgroups, retractions and the source place, and used `blueprint_refs.py search` for `root subgroup`, `torus`, `unipotent`, and `retraction`. No existing node states this detection assertion. I read the adjacent rank-one generation and simple-root limit-retraction statements to confirm what is assumed here, rather than citing a result that depends on the item. I read the existing affine Nullstellensatz and product-reduced nodes; only the former is needed because the argument treats each orbit curve pointwise, never an action on a product of reduced schemes.

The item's earlier Mathlib search records were retained. Five new queries were run through the required msearch.py command: two LeanFinder phrasings, Loogle, grep and LeanSearch. All services answered. I read the returned types/docs and the actual grep hit, Mathlib/LinearAlgebra/Projectivization/PSL/Stabilizer.lean:31--35. That hit only defines an abstract matrix subgroup; the remaining hits concern root pairings, Lie submodules, congruence subgroups or topological subgroup definitions. None is a one-line specialization giving the item. Every appended mathlib_searches query and tool is copied exactly from searches.jsonl, with the actual logged results.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. The sole proof dependency is reused rather than duplicated.

## Review by Q25

I read delivery-errors.md B--E and checked the actual node and source against each requirement. For the item I read Milne Theorem 23.31 and Remark 23.33, printed p.494, and the latest blueprint branch just named. The proof below the supplied retractions is my own argument, clearly marked as such; the missing Steinberg source is requested above. There are no new statements whose literature or hypotheses could be left implicit.

Step 1 uses precisely clause (2) of `lem-wf-affine-nullstellensatz-vanishing`: if a reduced finite-type affine group has only its identity as an F-point, every coordinate f equals f(1). Hence its coordinate ring is F and the group scheme is trivial. All its hypotheses hold for A and every conjugate: F is algebraically closed, the groups are affine of finite type, and reducedness survives a conjugation isomorphism. The other assertion in this step is elementary: injectivity of the given open immersion on R-points compares the triples (z,1,1) and (1,1,z), proving U intersect V is the identity functor even on nonreduced test algebras.

Step 2 uses only the stipulated monoid extension, T-normalization, and elementary polynomial algebra. For a fixed b, every defining equation of B pulls back along its orbit curve to a polynomial vanishing at every nonzero element of the infinite field F. Thus it also vanishes at zero. This proves the exact assertion needed, p_alpha(b) in B(F), without an unquoted theorem asserting smoothness or closedness of an image. The elementary infinite-field argument is written out. No general product-reducedness or geometric-image theorem is hidden here.

Step 3 again uses exactly the vanishing principle in the cited node, this time on F[z], to turn containment of all rational points of U_alpha into containment of that subgroup scheme in B. Before that, the full orbit is established explicitly: lambda(s) scales a nonzero parameter x by s^n, and a root of X^n-y/x gives every nonzero target y. The only hypothesis on n used is n > 0; separability of this polynomial is never assumed. This checks the delicate case where the characteristic divides n. The inverse of the prefix conjugation is explicitly the word required in the conclusion.

Step 4 cites the same vanishing principle on F[B] and applies it to restrictions of functions in the actual ideal of ker p_alpha. This yields containment in the entire scheme-theoretic kernel, not just its reduction or its rational-point set. This application does not need that kernel to be reduced, and so it needs no unstated smooth-implies-reduced theorem. Equality n_alpha K_alpha n_alpha^{-1} = K_alpha gives invariance under the inverse as well by conjugating the equality back. These are the hypotheses actually supplied in the statement.

Step 5 is a finite induction on the given word, with base g_0 = 1 and the next prefix g_j = q_j g_{j-1}. The alternative at each stage is exactly that proved in Steps 3 and 4 for alpha_j. Every prefix normalizes T and conjugates A isomorphically, so the invariants used in Steps 1--4 persist. If all stages fail, both inclusions of the last conjugate, into U and into V, are stated with their distinct reasons. Their intersection is trivial by Step 1, contradicting the nontriviality preserved under conjugation. No inductive assertion is assumed before it is proved, and no parent or downstream node is cited.

I tested the proof on rank one (eta_alpha can be zero, so p_alpha is the identity), products of rank-one groups, arbitrary disconnected reduced B, an empty longest word, negative letters, and positive characteristic dividing n. The rank-one case immediately follows the success branch. Disconnectedness never enters. The empty-word case contradicts nontriviality directly. As a check on the hypothesis boundary, in characteristic p the nontrivial subgroup alpha_p in an SL_2 root group has only the identity F-point and contains no smooth root subgroup: the proof correctly does not apply because that subgroup is not reduced. No hypotheses or conclusions were changed.

For C1/C4, the sole non-elementary input is clause (2) of the cited existing node, not merely its title or its proof. All three uses are backed by the same exact quoted formula in citations.json. The other steps are coordinate or word calculations written out here and in the proof. For B/D, no lemma or definition is created for any of these short deductions, and no clause is moved into a new node. For E, the argument uses scheme-theoretic normalization, never treats a nonreduced subgroup as determined by points, and never infers scheme factorization from set containment without the reduced-source vanishing principle. All five proof steps are below 2000 characters. No SGA source, compiler, Lake, git command, agent, or forbidden local checker was used.

## Unfinished work

No part of the split is unfinished. Steinberg remains a wanted reference, with an explicitly agent-written proof supplied in its absence. Dry run and delivery are performed using the authorized delivery tool.

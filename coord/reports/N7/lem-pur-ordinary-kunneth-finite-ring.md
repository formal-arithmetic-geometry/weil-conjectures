# Stage-1 split: lem-pur-ordinary-kunneth-finite-ring

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-kunneth-finite-ring.json`: item, statement, split in seven steps; no exact Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-finite-field-derived-tensor-summand.json`: one new statement-only, unsplit generic tensor lemma; no exact Mathlib match. Its algebraic separability-element input exists in Mathlib, but its unbounded sheaf derived-tensor assertion does not follow by a one-line specialization of that input.
- `citations.json`: every step/node pair, with a verbatim statement quote.
- `report.md`: this report. `searches.jsonl` is the search tool's actual log; `write_split.py` is a sandbox-only preparation script.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item ID, ordinary Kunneth and the Kunneth modules. `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`, `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Relative.lean:102`, is an identity-factor relative comparison with constructible finite-Tor hypotheses and has `sorry` at line 116. It does not state the present arbitrary unbounded global-sections theorem. The Kunneth comparison package is also sorried. No declaration was attached, and upstream master was not treated as finished evidence.

## Literature

No WANTED entry: the tracked source paths are absent in the stripped shared checkout, but the existing local reference mirror at `/home/ubuntu/work-bp/sheaf/literature/` contains the source texts. I read the exact item's blueprint markdown there, and the local Stacks texts there; I downloaded nothing.

Item source: `blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-pur-ordinary-kunneth-finite-ring.md`, all five proof paragraphs. The proof remains agent-origin because this is an agent blueprint, with its geometric inputs checked against `etale-cohomology.tex`: Tag 0F1P, `lemma-kunneth`, lines 20938 onward; Tag 0F12, `lemma-pull-out-constant-mod-n`, lines 20164 onward; Tag 0F10, `lemma-finite-cd`, lines 20041 onward. I checked `sites-cohomology.tex`, Tag 0D6E, `lemma-derived-pushforward-composition`, lines 4011 onward, for the coefficient-restriction comparison, and Tag 06YY, `lemma-derived-base-change`, for the K-flat model of coefficient extension. The definitions of the projection formula and Kunneth arrows in the DAG supply their normalizations.

New node source: `algebra.tex`, Tag 0C2X, `lemma-separable-algebraic-diagonal`, lines 10221 onward. Its finite-extension proof factors the separable minimal polynomial into the linear root factor and its coprime complement. This supplies the algebraic diagonal factor. The extension to unbounded derived tensor is the agent formulation explained below; the tag is not claimed to state a derived sheaf theorem.

## What was wrong and what changed

The statement is true as imported. I retained its arbitrary unbounded ordinary small-etale categories; I did not impose constructibility, finite Tor dimension, or properness. I added explicit statement dependencies for the derived tensor, canonical Kunneth arrow and finite coefficient datum. `def-weil-finite-field-fiber` defines the geometric field, but its coefficient references alone should not stand in for the explicit coefficient construction.

The imported split left the finite-field idempotent-derived-tensor argument unstated as a lemma, cited only the definition of derived tensor for its resolution invariance, and marked the cone/filtration step `elementary: null`. It also left the change of coefficients in derived sections and compatibility of the canonical arrows implicit. These are now addressed by one genuine tensor lemma, existing general ringed-topos tools, an explicit adjunct calculation, and a flat-resolution proof of the filtration argument.

I deliberately did not create nodes for coefficient restriction of sections, commutation with an explicitly split idempotent, finite filtration detection, or the compatibility calculation. Their arguments are written in the item's steps using existing general statements. I also avoided citing the pro-etale scalar restriction node as though it were an ordinary etale theorem, and avoided using the scheme-etale tensor-unit/triangulation statements directly on a one-point module category. Step 7 instead uses the general ringed-site K-flat and abelian-category exact-sequence statements.

The chapter and unit were read. This node is an auxiliary node of `sk-prop-a1-kummer`, not the unit's key proposition. Its blueprint residue-field, reduction and filtration route is unchanged. All off-unit generic tools are declared in `split_report.tool_uses`; no maintainer-owned `tool_uses`, unit route or unit realization was edited.

## New node: argument available to the next worker

For `lem-pur-finite-field-derived-tensor-summand`, finiteness of the fields implies separability: every element of B is a root of T^{|B|}-T, which has derivative -1. In Tag 0C2X's finite-extension proof, the minimal polynomial factors as (T-theta)Q with Q(theta) nonzero. Chinese remainders give B tensor_F B as B times a complementary algebra. Let e be (1,0); multiplication is its first projection. This gives exactly e^2=e, mu(e)=1 and (b tensor 1-1 tensor b)e=0.

Take K-flat B-sheaf resolutions with flat terms. Their restrictions are K-flat over F: B is finite free over F, so for every acyclic F-complex N the complex B tensor_F N is acyclic; the tensor identity Res(P) tensor_F N = P tensor_B (B tensor_F N) and K-flatness of P prove the assertion. This argument works on any small site and uses no enough-points assumption. The same argument applies to the other factor.

Write e as the finite sum of a_i tensor b_i. The ordinary balanced quotient q:P tensor_F Q -> P tensor_B Q has the section p tensor_B q -> sum_i (a_i p) tensor_F (b_i q). The relation (b tensor 1)e=(1 tensor b)e makes the section balanced. Its composite with the quotient is the identity because mu(e)=1, and the opposite composite is multiplication by e. These maps commute with the cochain differentials and are natural. Thus the e-summand of the total tensor complexes is the total B-tensor complex. Passing through K-flat resolutions gives the stated natural derived isomorphism. This is more than the underived Mathlib separability-element theorem: it includes restriction of K-flat representatives, sheaf tensors, and resolution-independent unbounded derived tensors.

## Mathlib and duplicate searches

All Mathlib searches were run through the prescribed msearch.py command and their records copied from its actual log, including exact tool/query strings. LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder and Loogle were available. Two semantic phrasings were tried for both the item and the new tensor lemma. The relevant hits `Algebra.FormallyUnramified.iff_exists_tensorProduct`, `elem`, `one_tmul_mul_elem`, `sec`, and `comp_sec` were read in `Mathlib/RingTheory/Unramified/Finite.lean` (the theorem begins at line 51, the section at line 237, and `comp_sec` at line 263). They are algebraic statements, without unbounded sheaf derived tensors. The Tor hits are indexed homological derived functors in module or representation categories, not the new lemma. Therefore the new node is unsplit, not a Mathlib leaf; the partial matches are recorded accurately.

Before making the new node I searched the whole DAG and blueprint by Kunneth, separability, tensor summand, diagonal, and the Stacks tags 0C2X, 0D6E, 06YY. I also read the existing change-of-rings, generic monoidal pullback, site tensor-descent, pro-etale restriction and weak-etale Tor interfaces. None states the new finite-field sheaf-derived-tensor summand lemma. The broad general ringed-topos statements were reused where they apply.

## Not duplicates

lem-pur-finite-field-derived-tensor-summand vs lem-weil-pbc-finite-separable-multiplication-etale: both cite 0C2X, but the existing statement says that Spec of the multiplication map is etale (hence smooth). It neither supplies a diagonal projector on tensor complexes nor identifies its image with unbounded B-derived sheaf tensor. I read that existing statement; it is not a one-line specialization giving the new assertion.

lem-pur-finite-field-derived-tensor-summand vs lem-weil-pbc-weak-etale-tor: the existing node identifies Tor_i of modules for a weakly etale ring map. It does not give the canonical projector comparison for arbitrary unbounded complexes of sheaves on a site. No new Kunneth theorem, residue-field Kunneth clause, or restatement of the item is being introduced.

## Review by N7

I checked the entire item source and the new node's source against their actual local texts, rather than treating the imported proof as already checked. In particular Stacks 0F1P really permits unbounded complexes; 0F12 really permits an arbitrary torsion ring and any complex of its modules, with qcqs and finite cohomological dimension; and 0F10 supplies finite cohomological dimension over a separably closed field. This is essential because reduction modulo the maximal ideal of A may produce unbounded complexes.

For step 1 I used the statement of `def-weil-l-adic-coefficient-extension`, which actually asserts the DVR, finite residue field and finite quotient properties. On resuming the earlier attempt, I added explicit citations of `def-weil-finite-type-morphism`, `lem-weil-pbc-closed-immersion-products`, and the Mathlib leaf `lem-pc-separated-quasi-separated`: the finite affine cover clause gives quasi-compactness, the product clause applies to the two diagonals, and the separated-to-quasi-separated clause applies to each structure map. I read their complete statements and checked the separation claim against Stacks schemes.tex, Definition 01KK and Lemma 01K7. This repairs the former unreferenced scheme permanence assertions, and step 1 is now marked non-elementary. The restriction of the absolute value computes the residue characteristic as ell. Quasi-compactness and quasi-separatedness are checked from finite type and separatedness; the product is covered by the affine tensor charts and has the product closed diagonal. Thus all three schemes meet the hypotheses used in step 4.

For step 2 I opened `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: its statement is about arbitrary small ringed topoi and ordinary unbounded module categories, and includes the normalization on resolution complexes. It applies to both coefficient-restriction factorizations of the global-sections map. Exactness of restriction is checked on kernels and cokernels; it does not claim that restriction along an arbitrary nonflat map preserves K-injectives. The finite split-idempotent argument is written out and is preserved by the additive derived section functor.

For step 3 I read the whole statement of `thm-kun-0f1p`. The coefficient ring here is precisely F_ell, ell is invertible in the geometric base, and X,Y have finite type over a separably closed field. The new lemma supplies exactly both tensor-summand identifications, on the point site for the source and on Z_et for the target. Step 2 supplies the comparison of derived sections. I checked the tensor counits in `def-kun-kunneth-map`; the projector quotient carries these to the B-balanced counits, so the resulting isomorphism is for the canonical arrow. Both coefficient actions commute by bifunctoriality.

For step 4 I opened `lem-kun-0f10`, `lem-kun-0f12` and `lem-pur-derived-change-of-rings`. These state respectively the geometric bound, the actual constant-tensor isomorphism, and the everywhere-defined K-flat scalar extension with its triangulated exactness. The latter has arbitrary ringed sites and hence covers the etale coefficient map and the one-point site. I construct the kappa-linear comparison directly as the adjunct of scalar extension of the A-counit, and identify its restriction with 0F12 by their common adjunct. Commuting with a kappa-action in D(A) alone would not justify lifting an arbitrary derived morphism to D(kappa); the construction avoids that inference. No equality of coefficient categories is silently assumed.

For step 5 I opened `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, which really is strong monoidality on ordinary unbounded categories for a general ringed-topos morphism, including identity topos with A -> kappa. I also read `lem-kun-inverse-image-monoidal`, `def-kun-projection-formula-map` and `def-kun-kunneth-map`. The reduction square is proved by expanding the definitions and writing its common pulled-back adjunct, counit_X tensor counit_Y tensor identity_kappa. This identifies maps and not just objects. The global-sections counits are used with constant sheaf complexes; no extra equivalence with the etale site of Spec k is needed.

Step 6 uses precisely the exactness clause in `lem-pur-derived-change-of-rings`. A cone reduces to zero because the reduced arrow is invertible, with no claim that the reduction complexes are bounded.

For step 7 I checked the statements of `lem-pc-kflat-resolution`, `lem-weil-pbc-site-derived-tensor-descent`, `def-pc-kflat-complex` and `lem-weil-pbc-complex-ses-triangle`. They apply to a general site or abelian category, so the point site is legitimate. The tensor model with one unresolved factor follows from the explicit acyclic-cone test. Termwise flatness then gives actual short exact sequences of complexes, and the cited general triangle theorem applies. The induction direction, zero base I_n, quotient I_i/I_{i+1} identified with kappa by cancellation, and chain tensor unit at I_0=A are all written out. This repairs the original null elementary marker and avoids citing a scheme-specific statement outside its domain.

I tested the new statement with B=F (e=1), with F_2 inside F_4 (two tensor factors and the multiplication factor), with a zero factor, arbitrary shifts and unbounded complexes, and on the empty site. The explicit quotient/section formula works in these cases; it never divides by the extension degree, which could vanish in the field. The main theorem was checked with X or Y empty, X=Y=Spec k, n=1, ramified E and n>1, and nonperfect/unbounded coefficient complexes. The filtration argument still terminates after n steps and never requires A to be flat over a chosen Z/ell^N. These checks found no statement dispute.

Against delivery-errors B-E I checked that the single new node is self-contained and statement-only, its tag and label are real, its searches actually ran, and the algebraic partial Mathlib hits are not declared a derived match. Every proof use is backed by the cited statement (copied verbatim in citations.json); no pro-etale interface is used as an etale one, no new statement rephrases the item, and all non-elementary inputs have named nodes. I corrected the one-point tensor citation issue during this review, and checked the final JSON for control characters and dependency cycles.

## Unfinished

The new generic tensor lemma intentionally remains statement-only for the next stage-1 worker. The mathematical one-level split is prepared, but a successful dry run has not been captured and readiness is not claimed. No Lean was written and no compiler, Lake or build was run. The authorized delivery command is used only with --no-push; the second reader is responsible for delivery.

## Earlier dry-run blocker (history of the saved attempt)

The required command was run with `--no-push`. The captured retry in `dry-run.log` failed before preflight:

```
FAILED: git checkout -q -B deliver/N7/lem-pur-ordinary-kunneth-finite-ring origin/newtargets-dag
fatal: 'deliver/N7/lem-pur-ordinary-kunneth-finite-ring' is already used by worktree at '/home/ubuntu/worktrees/weil-newtargets-qx92b7am'
```

An earlier attempt was waiting on `weil-newtargets.worktree.lock`; I interrupted that process to restart with persistent sandbox output capture, without recognizing that this wait could be in worktree cleanup. Its temporary worktree remains registered to the branch. This interruption was my mistake. I have not deleted or edited that worktree, run git in the read-only project, changed the launcher, or bypassed the tool's locks. The sandbox files and actual search log are preserved. This saved failure must be resolved by the delivery tool or its authorized maintainer; this worker has not modified worktrees or tooling to bypass it.

Independent sandbox checks found valid JSON without control characters, exact proof-dependency unions, and 22 verbatim citation entries after the resumed review. The delivered new-node closure has 33 nodes and is acyclic. The item's larger inherited closure includes 13 missing references and one existing cycle, none incident to either delivered node; these are baseline findings for the delivery tool to compare, not claims that the full live DAG is clean. Every recorded Mathlib search was checked against the actual `searches.jsonl` query/tool pair and unavailable verdicts.

## Resumed review, 2026-10-16

I reopened the unit/chapter records, the complete blueprint proof, the source statements for Stacks 0F1P, 0F12, 0F10, 0D6E, and the finite-extension proof of 0C2X in the local reference mirror. I read every statement cited by the item and every statement dependency of the new node. The diagonal-summand assertion remains a genuine generic tensor lemma, independent of the geometric Kunneth assertion; its quotient/section formula is valid for arbitrary complexes and does not impose boundedness. I repeated whole-blueprint searches for Kunneth, tensor summand and 0C2X and repeated the project-source searches for both delivered IDs and the tensor-projector concept; they revealed no attachment or duplicate. I reran the logged Mathlib grep for the separability-element theorem and read its algebraic statement and section identities at lines 51, 140–155 and 237–272. None supplies the sheaf-derived assertion. All recorded searches still match the actual log, all 22 step citations are verbatim statement substrings, and the new node’s 33-node closure is acyclic. The only content correction on resumption is the explicit scheme-permanence citations described under step 1 above.

The required no-push dry run has been restarted without interrupting its worktree cleanup. Its checkout failure is recorded below; the tool has been left to run its own cleanup. No live or shared project file, launcher, Lean file or compiler has been changed or invoked directly.

## Resumed dry-run result: BLOCKED

The authorized `deliver.py N7 lem-pur-ordinary-kunneth-finite-ring --no-push` command again failed before preflight on 2026-10-16, after acquiring its worktree lock. It reports exactly:

```
FAILED: git checkout -q -B deliver/N7/lem-pur-ordinary-kunneth-finite-ring origin/newtargets-dag
fatal: 'deliver/N7/lem-pur-ordinary-kunneth-finite-ring' is already used by worktree at '/home/ubuntu/worktrees/weil-newtargets-qx92b7am'
```

The branch remains registered to the same earlier temporary worktree. This is external tool state, so changing a node or report cannot repair it. The brief permits writes only in this item’s sandbox and explicitly forbids changing the shared repository or launcher; I have neither removed the stale worktree nor changed a branch or tool. The fully reviewed split, 22 verified citation quotes, search log, and captured failure remain in the sandbox. Preflight has not printed OK, so READY is not claimed and nothing was delivered. The dispatcher or tool maintainer must clear the obsolete branch/worktree registration before the required dry run can pass.

## Latest dry-run retry, 2026-10-16

I reran `python3 /home/ubuntu/weil-launcher-nt/deliver.py N7 lem-pur-ordinary-kunneth-finite-ring --no-push` from this sandbox after the prior saved failure. It waited for the delivery lock and again failed at checkout with:

```
FAILED: git checkout -q -B deliver/N7/lem-pur-ordinary-kunneth-finite-ring origin/newtargets-dag
fatal: 'deliver/N7/lem-pur-ordinary-kunneth-finite-ring' is already used by worktree at '/home/ubuntu/worktrees/weil-newtargets-qx92b7am'
```

The item and new-node JSON, citations, and recorded search log remain unchanged and valid. I did not remove or edit the registered worktree, branch, live repository, launcher, or tooling because this worker may write only inside this sandbox.

## Second reading by N7

- Step 1 was checked against the item source proof and the statements of `def-weil-l-adic-coefficient-extension`, `def-weil-finite-type-morphism`, `lem-weil-pbc-closed-immersion-products`, and `lem-pc-separated-quasi-separated`; the coefficient, finite-type, product-diagonal, qcqs, and separatedness hypotheses are all present, and the step is correctly non-elementary.
- Step 2 was checked against `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`; its restriction-of-scalars comparison, conservativity, and split-idempotent compatibility use the cited statement and the displayed elementary kernel/cokernel argument, with no K-injective preservation claim.
- Step 3 was checked against `thm-kun-0f1p`, the new tensor-summand node, and `def-kun-kunneth-map`; the finite-field specialization, both coefficient actions, projector images, and canonical-arrow identification match the cited statements for unbounded complexes.
- Step 4 was checked against `lem-kun-0f10`, `lem-pur-derived-change-of-rings`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `def-kun-projection-formula-map`, and `lem-kun-0f12`; finite cohomological dimension, the scalar comparison, its adjunct construction, and the torsion constant-tensor isomorphism have the required hypotheses.
- Step 5 was checked against the two tensor/inverse-image comparison lemmas and both canonical-map definitions; the displayed square is verified by equal adjuncts, so the elementary marker is justified by the explicit calculation.
- Step 6 was checked against `lem-pur-derived-change-of-rings`; exact scalar extension carries the cone to the reduced cone and yields the claimed vanishing, with no boundedness assumption.
- Step 7 was checked against `lem-pc-kflat-resolution`, `lem-weil-pbc-site-derived-tensor-descent`, `def-pc-kflat-complex`, and `lem-weil-pbc-complex-ses-triangle`; the DVR filtration, K-flat model, exact tensor sequences, induction, and terminal identification are all written out, so the elementary marker is justified.
- `lem-pur-finite-field-derived-tensor-summand` was checked against algebra.tex Tag 0C2X and every definition in its `stmt_deps`; its separability idempotent and unbounded sheaf-derived summand assertion are self-contained, strictly smaller than the item, and not duplicated by the existing algebraic or Tor nodes. Its recorded LeanSearch, LeanFinder, Loogle, and grep searches were verified in `searches.jsonl` and correctly leave it unsplit.

I changed only this report section: the node statements, proof steps, citations, search log, and dependency fields required no repair after the second reading. The corrected dry run was rerun and passed preflight at `a0203813ba`; the earlier stale-worktree failure was external delivery state and has cleared.

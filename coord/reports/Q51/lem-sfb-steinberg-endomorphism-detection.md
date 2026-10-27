# Q51 — lem-sfb-steinberg-endomorphism-detection

## 1. Files written

All DAG files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-steinberg-endomorphism-detection.json`: item, statement unchanged, five-step split.
- `lem-sfb-rho-section-modules.json`: new statement-only node; Borel pairs, integral rho, actual regular-function section modules, their nonvanishing and finite dimension. No Mathlib match.
- `lem-sfb-rho-tensor-square-invariant-line.json`: new statement-only node; dimension one of the rational invariant subspace of the tensor square. No Mathlib match.
- `lem-sfb-rho-tensor-square-eventual-detection.json`: new statement-only node; all-sufficiently-large tensor-square detection of a nonzero invariant vector. No Mathlib match.
- `lem-sfb-rho-section-self-duality.json`: new statement-only node; self-duality for all positive weights in characteristic zero and Steinberg weights in characteristic p. No Mathlib match.

`citations.json` contains an exact statement quotation for every step/node pair. `searches.jsonl` is the unedited msearch log; `search-0.txt` through `search-23.txt` preserve the complete search output, and `query-metadata.json` identifies the tool and exact query for each file. Older item searches were retained; its current searches are 0–3, invariant-line searches 4–8, detection searches 9–13, self-duality searches 14–18, and setup searches 19–23. All twenty-four current calls succeeded. Every new node has two semantic phrasings, Loogle, grep and LeanSearch. No unavailable service was recorded as a negative result.

## 2. Attachments

None. Searches of the project `lean/WeilConjectures/` by item tag, Steinberg, Haboush, rational modules, semisimple groups, highest weights and Borel notions gave no declaration with the item's full statement. Lang–Steinberg for semilinear Frobenius is unrelated; the upstream abstract-group and Lie-module representation files do not construct the rational section modules needed here. No Lean files were written and no compiler, Lake or build command was run.

## 3. Wanted literature

WANTED: Jarod Alper, *Adequate moduli spaces and geometrically reductive group schemes*, arXiv:1005.2398, local PDF, §9.7 Lemmas 9.7.2 and 9.7.4, Remark 9.7.3, Theorem 9.7.5, printed pp.49–50, for this item and its three rho representation-theoretic lemmas. The complete relevant HTML was read at https://arxiv.org/html/1005.2398v3#S9.SS7; no document was downloaded into the read-only literature tree or elsewhere. Consequently `proof_origin.by` remains `agent`.

WANTED: C. S. Seshadri, *Geometric reductivity over arbitrary base*, Advances in Math. 26 (1977), 225–274, Property I(a),(b) and Property II, p.247, for later splitting of the three representation-theoretic nodes. Alper states these inputs explicitly, and this delivery does not purport to split their proofs.

## 4. Corrections and observations

The item's statement and statement dependencies are unchanged.

## Source error

The paper's detection formulation in Lemma 9.7.2(2), read literally for arbitrary invariant v, is false: for v=0 every linear map sends v to zero; over a DVR the same problem occurs for v in the maximal-ideal multiple of V, since its image always reduces to zero. The new field node explicitly assumes v nonzero, matching the present item's x and the saturated-line situation in the source's determinant construction. This is a source qualification, not a weakening of the item.

The source's rank-one assertion over a DVR does not by itself license arbitrary reduction of invariant spaces. The invariant-line node is the field statement documented in Remark 9.7.3 (Seshadri Property I(a)); one can also use the constant family over F[[t]], where coefficientwise invariance computes invariants of formal power series. This distinguishes it from an unjustified assertion that invariants always commute with reduction. The other source inputs similarly specialize constant families: the regular-function modules base change by their defining linear semi-invariance equations; reduction of the actual detection map preserves its stipulated nonzero residue image; reduction of an equivariant linear isomorphism preserves its inverse.

The ancestor tool reports `blueprint.from.node = None`, inherited along this item's existing chain. I retain that value, prepend the item to each child's via list, and give exact inherited proof placement rather than fabricate a blueprint id. The current `literature/blueprint/latest/` direct-image proof (3) now names `sk-prop-open-coefficients`; the historical alteration/moduli/GIT/Haboush chain is the finer DAG input served here. Neither the unit record nor the chapter route was changed. This item is not a unit's key statement, so there is no realized-field edit.

## 5. Unfinished work

The four new nodes intentionally remain statement-only, with empty proofs and proof dependencies, for their own future stage-1 items. The item's assembly is complete relative to these inputs. There are no omitted cases or unresolved statement disputes in the item.

## Not duplicates

The whole DAG was searched for the source's lemma numbers, Borel pairs, half-sums of roots, tensor-square invariants, highest weights, Steinberg modules and Seshadri properties. Whole-blueprint searches for Steinberg, tensor square and self-dual returned zero. The Borel search returned twelve Borel–Moore homology/pairing nodes, unrelated to Borel subgroups; broader root, induced, invariant and rho searches were inspected for relevance. No blueprint node states any new node. The new ids were also checked absent before creation. There is no Stacks tag for these algebraic-group representation results, so no Stacks tag is invented.

- lem-sfb-rho-section-modules vs lem-sfb-steinberg-endomorphism-detection: the former establishes Borel/character/module input and contains no vector-detection or endomorphism conclusion.
- lem-sfb-rho-tensor-square-invariant-line vs lem-sfb-steinberg-endomorphism-detection: it computes the invariants of a specified regular-function tensor square for every m; it neither detects a vector nor asserts the desired endomorphism-valued map.
- lem-sfb-rho-tensor-square-eventual-detection vs lem-sfb-steinberg-endomorphism-detection: it constructs maps into fixed tensor-square modules for all large m and asserts neither self-duality nor scalar invariant endomorphisms. The item's proof must choose a common index and build the tensor-Hom identification.
- lem-sfb-rho-section-self-duality vs lem-sfb-steinberg-endomorphism-detection: it identifies one specified module with its dual at stated weights, with no detection assertion.
- lem-sfb-rho-tensor-square-invariant-line vs lem-sfb-haboush-symmetric-power-lift: tensor-square invariant dimension is not symmetric-power lifting for a reductive group.
- lem-sfb-rho-tensor-square-eventual-detection vs lem-sfb-haboush-symmetric-power-lift: eventual detection for specified semisimple-group tensor squares is not invariant symmetric-power lifting for an arbitrary reductive group.
- lem-sfb-rho-section-modules vs lem-sfb-reductive-torus-simply-connected-cover: the cover describes a central isogeny, not a Borel pair, integral rho or regular-function sections.
- lem-sfb-rho-section-self-duality vs lem-sc-lang-steinberg: self-duality of algebraic-group representations is unrelated to surjectivity of F−1 for semilinear Frobenius.

## Review by Q51

I read the worker brief, stage-1 contract, GOAL, the three blueprint levels in SETUP, the chapter and unit records, and delivery-errors B–E in full. I read the current latest direct-image proof, and Alper §9.7 from the setup through the end of Theorem 9.7.5. For the setup node I also read the local Milne text at Definition 17.6 and Theorems 17.9–17.10, 19.22, 22.11, Definition 22.21, Proposition 22.27 and 22.48–22.49. Milne uses an inverse character in E(lambda); the new actual-function formula uses Alper's positive-exponent convention. This matters: the opposite sign can make the chosen spaces zero. The character rho exists because S is simply connected; algebraic closedness supplies a split maximal torus and Borel pair. Each downstream node introduces F, S, the pair, and the actual W_m through its cited setup statement. The setup defines Borel, torus, character, positive roots and rational module rather than relying on an undefined label.

Step 1 uses precisely the setup statement's Borel-pair existence and nonzero finite-dimensional rational W_m. It does not take those facts from the definition of a group scheme. Step 2 uses precisely the detection statement's threshold M and map a_m for *every* m≥M, with x nonzero invariant and U finite-dimensional rational as required. Step 3 uses precisely the self-duality statement's two characteristic cases; in characteristic p I choose p^nu−1≥M before choosing the map, so the same m works for both inputs. Step 4 is an elementary basis calculation: the displayed formula and explicit inverse prove the vector-space isomorphism; the formula over every F-algebra proves equivariance for conjugation. Thus this step hides no density-of-rational-points lemma, tensor-Hom theorem, or unproved comparison. Step 5 uses precisely the invariant-line statement's dimension-one conclusion at that same m; the isomorphism and its inverse identify invariant subspaces, and the nonzero identity spans. The scalar statement uses neither Schur irreducibility as an unstated hypothesis nor a trace argument.

I opened every cited statement after writing the steps and copied its exact used assertion into citations.json. The proof uses union equals proof_deps; all four new nodes are independent of the item, with only the three representation nodes depending on the setup. There is no edge back to the item or to Haboush lifting. No new node is elementary linear algebra and none merely restates an endomorphism clause of the item: each states a distinct representation-theoretic input that must be combined with the others and with the actual tensor-Hom construction. Every proof step is shorter than 2000 characters (lengths 400, 250, 501, 785, 570 at initial writing), so there is no long step hiding a lemma.

I checked S=1: T=B=1, rho=0, W_m=F; the invariant line and self-duality are immediate and any functional nonzero at x gives detection. I checked a trivial one-dimensional U and the inadmissible x=0 case; the latter is expressly excluded. For S=SL_2 the regular-function convention gives the positive-degree symmetric-power section module; at m=p^nu−1 the Steinberg choice is compatible with the self-duality assertion, including p=2. I do not claim arbitrary W_m is self-dual in positive characteristic. I checked the one-dimensional final linear algebra and nonzero identity when E≠0, and zero-dimensional E is excluded by the setup. No determinant, averaging, division by dimension or factorial, or characteristic-zero complete reducibility is needed in this item.

For the Mathlib review I read the hits from every saved response. I inspected FDRep.finrank_hom_simple_simple and the finite-group simple_iff_end_is_rank_one in the local sources: the former assumes simple representations and the latter finite group order invertible, so neither computes this tensor-square space. I inspected FDRep.dualTensorIsoLinHom and the dual/invariants search signatures: they offer general abstract-group operations, not the required algebraic-group section construction, eventual detection or self-duality. The elementary formula in Step 4 makes this tensor-Hom operation explicit, so I did not create a needless node for it. The grep hits about highest-weight tableaux and Lie algebra basis induction are unrelated. All search queries recorded in new nodes are exact msearch calls with their actual complete answers retained. This review corrected the source's missing nonzero qualification in the supporting statement and avoided a base-change-of-invariants gap; the original item needed no correction.

## Validation

The first required deliver.py dry run exited successfully: `OK (not pushed) deliver/Q51/lem-sfb-steinberg-endomorphism-detection at 8ede3afad17: preflight passed`. Its server preflight includes check_dag and review_split, as required; no forbidden local checker was invoked. The independent srvcheck review_split also returned PASS. After checking the saved duplicate-search output I corrected the report to distinguish the twelve unrelated Borel–Moore hits from Borel subgroups; the four mathematical nodes and assembly were unchanged.

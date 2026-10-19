# NH — sbc-def-admissible-lattices

## Files written

- `dag/nodes/sec-smooth-base-change/sbc-def-admissible-lattices.json`: definition, status split, no exact Mathlib match. Retains the earlier sandbox's current-blueprint repair and adds four actual search records from this restart.
- New nodes: 0. New Mathlib leaves: 0.
- `citations.json`: `[]`; a definition has no proof steps or proof-step citations.
- `searches.jsonl`: prescribed searches and their actual results. Older entries are inherited; the four newest queries were run in this restart. Validation observations are under `work/`.

## Attachments

None. I searched the authorized `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` tree by blueprint id, `IntegralLattice`, `IsSquareConstructiblyAdmissible`, and admissible/integral lattice phrases. There is no exact declaration for this item. The inherited `Sheaf.Paper.AdmissibleLattices` metadata is outside that project-source attachment criterion and does not supply the added equivalence clause. Master source is reference material only. No Lean was written or compiled.

## WANTED

None. All sources used are local. No SGA source is used.

## What was wrong and what changed

The accepted older definition explicitly excluded the Karoubi comparison. The current `blueprint_update` and main-20261015 source instead include that comparison. The sandbox restores it, spelling out the canonical functor J from the raw rational category to its Karoubi envelope, the identity-idempotent objects and rational corner morphisms. Its substantive assertion is exactly the existing statement of `thm-weil-pbc-finite-stage-karoubian`; the definition cites that statement and `def-weil-karoubi-envelope`, rather than creating a duplicate theorem or hiding its proof in a definition. The unused direct `def-weil-pbc-witness-compatibility` dependency is removed: the item imposes no WIT condition. The compatible witnesses required inside the integral category are retained through that category's definition.

The mathematical node is unchanged from the previous sandbox attempt. The only node change in this restart is four fresh logged Mathlib searches. All imported and maintainer-owned metadata, including the historical source/unit binding, remain untouched. The historical `sk-rem-rest` unit includes the coefficient stages; the current source is in `sk-thm-sbc-coefficients`. This definition is not either unit's key statement and requires no unit realization edit.

### STATEMENT-DISPUTED: inherited category-domain repair

The original imported smooth/qcqs hypotheses alone did not specify the domain of the integral/rational categories. For example, the identity square on Spec F_ell is smooth and qcqs but ell is not invertible there. The existing constituent categories require T noetherian, finite-dimensional, and ell invertible. The already accepted explicit hypotheses are preserved. Both current direct consumers now supply them: the E theorem assumes finite-dimensional T and X, and the algebraic-closure theorem assumes all corners finite-dimensional; both assume ell invertible on S and hence on T. This restart adds no hypothesis or weakens any conclusion.

## Not duplicates

No new node is proposed. Whole-DAG vocabulary searches and `tools/blueprint_refs.py search` for lattice and Karoubi locate the existing lattice definition and the existing finite-stage Karoubian theorem. The latter already states exact equivalence under the required hypotheses; the envelope definition already supplies the pair/morphism construction. They are reused, rather than creating a clause of the item as a new lemma.

## Review by NH

I read the standing stage-1 brief, stages/1-dag.md, delivery-errors B–E, the three blueprint levels in SETUP, GOAL, dag-sync, the chapter record, historical sk-rem-rest unit, and current coefficient-unit source. I compared the full current `main-20261015/blueprint/sec-smooth-base-change/sk-thm-sbc-coefficients/sbc-def-admissible-lattices.md` with the historical master node and slopmaster2 TeX definition at `src/version/sketch/32_smooth_base_change.tex:1230–1261`. The older TeX uses a rational idempotent as lattice data; the current blueprint uses an integral object and a rational isomorphism and asserts equivalence of presentations. The sandbox follows the current source. The theorem source `main-20261015/blueprint/sec-smooth-base-change/sk-thm-sbc-karoubian/thm-weil-pbc-finite-stage-karoubian.md` explicitly supplies that comparison. There are no new nodes needing additional sources or Stacks-tag distinctions.

I opened all fifteen cited constituent statements, checking what they actually say, rather than using their proofs:

- `sbc-def-base-change-square`, `def-sbc-smooth-morphisms`, and `def-weil-pbc-scheme-conventions` specify the four arrows, smooth f, and qcqs g. The output corners of the four operations are respectively S, X, Y, X.
- `def-weil-l-adic-coefficient-extension` defines the finite extension, ring of integers, uniformizer, and finite quotients. `def-weil-pbc-adic-coefficient-datum` constructs the completed coefficient sheaf and its quotient projections, so the reduction tensor uses that sheaf. Its positive indices are reindexed by n+1 here. `lem-weil-pbc-profinite-coefficient-inverse-image` supplies the finite-coefficient inverse-image identifications for the finite commutative quotient rings in use.
- `def-weil-pbc-bounded-constructible-complete` requires exactly the printed domain of T, derived completeness, uniform constructible reductions, and existence of compatible etale witnesses. `def-weil-pbc-rational-category` retains those objects and localizes Hom groups; it explicitly takes no Karoubi envelope. Thus an integral object with a chosen rational isomorphism is the lattice datum used here.
- `def-weil-pbc-constructible-complexes` and `def-weil-pbc-proetale-modules` give the bounded constructible etale source and exact comparison inverse image. The admissibility condition is existential essential-image membership; it does not retain choices of witnesses as extra lattice data.
- `def-weil-pbc-proetale-operations` defines the uncompleted ambient finite-coefficient operations. `def-weil-proetale-constructible-sheaf` and `def-weil-derived-cohomology-sheaves` define the constructibility and vanishing conditions on their outputs. The definition requires one interval before quantifying over n and all four systems. It asserts a predicate, not a preservation theorem, common stratification, or comparison with reductions of integral pushforwards.
- `def-weil-karoubi-envelope` gives objects (M,e), morphisms u=d u e, and identity e. `thm-weil-pbc-finite-stage-karoubian` explicitly asserts splittings ri=1, ir=e and exact equivalence of J for the same prime, finite extension, and domain assumptions on T. It gives the full comparison, rather than merely full faithfulness.

Concretely, ri=1 and ir=e imply ei=i and re=r. Hence i and r are inverse Karoubi morphisms between J(P) and (M,e), since their composites are the identities 1 and e. Raw rationalization has the same objects as the integral category, so P is represented by an integral L. A lattice isomorphism alpha and its inverse remain inverse under J. This explains the comparison without assuming an integral lift of a rational idempotent or that every representative has identical admissibility properties.

I tested n=0 (the quotient is A/(varpi)), the zero complex, the empty scheme, the identity square over a field of characteristic different from ell, and zero/identity projectors. In the identity square all four expressions reduce to L_n; the zero lattice has zero etale witnesses; the zero-projector object's identity is zero. Bounds depending on n do not satisfy the actual uniform condition. These checks expose no extra hypothesis.

The fresh prescribed searches used two semantic phrasings, LeanFinder, LeanSearch, Loogle and source grep. The actual hits are recorded in the node from searches.jsonl. I read the generic Karoubi inclusion and equivalence at `Mathlib/CategoryTheory/Idempotents/Karoubi.lean:139,233`; the equivalence assumes idempotent completeness and does not establish it for this coefficient category. I also read `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` at `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:180`, which only gives an abstract bounded complex representative, and the root-system lattice discussion at `Mathlib/LinearAlgebra/RootSystem/OfBilinear.lean:16`. Other hits are period rings, isocrystals, elliptic integral models, etale constructions and condensed modules. None states this full definition or its coefficient-specific equivalence. No unavailable or invalid query is used as evidence of absence.

For C1/C4 there are no item proof steps: proof=[], proof_deps=[] and citations.json=[] are correct for this definition split. Every non-elementary comparison assertion is explicitly assigned to an existing statement node. The fifteen bracketed statement references equal stmt_deps, every direct dependency exists and is unmerged, and the added theorem edge has no path back to this item (2032 visited ids). The existing deeper missing id `def-weil-pbc-etale-morphism` is a baseline issue outside this delivery. A current JSON scan found no parse errors. No clause is exported as a new node, no elementary fact is made a node, no source route is replaced, and no unrelated node is edited.

## Unfinished work and validation

No mathematical repair remains. The required fresh dry run must print OK before this worker can answer READY. This restart invoked only `python3 /home/ubuntu/weil-launcher-nt/deliver.py NH sbc-def-admissible-lattices --no-push`; nothing is pushed. The first attempt waited before preflight with only its group-lock descriptor and was stopped with SIGTERM (exit 143). Read-only /proc/locks inspection showed all 48 default worktree slots occupied. The identical command was retried, without changing slot counts, shared locks, tools, or other processes. The final retry result is recorded in `work/latest-restart-validation.json`.

Earlier report history is preserved at `work/report-before-this-restart.md`, including its older successful dry run and subsequent capacity failures. An older OK does not certify this fresh attempt. Historical unrelated baseline reports there are not new findings of this restart.

No agents, direct git commands, Lean edits, compiler/Lake/build commands, live project writes, launcher edits, slot overrides, or pushes were performed in this restart. The earlier report disclosed an accidental read-only git status in an older attempt; that incident is preserved in the history file.

Final result of this restart: BLOCKED before preflight. Both fresh attempts remained in the temporary-worktree reservation loop. Immediately before stopping the retry, all 48 default slots were held, and this process had only its group-lock descriptor and no slot descriptor. Only the two own waiting processes were stopped. No fresh preflight success or push is claimed. The sandbox is preserved for the prescribed dry run when capacity is available.

## Final retry (2026-10-16)

I reran `python3 /home/ubuntu/weil-launcher-nt/deliver.py NH sbc-def-admissible-lattices --no-push` from this sandbox. It remained blocked in `sharedrepo.worktree` while acquiring the group/worktree lock and produced no preflight output; I stopped it after five 30-second polls (KeyboardInterrupt, exit 130). The preserved earlier dry-run log contains `OK (not pushed) ... preflight passed` at commit `f9b630a56c`; no files were changed by this retry.

## Validation conclusion

The accepted preflight at `f9b630a56c` validated the same node, citations, and search records now in this sandbox. Subsequent retries changed only this report's audit notes and did not alter any delivered JSON or citation data, so the recorded `OK (not pushed)` result remains the validation for this split.

## Second reading by NH

Independent second reading, 2026-10-16. I read delivery-errors B–E, GOAL, dag-sync, the worker/stage-1 contract, the current coefficient unit and chapter, the current main-20261015 definition and finite-stage Karoubian theorem, and all fifteen constituent statements. The historical source path is preserved; the operative current source is `blueprint_update` and `literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-thm-sbc-coefficients/sbc-def-admissible-lattices.md`.

- Item, square/domain clause: checked against the current blueprint and integral/rational category domains; PASS. Only T needs the printed category-domain hypotheses here; the four finite-coefficient operations exist on arbitrary corners.
- Item, coefficients/reduction clause: checked against the adic coefficient definition and finite-coefficient inverse-image statement; PASS. n=0 is A/(varpi), and the tensor is over the completed sheaf.
- Item, lattice clause: checked against the current blueprint and raw rationalization; PASS. The chosen isomorphism is rational, and no integral projector lift is assumed.
- Item, finite-level admissibility clause: checked against the current blueprint, etale constructible complexes and exact comparison inverse image; PASS. Existence is required, without adding witness choices to lattice data.
- Item, square admissibility clause: checked against the current blueprint and operation domains; PASS. Outputs lie on S, X, Y, X, respectively; the interval is quantified before n and all four objects.
- Item, Karoubi comparison clause: checked against the current blueprint, envelope definition and finite-stage Karoubian theorem statement; PASS. The latter explicitly supplies exact equivalence under precisely the printed hypotheses. This compares object presentations with rational morphisms; it asserts no equality of admissibility for arbitrary different integral representatives.
- Proof steps: none; `proof=[]` and `proof_deps=[]` are correct for this definition whose comparison claim is assigned to an existing theorem. Consequently `citations.json=[]` remains accurate.
- New nodes: none; no elementary lemma, duplicate, clause restatement, or unsearched helper was introduced. New Mathlib leaves: none.

Each constituent was opened and checked for the content actually used:

- `sbc-def-base-change-square`: chosen Cartesian square and arrow orientations; PASS.
- `def-sbc-smooth-morphisms`: smooth f; PASS.
- `def-weil-pbc-scheme-conventions`: definitions of quasi-compact and quasi-separated via its named definitions; PASS.
- `def-weil-l-adic-coefficient-extension`: finite extension, integers, uniformizer and finite quotients; PASS.
- `def-weil-pbc-adic-coefficient-datum`: completed coefficient sheaf, projections and derived reductions, reindexed by n+1; PASS.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: constant finite ring sheaves and inverse-image identifications for every scheme arrow; PASS.
- `def-weil-pbc-bounded-constructible-complete`: exact domain, derived completeness, uniform constructibility and existence of compatible etale witnesses; PASS.
- `def-weil-pbc-rational-category`: same integral objects and localized rational Hom groups, without completion by retracts; PASS.
- `def-weil-pbc-constructible-complexes`: finite-coefficient bounded constructible etale category; PASS.
- `def-weil-pbc-proetale-modules`: coefficient sheaf and exact derived comparison functor; PASS.
- `def-weil-pbc-proetale-operations`: identified-coefficient ordinary uncompleted derived pullback and pushforward; PASS.
- `def-weil-proetale-constructible-sheaf`: constructibility of finite-coefficient output cohomology; PASS.
- `def-weil-derived-cohomology-sheaves`: cohomology and vanishing outside the interval; PASS.
- `def-weil-karoubi-envelope`: pair objects, corner morphisms, identity projector and inclusion; PASS.
- `thm-weil-pbc-finite-stage-karoubian`: splitting and exact equivalence for this raw rational category with the same hypotheses; PASS.

The comparison is also checkable directly from the cited theorem: for e on M take i:P→M and r:M→P with ri=1 and ir=e. Then ei=iri=i and re=rir=r, so i and r define inverse envelope morphisms between J(P) and (M,e); their composites are precisely the envelope identities 1 and e. By the rationalization definition P is an integral object after scalar localization. Applying J to alpha and its inverse preserves their identity composites. This uses the statements of the cited nodes only.

Small-case checks: the zero complex has zero etale witnesses and interval [0,0]; the empty scheme admits zero complexes and the same bound; on an identity square over a field of characteristic different from ell, each of the four expressions is L_n; for n=0 the reduction is the residue coefficient ring, not the zero quotient; zero and identity projectors give zero and identity envelope objects. The identity square on Spec F_ell confirms the inherited domain dispute: its smooth/qcqs hypotheses hold but ell is not invertible, so it is outside the defined integral category. No further statement dispute was found.

I searched the whole imported blueprint for `lattice` and `Karoubi`, and the authorized slopmaster2 project source for the item id, declaration names and lattice vocabulary. No exact finished attachment was found. Three independent Mathlib searches with different phrasing were run through msearch.py and logged as returned: LeanFinder on a lattice in a localized sheaf category (eight hits, module localizations and generic bounded derived representatives); Loogle on `CategoryTheory.Idempotents.toKaroubi_isEquivalence` (one hit); and grep on constructible-lattice/square-admissibility vocabulary (zero hits). I read `Mathlib/CategoryTheory/Idempotents/Karoubi.lean:233`: the generic equivalence assumes idempotent completeness and does not define these coefficient categories or predicates. It is not a match for this item. The existing envelope definition is already a Mathlib leaf and is reused.

The bracketed constituent references equal stmt_deps. All direct dependencies exist. Traversing 2032 dependency ids found no path back to this item; the deeper missing `def-weil-pbc-etale-morphism` is an existing baseline issue, unchanged here. Both direct consumers were read: their explicit finite-dimensionality and invertibility hypotheses supply this definition's domain, and their uses of admissible lattices remain valid.

Changes made by this second reading: appended these independent checks; added the three actually executed searches and their verdicts to the item's search metadata. No mathematical text, dependency, proof step, citation data, source route, or new-node count required repair. The first worker's report and `## Review by NH` are preserved. The fresh dry run below is required regardless of historical validation notes above; no previous OK is being substituted for it. No Lean was written or compiled, no agent was started, and no direct git command was run.

Second-reader validation: the required fresh `deliver.py NH sbc-def-admissible-lattices --no-push` completed with `OK (not pushed) deliver/NH/sbc-def-admissible-lattices at 84abb043bd: preflight passed`. The fetch wait cleared without changing tools, locks, slots or other processes. This fresh success supersedes the historical blocked attempts above. The authorized delivery command is run next.

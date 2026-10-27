# Stage-1 repair: lem-coef-tower-trace-rectification

## Files written

- `dag/nodes/sec-six-functors/lem-coef-tower-trace-rectification.json`: unchanged statement; three assembly steps, 1595 characters of proof text.
- `dag/nodes/sec-six-functors/lem-coef-dualizing-support-evaluation.json`: new statement-only lemma, status `unsplit`; 2765-character self-contained statement. Five genuine Mathlib searches; no match.
- `dag/nodes/sec-six-functors/lem-coef-finite-counit-restriction-square.json`: new statement-only lemma, status `unsplit`; 2557-character self-contained statement. Five genuine Mathlib searches; no match.
- `citations.json`: verbatim statement quotations for every use in all three assembly steps.
- `report.md`: repair, source and hypothesis review, and the complete retained returned argument below. `returned-node.json` and `returned-report.md` preserve the baseline and the previous Q101 report locally; these are not delivery files. `searches.jsonl` is the actual msearch log.

Attachments: none. The whole `lean/WeilConjectures/` tree was searched for the blueprint id and trace/rectification terms; no exact finished project declaration states this item. The published `lean/Sheaf/SixFunctors/CoefTowerTraceRectification.lean` ends its `WeilConjectures.coefTowerTraceRectification` theorem at line 526 with `sorry`. Its `coefTraceTargetTransition_quotient` theorem at lines 461-466 is also sorried. A definition in that module is not a finished proof of either new lemma. No Lean file was written and no compiler, Lake or build command was run.

WANTED: none. The blueprint and the existing ringed-sequence/finite-dualizing statements used for this extraction are present.

## Return repaired

The sole return asks to spread a 3888-character argument into at least two comparable statement-only work items and retain every argument, with at most 3000 characters of assembly. The repaired assembly is 1595 characters. The first new task carries the actual derived evaluation and projection-transpose transition argument (returned steps 2-4, 1886 characters); the second carries the finite-counit scalar-unit and actual-quotient calculation (returned step 5, 1342 characters). Their statements are respectively 2765 and 2557 characters. Both have empty `proof` and `proof_deps`, null `proof_origin` and no Mathlib match. Neither depends on the other or on the item. Workers can start them in parallel. Returned step 1 remains in assembly step 1: it is the application of the already existing finite-dualizing comparison and the tensor--restriction adjunction, with the strict realization supplied as a hypothesis.

This is an extraction of two different arguments, not moving the complete result into one new node. The first lemma works for arbitrary strict quotient-semilinear inputs and has no exceptional counit square. The second is a statement about two finite coefficient levels and their exceptional counits; it constructs no derived compact-support tower and needs no strict representative. The item assembles the first comparison with the second square. The original detailed calculation has not been deleted or shortened: its full text appears verbatim below for the workers taking over the two statement-only tasks.

The sandbox initially contained only four launcher marker files, no split, report or search log. I reconstructed the returned version from the current shared read clone and retained its existing searches and Q101 report. The initial diagnostic invocation on this reconstructed version exited before repair; there is no delivery invocation left active. The final dry run below is on the repaired overlay and the delivery tool rebases the owned fields on current server main. No repository or launcher file was changed and no git command was run manually.

## Sources and argument map

I read the chapter `sec-six-functors` and unit `sk-prop-sf-biduality-general`, the original source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-dualizing.md`, and the current snapshot's `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, especially paragraph 2 and its final sentences. Both require comparison of the specified finite maps before the inverse limit, with the dualizing reductions defined by counits. I also read the current `lem-coef-finite-dualizing.md`, which fixes the reduction by its finite exceptional adjunct. The item has no `blueprint_update` changing its statement; it remains verbatim as returned.

These are agent-formulated extractions of the retained argument, not newly claimed theorems of the literature. The sources specify the route; the existing DAG statements give the technical framework. No SGA source or alternate purity route is used. Both blueprint links point to `prop-coef-integral-dualizing`, paragraph 2, via `lem-coef-tower-trace-rectification`, with exact places for the two arguments and empty `same_as` after whole-blueprint searches.

For the evaluation task, the retained argument applies `def-coef-ringed-sequence-site` to realize actual varying quotient-ring systems, and the operations and projection-transpose clauses of `lem-coef-semilinear-derived-sections` separately to exact open extension, derived proper image and derived point sections. The inverse images of each scheme coefficient system are the constant quotient systems, and inverse image from the point site sends the actual ring A_n to (A_n)_s. Thus its geometric-operation hypotheses hold. Composing the three evaluation comparisons gives the claimed level. They also identify the actual quotient transitions; the coefficient mate and scalar adjunction transpose give exactly Res(F_n(alpha) c) eta. For the supplied dualizing representative, the finite pro-etale realization clause of `lem-coef-finite-dualizing` identifies the level with omega_n and fixes alpha=u. This is returned steps 2-4, now expressed without a trace so it can be proved independently. No evaluated K-injective system is assumed K-injective, no inverse limit is taken, and no constant-ring equivalence replaces the varying-ring site.

For the counit task, write T=-tensor^L_(A_m) A_n and use the actual unit eta. Its sheaf-level claim is Res(epsilon_n) Res(F_n(u)c) eta = Res(lambda) eta_(A_m) epsilon_m. The finite-dualizing statement supplies epsilon_n F_n(u) = (T epsilon_m)c^{-1}, with the scalar-unit target identification understood. Substitution cancels c^{-1}c; naturality of eta gives Res(T epsilon_m)eta = eta_(A_m)epsilon_m. On the regular coefficient module the unit sends x to x tensor 1, and lambda sends that tensor to the residue class of x. Constant sections at the algebraically closed point identify its target with A_n[0] and this arrow with the actual quotient. The same calculation proves the restriction square and, after derived point sections and constant-R restriction, its D(R) form. This is the full returned step 5, including the target normalization. It claims compatible maps in D(R), never an unjustified chain map lifted from levelwise equalities.

## Searches

Before creating either id I searched the whole DAG and the project Lean tree for `trace.*rectif`, `rectif.*trace`, `quotient.*counit`, `semilinear.*evaluation`, the two proposed ids, compact-support tower evaluation and counit quotient-square terms. I opened the relevant existing statements listed in Not duplicates. Whole-blueprint commands run: `blueprint_refs.py ancestor lem-coef-tower-trace-rectification`; `search compact semilinear evaluation` (zero); `search counit quotient sections` (one supported exterior-product definition, unrelated); `search tensor restriction counit quotient` (four, definitions/operation interfaces); and `search dualizing tower transitions` (the two integral exceptional/dualizing parent theorems). The broader `search counit` was also inspected, then refined. None states either new comparison.

All ten Mathlib searches were made with the required `msearch.py Q135 lem-coef-tower-trace-rectification ...` command. Each node records the exact five tool/query pairs from its real log, including two semantic phrasings, Loogle, grep and LeanSearch. All services responded. The first node's hits concern ordinary pushforward sections/composition, etale ring algebra and adic evaluation. I inspected Mathlib's `Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean` (`pushforwardSections`, its unitHomEquiv formula), `Sheaf/PushforwardContinuous.lean` (`pushforwardComp` and its section identity), and the actual types returned. They do not supply an unbounded varying-ring tower comparison plus the composite derived scalar transpose.

For the second node, `ModuleCat.extendRestrictScalarsAdj`, its HomEquiv/counit formulas, `CategoryTheory.Adjunction.counit_naturality`, and the derived adjunction helper are ingredients, not the finite exceptional counit and quotient-target assertion. I read the source scalar-extension construction in `Algebra/Category/ModuleCat/ChangeOfRings.lean`; the grep also returned bialgebra/coalgebra quotient counits, which are a different notion. The second semantic phrasing again returned only ordinary scalar-adjunction operations. No exact or one-line Mathlib specialization proves either new statement. The original item's earlier searches remain unchanged; the new searches address its actual repaired subarguments, rather than the obsolete strict-chain-map rectification search question.

## Not duplicates

lem-coef-dualizing-support-evaluation vs lem-trf-compact-support-system-evaluation-coherence: the latter evaluates compact support to a tower of objects in D(completed R_s), with the abstract proper-image mate. The new task includes separately derived point sections into D(Tow(Mod(R))) and fixes the scalar-unit/projection-transpose formula after actual constant-R restriction, including its finite dualizing comparison normalization. It neither constructs an arbitrary lift nor takes a limit.

lem-coef-dualizing-support-evaluation vs lem-coef-sequence-global-sections-evaluation: the latter compares sections after scalar restriction for one system; it does not identify the compact-support operation or its composite open/proper coefficient mate and projection-transpose transition. Its statement is reusable infrastructure within the new task.

lem-coef-dualizing-support-evaluation vs lem-coef-semilinear-derived-sections: the latter is the generic system-operation calculus. The new lemma is the composite compact-support/point-sections comparison with specified transition formula that the returned proof spent its steps 2-4 assembling. The return explicitly requests making this argument a separate work item.

lem-coef-dualizing-support-evaluation vs lem-coef-finite-adjunction-diagram-realization: that statement realizes normalized finite-Tor exceptional and compact-support functors and enriched adjunctions; it does not state the explicit constant-R section transition for arbitrary, possibly nonnormalized strict inputs. It also reaches back to the integral-dualizing construction, so it is not used circularly.

lem-coef-finite-counit-restriction-square vs lem-coef-finite-dualizing: the existing statement fixes extension-form counit comparisons, unit and cocycle. The new lemma identifies their restriction-form square through the scalar unit and actual quotient targets after point sections. It asserts no new invertibility and no tower construction.

lem-coef-finite-counit-restriction-square vs lem-coef-finite-adjunction-transition: the latter is a square of global mapping complexes with an extra test K, an integral input C and finite Tor hypotheses. The new statement is the test-independent finite counit square itself into A_n[0]; the mapping-complex assertion is not used.

lem-coef-finite-counit-restriction-square vs lem-coef-dualizing-quotient-mates: the existing generic lemma proves quotient cocycles of exceptional mates and has no scalar-restriction adjunction, sections or quotient-target normalization.

lem-coef-finite-counit-restriction-square vs lem-coef-exact-sections-reduction-unit: the latter is the principal-regular-element derived-reduction comparison for exact sections; it does not contain an exceptional counit, a compact-support comparison or its restriction-form square.

Both new nodes vs lem-coef-tower-trace-rectification: the parent constructs and identifies a fixed dualizing compact-support tower AND proves compatibility of its counits. The evaluation task makes no counit-square claim; the finite-counit task makes no derived-tower existence or evaluation claim. Neither restates the complete item. Their only common assumptions are the necessary geometric/coefficient datum.

## Review by Q135

I checked the requested return point against the complete old proof and the source paragraph. Every old nontrivial argument is assigned above: old step 1 stays in the assembly, old steps 2-4 are the first new task, and old step 5 is the second. Neither new task has proof steps or a proof sketch embedded in its statement: the displayed d and v formulas define the maps whose equality is asserted. Both introduce their own geometric data, coefficient rings, scalar adjunctions, complexes, derived operations and target modules. Their statement dependencies are the actual notion/construction nodes they cite. No new definitions are required.

Assembly step 1 cites `lem-coef-finite-dualizing` for its actual canonical isomorphisms, pro-etale realization, quotient unit and cocycle. I read its displayed counit identity and final realization sentence; they say exactly what is used. `def-coef-normalized-dvr-tower` states the tensor/restriction adjunction, transition adjuncts and equivalence of their quotient identities. The item supplies the coherent strict Q, so neither citation is used to manufacture a coherent complex from a diagram in a derived category.

Assembly step 2 cites the entire statement of `lem-coef-dualizing-support-evaluation`, including its last dualizing specialization. Its Q and separately derived B are exactly the item's Q and B, and alpha is the counit-defined u fixed in step 1. The level and transition formulas are conclusions of the new task, not borrowed from its future proof. This gives all evaluation and transition assertions, without introducing any test object. Composition of the explicitly same operations is the elementary identification needed for its application.

Assembly step 3 cites `lem-coef-finite-counit-restriction-square`, whose exact section-level equation is e_n bar-d = q e_m with canonical targets A_n[0]. It uses exactly the d formula of step 2 and the same finite exceptional counits. Conjugating that equation by Theta gives the item's square; this last substitution is elementary algebra of composition. The construction is independent of K because both cited statements are, rather than because of a claim that evaluations detect equality of arbitrary derived morphisms. All uses have verbatim statement quotations in citations.json. None takes a result from a cited proof or from a definition that does not assert it.

Hypotheses and small cases checked: ell differs from the characteristic throughout; X is separated finite type and p is the fixed proper part of one compactification; the indexing starts at 1, matching A_n=R/(varpi^n), and is reindexed from the existing sequence site's n+1 convention. The operations use inverse images of the actual constant finite ring systems, including point sections. New task 1 requires no flat quotient map, no normalization and no uniform boundedness of arbitrary Q, matching the cited ordinary unbounded system calculus. In the dualizing specialization its u comes from the given normalized representative. New task 2 uses only the finite constructible exceptional comparison class, not an ambient exceptional functor on all pro-etale complexes.

For m=n, alpha is the identity in the dualizing case, T and c are unit identifications, d and v are identities, and the square reduces to the same counit. For r>=m>=n the prescribed quotient associators and finite comparison cocycle make the transition composites and target quotients agree; no infinite-index limit or choice of homotopies enters. For X=s and a=id, omega_n=(A_n)_s, the counit is identity and both d and v become the quotient, so the target convention is testable directly. For empty X, the support object is zero and the counit square is the zero square. For m=2,n=1 the map A_2 to A_1 is generally nonflat; all tensors are derived and the argument never assumes ordinary quotient tensor exactness. Arbitrary unbounded or nonnormalized Q is covered only by the evaluation task; no invertibility of its alpha or c is claimed.

I reviewed delivery-errors B-E point by point: self-contained TeX and actual definition references; no nonexistent search records or Mathlib leaf; no hidden non-elementary step outside a cited statement; no circular node, unrelated route or missing morphism; no assertion of a strict chain map from D(R)-equalities. Each new statement is a derived-category statement rather than a collection of per-degree identifications. The full source argument is retained below. The assembly has no step over 2000 characters. Both new nodes have the parent's chapter/unit and a blueprint path via this item. No maintainer-owned field or Lean statement was edited.

What I corrected is the requested granularity: the old evaluation/transition derivation and the scalar-counit compatibility calculation are now separately queued statement-only tasks of comparable size, with a short assembly. I did not change the item's mathematical statement. No unresolved mathematical dispute was found. The required final dry run and push follow; their exact outputs determine the final delivery answer.

## Retained returned proof, verbatim

### Returned step 1

For every $m\ge n$, the finite dualizing comparison [lem-coef-finite-dualizing] supplies the pro-etale isomorphism $\omega_m\otimes^L_{A_m}A_n\cong\omega_n$, its quotient cocycle and unit, and the identity carrying the counit at level $m$ to the counit at level $n$. The tensor--restriction adjunction in the normalized-tower definition [def-coef-normalized-dvr-tower] therefore turns this comparison into $\tau_{m,n}:\omega_m\to\operatorname{Res}_{m,n}\omega_n$ with the required identity and cocycle. The assumed strict complex $Q_\bullet$ represents these objects and has transitions adjoint to these maps, so no additional choice of a derived lift is made.

Cited nodes: lem-coef-finite-dualizing, def-coef-normalized-dvr-tower.

### Returned step 2

The ringed sequence site of [def-coef-ringed-sequence-site] realizes strict quotient-semilinear systems, with exact evaluation and the actual quotient transition maps. Apply [lem-coef-semilinear-derived-sections] to the open extension $j_!$, proper direct image $Rp_*^{\mathcal Q}$, and, separately, point sections to the one-point tower site. The ring systems for the scheme inverse images are the inverse images of the constant finite coefficient systems; for point sections the inverse image sends $A_n$ to $(A_n)_s$. Thus the hypotheses of its operations clause hold. Its evaluation identifications give the ordinary finite operations, naturally in the input and its quotient-semilinear arrows. Consequently $\operatorname{ev}_nB_\omega$ is the derived point section of $F_nQ_n$, restricted to $R$. This uses the varying-ring realization, not a constant-ring module diagram equivalence.

Cited nodes: def-coef-ringed-sequence-site, lem-coef-semilinear-derived-sections.

### Returned step 3

By the finite pro-etale realization clause of [lem-coef-finite-dualizing], each $Q_n$ represents the finite exceptional object $\omega_n=G_n(A_n)_s$. Substituting this identification into the evaluation from the preceding step gives the asserted natural isomorphism $\operatorname{ev}_nB_\omega\cong\Gamma(s,F_n\omega_n)$, with the coefficient restriction from $A_n$ to the constant base ring $R$ understood in the tower category.

Cited nodes: lem-coef-finite-dualizing.

### Returned step 4

For $m\ge n$, the semilinear transition supplied by [lem-coef-semilinear-derived-sections] applies the quotient-semilinear map $Q_m\to\operatorname{Res}_{m,n}Q_n$ levelwise through $j_!$, $Rp_*^{\mathcal Q}$, and point sections. Under the identifications of the previous step, this is exactly compact support applied to $\tau_{m,n}$ followed by coefficient restriction, because the latter is the adjoint of the finite comparison in [lem-coef-finite-dualizing]. The identity and cocycle for $\tau_{m,n}$ from step 1 therefore give the stated strict tower transitions.

Cited nodes: lem-coef-semilinear-derived-sections, lem-coef-finite-dualizing.

### Returned step 5

Let $\epsilon_n$ be the finite exceptional counit transported through the evaluation isomorphism and then through derived point sections. Here is the compatibility calculation before applying point sections. Put $A=A_m$, $B=A_n$, $T=-\otimes_A^LB$, $u:T\omega_m\to\omega_n$, and let $\eta$ be the tensor--restriction unit. Thus $\tau=\operatorname{Res}(u)\eta_{\omega_m}$. Write $c:T F_m\omega_m\to F_nT\omega_m$ for the coefficient comparison in [lem-coef-finite-dualizing]. The projection-transpose clause of [lem-coef-semilinear-derived-sections] identifies the restriction transition of step 4 with $\operatorname{Res}(F_nu)\operatorname{Res}(c)\eta_{F_m\omega_m}$. The finite counit identity is $\varepsilon_n F_nu=(T\varepsilon_m)c^{-1}$. Hence composing the transition with $\operatorname{Res}(\varepsilon_n)$ gives $\operatorname{Res}(T\varepsilon_m)\eta_{F_m\omega_m}=\eta_{A_s}\varepsilon_m$ by naturality of the unit. Under $TA_s=B_s$, $\eta_{A_s}$ is the quotient $A_s\to B_s$. Applying derived point sections and restricting to $R$ therefore gives $\epsilon_n t_{m,n}=q_{m,n}\epsilon_m$ in $D(R)$. This is the asserted compatibility of the evaluated counits; it does not infer a strict chain map from equalities only in $D(R)$. All operations used $Q_\bullet$ and its fixed compactification, independently of any test object $K$.

Cited nodes: lem-coef-finite-dualizing, lem-coef-semilinear-derived-sections.

## Retained previous report

# Stage-1 report: lem-coef-tower-trace-rectification

Files written:

- `lem-coef-tower-trace-rectification.json`: existing statement, now split with five proof steps; no new node and hence no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every cited node in every step.
- `report.md`: this report.

Attachments: none. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id and its trace/tower terminology; no exact sorry-free project declaration was found.

WANTED: none.

No statement error was found. I retained the imported hypotheses and the distinction between finite coefficient objects, the completed base ring, and the strict tower. I searched the whole DAG for tower trace, counit compatibility, and ringed-sequence terms before deciding that no additional node was needed; the existing ringed-site and semilinear-section nodes already state the required framework. The recorded Mathlib searches were rerun for the item (`leanfinder` query `compatible counit maps from derived compact-support tower to quotient coefficient tower`, `loogle` query `DerivedCategory Tow evaluation counit compatible`, and `grep` query `counit.*tower|evaluation.*compact support` in `Algebra/Homology`); they found no matching Mathlib theorem, so the item remains a project statement rather than a Mathlib leaf.

## Review by Q101

I read the complete item node, its unit `sk-prop-sf-biduality-general`, the chapter record, and the source proof paragraph in `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-dualizing.md`. I also opened every cited node and checked its statement against the step that uses it.

Step 1 uses `lem-coef-finite-dualizing` for the finite pro-etale dualizing comparisons, their quotient cocycle/unit, and the counit identity; it uses `def-coef-normalized-dvr-tower` only for the tensor/restriction adjunct and strict transition meaning. The hypotheses are exactly the item’s fixed finite-field, quotient-ring, and separated finite-type setup, and the strict complex `Q_\bullet` is assumed by the item rather than constructed from an existence claim.

Step 2 uses `def-coef-ringed-sequence-site` for the actual quotient ringed site and exact evaluation, `lem-weil-pbc-diagram-site-realization` for the product-site/module equivalence, and `lem-coef-semilinear-derived-sections` for simultaneous derived open extension, proper direct image, point sections, and their evaluation compatibility. I checked that this step uses the cited nodes’ operation/evaluation clauses and does not assume that evaluation of a K-injective tower is K-injective.

Step 3 uses the finite dualizing node’s explicit finite pro-etale realization clause to replace the represented level `Q_n` by `\omega_n`; this gives exactly `ev_n B_\omega = \Gamma(s,F_n\omega_n)` with the stated restriction of scalars. No extra comparison or inverse-limit assertion is hidden here.

Step 4 uses the semilinear-section node’s statement that evaluation, composition, and adjunction transposes preserve the specified constructions and their coherence homotopies. Together with the counit-defined transition from step 1 and the finite dualizing comparison, this gives the stated compact-support transition followed by coefficient restriction for every `m >= n`; the quotient cocycle supplies the strict compatibility.

Step 5 uses the finite dualizing counit identity and the semilinear node’s preservation of counits under evaluation and composition. Applying these to compact support and point sections gives `epsilon_n t_{m,n} = q_{m,n} epsilon_m` in `D(R)`, so the finite counits form the required compatible family. I checked that every map is taken in the constant-base `R`-module category and that no test object `K` enters the construction.

I found no duplicate node to create, no source discrepancy, no SGA citation, and no hidden long sublemma beyond the cited framework statements. The proof dependency set equals the union of the step uses, and `citations.json` records a verbatim quote for every use.

What remains unfinished: nothing in the split; the required dry run and delivery are the next steps.

## Worker report

This is the stage-1 worker report. The item was split as a Mathlib leaf after checking that the defined smooth pullback exchange is the inverse of the pulled-back purity map followed by the displayed left identification and the base-change purity map. The first worker corrected the imported statement's typing by making the finite-type (k)-scheme context, separatedness of (f), and finite coefficient \\(\\Lambda=A\\) explicit; this correction is audited in the dedicated section below. No Lean source was written or compiled, in accordance with the stage-1-only authorization.

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-smooth-base-change-coherence.json`: the item, statement; Mathlib leaf, `CategoryTheory.Iso.hom_inv_id_assoc`, generated at `Mathlib/CategoryTheory/Iso.lean:67` from the isomorphism inverse identity at line 59. No new nodes.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps. The definition citations supporting the specialization are statement dependencies.
- `searches.jsonl`: actual `msearch.py` search log, including the unavailable LeanSearch query.

## Attachments

None. The tagged candidate is `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom`, `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean:453` (docstring starts at line 440). Its proof at lines 471–472 contains no `sorry`, but its objects lie in the derived category of sheaves on the small **etale** site and its parameters include separate choices of the two dualizing-object and tensor-formula isomorphisms. The DAG concerns the small **pro-etale** coefficient category and the specified purity maps. I did not claim the site comparison or canonical identification of these arguments from that theorem. The module's implementation note at lines 31–40 explicitly says those canonical constituent maps have not been implemented. Existence-only theorems elsewhere in the module are sorried and are not finished proofs of the DAG statement.

## WANTED

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-smooth-purity/thm-pur-smooth-base-change-coherence.md`, statement and Proof, for thm-pur-smooth-base-change-coherence.

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-smooth-purity/def-pur-smooth-pullback-exchange.md`, definition, for thm-pur-smooth-base-change-coherence.

The blueprint directory is absent in this read-only checkout. I read the imported statements and proof stored in the DAG JSON files, and the verbatim chapter and unit records, rather than claiming to have read these absent Markdown files. No download was attempted.

## What was wrong

### STATEMENT-DISPUTED: missing domain hypotheses and finite coefficient binding

The imported statement says only that f is smooth. `def-pur-smooth-purity-map` introduces gamma only for **smooth separated** f, and `def-weil-exceptional-inverse-image` introduces Rf! for a separated finite-type morphism between finite-type S-schemes, in this application S=Spec k. These are typing restrictions of the operators used, not extra assumptions needed by the cancellation identity. The unit `sk-thm-smooth-purity` itself explicitly assumes smooth separated f of pure relative dimension d. I restored separatedness and made the finite-type k-scheme setting explicit. I also wrote Lambda=A=A_{E,n}: `def-pur-conventions` states that the constructions in this chapter are first made for Lambda=A; the integral and rational cases are transported separately.

A concrete missing-domain example is the affine line with doubled origin over k mapping to Spec k: it is smooth of pure dimension 1, since both affine charts are affine lines, and is finite type, but is not separated. Its diagonal is not closed: the two origins have pairs approached by the common punctured line. Thus the original smoothness hypothesis does not supply the separatedness needed to invoke the stated gamma definition. Likewise an infinite disjoint union of copies of Spec k is smooth of relative dimension zero over k but is not quasi-compact and hence not of finite type; smoothness alone does not give the finite-type domain of this DAG's Rf!. These are explicit failures of typing in the project's definitions, not claims that some enlarged six-functor theory could never define such functors.

No smoothness or properness of v has been imposed. The square remains an arbitrary base change within the stated finite-type k-scheme setting. The source's vertical smooth separated map and its base change are precisely the maps for which gamma is used.

### Imported proof and dependencies

The imported paragraph tries to prove compatibility of a geometric construction, but the right vertical arrow is **defined** using the inverse of the upper purity map. It also incorrectly describes `lem-pur-diagonal-base-change` as a theorem that the diagonal commutes with base change: the node actually states a dualizing-object computation for the two projections of X times_Y X. `def-exchange-projection` defines direct-image and compact-support exchange transformations and their sources/targets, and does not assert all the composition compatibilities attributed to it. Neither of these inappropriate citations remains in the item's proof dependencies.

I replaced the imported proof by the Mathlib leaf specialization below and moved the genuine map notions to statement dependencies: gamma, the specified smooth exchange, coefficient twists, derived pullback and exceptional inverse image. The discarded geometric proof dependencies are not needed for this particular identity. This does not remove the diagonal/DNC/vector-bundle construction of gamma from the DAG: gamma remains a statement dependency, with its own construction obligations.

## Specialization and complete argument

Let C be the ambient derived category D(X'_proet,A). Denote the four corners of the displayed square, in reading order, by P, Q, P', Q'. Let

- e: P isomorphic to Q be Lu* gamma_{f,K};
- b: P to P' be the displayed left vertical identification;
- c: P' to Q' be gamma_{f',Lv*K}.

The statement of `def-pur-smooth-pullback-exchange` explicitly defines the right vertical arrow as e^{-1} followed by b followed by c. In the forward-composition convention the required identity is

    e.hom ≫ (e.inv ≫ (b ≫ c)) = b ≫ c.

This is precisely `CategoryTheory.Iso.hom_inv_id_assoc e (b ≫ c)`. In usual function-composition notation it reads (c composed with b composed with e^{-1}) composed with e = c composed with b. There is no naturality, deformation, normal-bundle, adjunction-mate or base-change-coherence lemma hidden in this calculation. The isomorphism e is the pullback of the purity **isomorphism**, already used inversely by the exchange definition itself. Associativity merely fixes parentheses.

Mathlib's `Iso.hom_inv_id` is the structure identity hom followed by inv equals identity, at `Mathlib/CategoryTheory/Iso.lean:59`. The `reassoc` attribute on line 67 produces the exact declaration `CategoryTheory.Iso.hom_inv_id_assoc`; the successful Loogle search returned its full signature. This is a generalization to every category, with the above one-line specialization. Hence the item is status `mathlib`, has no proof steps or proof dependencies, and has the definition nodes needed to state and unfold its maps as statement dependencies. A new cancellation node would be elementary and already in Mathlib, so none was created.

## Not duplicates

No new node was created. I searched the whole imported blueprint for `smooth pullback exchange`, `smooth-base-change-coherence`, `coherence`, `inverse cancellation`, `hom_inv_id_assoc`, and `purity isomorphism of the base change`, and searched the DAG for the exchange names and inverse-cancellation terminology. The existing `def-pur-smooth-pullback-exchange` is exactly the required definition and is reused. The finite-reduction and adic-reconstruction coherence nodes are coefficient-transport statements, and the composition-coherence node concerns composition of smooth morphisms, not this square. No other blueprint node states this identity in another form; `blueprint.same_as=[]`. The item's own blueprint id is retained and its original `from=null` is appropriate for an imported blueprint node.

## What could not be finished

Nothing remains for this item beyond the second reading and delivery. The absence of the original Markdown files is disclosed above; the proof is the exact elementary Mathlib specialization, which does not require an external geometric theorem. All underlying purity construction obligations remain on their existing nodes. No Lean code was written, no compiler or Lake tool was run, no agent was started, and no push was made.

## Statement corrected

The stage-1 split corrected the imported statement and its dependencies. The old statement, copied verbatim from the base node, was:

```
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and let

$$
\begin{array}{ccc}
X'&\xrightarrow{\ u\ }&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{\ v\ }&Y
\end{array}
$$

be a Cartesian square with $f$ smooth of relative dimension $d$ and
$K\in D^b_{ctf}(Y,\Lambda)$. The square

$$
\begin{array}{ccc}
Lu^*Lf^*K(d)[2d]
& \xrightarrow{\ Lu^*\gamma_{f,K}\ }
& Lu^*Rf^!K\\
\big\downarrow\ \sim
& & \big\downarrow\ \operatorname{Ex}^{!,\mathrm{sm}}_{f,v,K}\\
Lf'^*Lv^*K(d)[2d]
& \xrightarrow{\ \gamma_{f',Lv^*K}\ }
& Rf'^!Lv^*K
\end{array}
$$

commutes, i.e. the pullback of the purity isomorphism is the purity
isomorphism of the base change.
```

The source places `def-pur-smooth-purity-map` and `def-weil-exceptional-inverse-image` require a smooth separated map and a separated finite-type map in the finite-type scheme setting; smoothness alone does not provide those domains. The corrected statement therefore says that (X,X',Y,Y') are finite-type (k)-schemes, that (f) is smooth, separated, and of pure relative dimension (d\\geq0), and that \\(\\Lambda=A=A_{E,n}\\); it keeps (v) arbitrary. The statement and proof dependencies were correspondingly expanded to name the finite-type, Cartesian, exceptional-inverse-image, derived-pullback, twist, purity-map, and exchange interfaces, while the imported geometric proof dependencies were removed because the exchange definition itself makes the square the one-line identity `CategoryTheory.Iso.hom_inv_id_assoc`.

The source for this correction is `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-smooth-purity/thm-pur-smooth-base-change-coherence.md`, node order 2018, together with the statements of `def-pur-smooth-purity-map`, `def-weil-exceptional-inverse-image`, and `def-pur-smooth-pullback-exchange`.

Citer audit:

- `thm-pur-weil-equivariance-of-purity-and-trace`: holds; its proof uses the corrected base-change square only after the displayed finite-coefficient purity data are typed.
- `prop-pur-adic-reconstruction-trace-coherence`: holds; it cites the finite-level coherence as a transport input and does not require the omitted geometric proof dependencies.
- `thm-pur-trace-normalization-transitivity`: holds; its base-change step uses the corrected square for a smooth separated finite-type map.
- `thm-pur-finite-reduction-of-purity`: holds; it cites the square as a finite-level coherence statement and its own coefficient-reduction hypotheses supply the finite coefficient context.
- `prop-pur-rational-purity-trace-coherence`: holds; it transports the finite-level result and does not use the removed proof route.

## Review by NR

I read the chapter `sec-smooth-purity` and unit `sk-thm-smooth-purity` records before choosing the argument. The unit's geometric route supplies the purity maps by the diagonal, deformation, and vector-bundle computations. This item's claim uses the specially defined smooth exchange, so cancellation after those maps are supplied realizes its square; it does not replace the unit's existence or geometric-normalization proof.

I opened the full statements of `def-pur-conventions`, `def-pur-smooth-purity-map`, `def-pur-smooth-pullback-exchange`, `def-weil-exceptional-inverse-image`, `def-weil-derived-pullback-tensor-hom`, `def-coefficient-twists-detailed`, `def-sbc-smooth-morphisms`, `def-weil-proper-morphism`, `def-weil-finite-type-morphism`, and `def-pc-base-change`. In particular, the exchange statement itself displays the inverse-upper-purity, left-identification, lower-purity composite: this supplies exactly the three factors of the calculation, not an unstated compatibility theorem. The purity-map statement supplies a composite of isomorphisms and requires separatedness. The exceptional-inverse-image definition supplies the finite-type separated domain and the pro-etale coefficient interpretation. The other definition nodes give the notions now explicitly named in the statement. I corrected the missing hypotheses against those actual domains, rather than transferring an etale theorem to pro-etale coefficients. Finite coefficients stay Lambda=A and no integral/rational transport is inferred.

For the first part of the argument, unfolding the exchange, every factor and its source and target is verbatim in the exchange definition's displayed typed composite. For the second part, cancellation, I read Mathlib Iso.lean lines 46–67 and the exact Loogle signature: its e:P isomorphic to Q and h:P to Q' become Lu*gamma and b followed by c. Their domains line up in D(X'_proet,A), so no smallness, flatness, or adjunction hypothesis is being silently introduced. There are no node proof-step citations in a Mathlib leaf; therefore citations.json is deliberately empty. The definition nodes remain statement dependencies, and the Mathlib declaration and both relevant source lines are recorded in mathlib_match.

I also opened `lem-pur-diagonal-base-change`, `thm-pur-diagonal-dualizing-object`, `thm-pur-cohomological-smoothness`, and `def-exchange-projection` to audit the imported paragraph. The first and last do not state the coherence claims that paragraph took from them. Rather than rephrase those unjustified claims, I removed the unnecessary argument and retained the actual defined exchange. The distinction from the compact-support right-adjoint mate is explicit in the exchange definition and is preserved here.

Against delivery-errors B–E: no new statement-only node, duplicate, clause-node, or hidden general-category lemma has been introduced; every recorded search actually ran with msearch.py and LeanSearch is recorded unavailable. The successful grep giving Iso.lean:67 was read together with the defining inverse axiom, and the earlier single-file grep parser issue is disclosed in its result record. The item is self-contained relative to its definition dependencies, the coefficient category has not changed, and there is no appeal to a theorem's proof or a notion's definition for a non-elementary assertion. The statement corrections are declared above with explicit missing-domain examples. Elementary inverse cancellation is the whole one-line Mathlib specialization, not a moved geometric clause.

I tested the identity with d=0, K=0, v an identity, f an identity, and with empty schemes: it remains the inverse identity in each case and never cancels a zero morphism unless it is the identity on a zero object. For an arbitrary v and d>0 the same typed identity applies; no assumption on v is used. The doubled-origin and infinite-disjoint-union examples verify why the imported domain needed repair. No new mathematical statement needs further small-case testing.

The first dry run reported one metadata error: preflight requires proof_origin even for a Mathlib leaf. I supplied agent origin metadata referencing the imported blueprint location and the explicit Mathlib specialization, with the absent Markdown disclosure intact; proof steps remain empty as required for a leaf.


## Earlier second reading (a previous round; superseded)

- Item statement: compared every corner, arrow and commutativity clause with the imported node at blueprint order 2018 and the typed composite of `def-pur-smooth-pullback-exchange` at order 2017; PASS. Neither source is a Stacks-tagged lemma. The referenced Markdown files and the Stacks `.tex` directory are absent from this checkout, so this reading uses the preserved DAG statements and the chapter/unit records, not a claimed reading of absent files.
- Domain and coefficients: compared with `def-pur-conventions` (n >= 1, Lambda=A at finite level), `def-pur-smooth-purity-map` (smooth separated, pure d), and `def-weil-exceptional-inverse-image` (finite-type schemes and separated finite-type f); PASS. The explicit restrictions repair the imported typing and match the unit's smooth separated pure-d setting. A k-map between finite-type k-schemes is finite type: on affine pairs a finite set of k-algebra generators also generates over the target algebra, and preimages of affine opens are quasi-compact because the source is Noetherian. No separatedness, smoothness or properness of v is used.
- Statement notions: opened `def-weil-finite-type-morphism`, `def-pc-base-change`, `def-sbc-smooth-morphisms`, `def-weil-proper-morphism`, `def-weil-pbc-proetale-site`, `def-weil-derived-pullback-tensor-hom`, and `def-coefficient-twists-detailed`; PASS. They define the actual finite-type, Cartesian, relative-dimension, separated, pro-etale, pullback and twist notions cited, rather than similarly named alternatives.
- Specialization, unfolding step: against the complete statement of `def-pur-smooth-pullback-exchange`, the right arrow is e.inv followed by b followed by c, with e=Lu*gamma:P isomorphic to Q, b:P to P', c:P' to Q'; PASS. This uses its stated definition, not any argument hidden in a proof. All four objects live in D(X'_proet,A), and b is the very same left identification appearing in the item's square.
- Specialization, cancellation step: against Mathlib `CategoryTheory.Iso.hom_inv_id` at `Mathlib/CategoryTheory/Iso.lean:59`, its reassoc generation at line 67, and the full types returned independently by LeanFinder and Loogle; PASS. Substituting h=b followed by c in `Iso.hom_inv_id_assoc e h` proves e.hom followed by (e.inv followed by (b followed by c)) = b followed by c. The purity definition states gamma as a composite of isomorphisms, so its functorial pullback supplies e. This is the whole elementary calculation; no geometric coherence or comparison theorem is inferred from cancellation.
- Serialized proof steps: none, correctly, because the item is a Mathlib leaf; PASS. `citations.json=[]` remains exact. The preceding two lines audit the unfolding and specialization described in `mathlib_match.how` and in the worker's complete argument.
- Imported discarded step: opened `lem-pur-diagonal-base-change`, `thm-pur-diagonal-dualizing-object`, `thm-pur-cohomological-smoothness`, and `def-exchange-projection`; PASS for its removal. The first gives the projection dualizing-object calculation, not the diagonal comparison claimed there; the last defines exchanges without asserting their composition compatibility. The exchange used here is explicitly defined from purity, and is not identified with the compact-support adjunction mate.
- Source Lean candidate: read `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom`, `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean:453–472`, including all theta/phi arguments and the small-etale category; PASS for not attaching it as an exact pro-etale declaration. Neither its sorry-free local proof nor upstream master sorry declarations establish the missing site/parameter identification.
- New nodes: none; PASS for B1–B7 and D1–D2. No elementary cancellation node or copy of an item's clause has been introduced. Independent DAG keyword/match searches found no duplicate geometric-square node; existing coefficient-reduction coherence concerns different maps. Traversing both statement and proof dependency edges from each of the eleven statement dependencies found no path back to this item.
- Edge cases: checked K=0, f and v identities over Spec k, d=0, d=1, empty source and empty base, and n=1; PASS. The same explicitly typed inverse identity holds, including in the zero category. n=0 is outside the coefficient convention, rather than silently included. The doubled-origin affine line is a smooth finite-type dimension-one counterexample to omitted separatedness; an infinite disjoint union of points is a smooth dimension-zero counterexample to omitted finite type. These support the worker's declared STATEMENT-DISPUTED typing repair.
- Unit and chapter: compared `dag/units/sk-thm-smooth-purity.json` and `dag/chapters/sec-smooth-purity.json`; PASS. This identity for the defined exchange does not replace the diagonal/DNC/vector-bundle construction of the purity maps, which remains below its definition dependencies.

Changes in the second reading: appended three independently executed Mathlib searches with different, general-category phrasing and their actual results; added this hypothesis-by-hypothesis, typed-composite, edge-case and dependency audit. No mathematical statement, match, dependency, or citation needed further repair. All first-worker sections, including `## Review by NR`, are retained.

Delivery-tool note: the prescribed trailing `.` is rejected by this installed script's argument parser, which accepts only group and item plus `--no-push`. I use its documented syntax with the same sandbox selected automatically. An early dry run encountered a temporary-worktree branch collision; its process ended and the tool's cleanup removed that worktree before retry. No launcher or repository tool was edited.

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NR thm-pur-smooth-base-change-coherence --no-push` printed `OK (not pushed) ... at 5abfe6364a: preflight passed`. The package contains zero new nodes and one Mathlib leaf (the existing item).

## Second reading by NR

- Item statement: checked the displayed Cartesian square, all four objects, both purity arrows, the left identification, and the right `Ex^{!,\mathrm{sm}}` arrow against the imported blueprint node (order 2018) and the full definition of `def-pur-smooth-pullback-exchange` (order 2017); PASS. The corrected statement explicitly fixes finite coefficients `\Lambda=A=A_{E,n}`, finite-type `k`-schemes, and `f` smooth, separated, and pure of relative dimension `d\geq0`; these are the domains required by `def-pur-smooth-purity-map` and `def-weil-exceptional-inverse-image`. The arbitrary base-change map `v` has no added hypothesis because none is used.
- Domain and edge cases: checked `d=0`, `K=0`, identity maps, an empty source/base, and `n=1`; the assertion reduces to the same inverse cancellation. `n=0` is excluded by `def-pur-conventions` (`n\geq1`). The doubled-origin line and an infinite disjoint union of points show why omitted separatedness and finite type would leave the imported operators ill-typed; the repaired hypotheses address those failures.
- Statement dependencies: opened each of `def-pur-conventions`, `def-weil-finite-type-morphism`, `def-pc-base-change`, `def-sbc-smooth-morphisms`, `def-weil-proper-morphism`, `def-weil-pbc-proetale-site`, `def-weil-derived-pullback-tensor-hom`, `def-weil-exceptional-inverse-image`, `def-coefficient-twists-detailed`, `def-pur-smooth-purity-map`, and `def-pur-smooth-pullback-exchange`; PASS. Each cited node defines the corresponding finite-coefficient, scheme, square, smoothness/separatedness, site, derived-operation, twist, purity, or exchange notion used by the statement.
- Proof step: the imported geometric paragraph was checked against `lem-pur-diagonal-base-change`, `thm-pur-diagonal-dualizing-object`, `thm-pur-dnc-invariance`, `cor-pur-vector-bundle-purity`, `lem-pur-smb-extraordinary`, `def-exchange-projection`, `lem-pur-coprojection`, and `thm-pur-cohomological-smoothness`; PASS for removing it from the proof because those statements do not supply the claimed composition compatibilities. Unfolding `def-pur-smooth-pullback-exchange` gives `e.hom ≫ (e.inv ≫ (b ≫ c)) = b ≫ c`, with `e=Lu^*\gamma_{f,K}`, and `CategoryTheory.Iso.hom_inv_id_assoc e (b ≫ c)` proves exactly this one step.
- Mathlib leaf: checked `Mathlib/CategoryTheory/Iso.lean` lines 59 and 67, and independently reran the recorded Loogle, LeanFinder, and grep searches in `searches.jsonl`; PASS. The declaration is an exact one-line specialization in the pro-etale derived category, so `citations.json` is correctly empty and no project Lean file is needed. The small-etale upstream candidate was inspected and rejected as an exact attachment because its site and parameters differ.
- New nodes: none. The only candidate helper, inverse cancellation, is already Mathlib and elementary; no duplicate, restatement, clause node, or definition node was created. The report's prior blueprint and duplicate searches were retained and checked.
- Changes made in this second reading: added this required section and three actual independent search records (Loogle, LeanFinder, grep). The corrected statement, proof origin, Mathlib match, empty citations, and prior `## Review by NR` remain unchanged. The original source is a blueprint node, not a Stacks-tagged statement; its referenced Markdown is absent, so I read the full preserved statement and definition in the DAG, plus the chapter/unit records, as explicitly disclosed above.

Second-reader validation: the prescribed delivery script (using its supported two-positional-argument syntax, without the rejected trailing dot) printed `OK (not pushed) deliver/NR/thm-pur-smooth-base-change-coherence at d26a417305: preflight passed`. The initial retries waited on shared infrastructure; no tool or live project was modified to bypass it. This delivery contains zero new nodes and one Mathlib leaf.

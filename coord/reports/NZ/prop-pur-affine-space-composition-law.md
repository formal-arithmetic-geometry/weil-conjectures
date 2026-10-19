# Stage-1 report: prop-pur-affine-space-composition-law

1. Files written: `dag/nodes/sec-smooth-purity/prop-pur-affine-space-composition-law.json` (statement, split; not a Mathlib leaf). No new nodes and no new Mathlib leaves. `citations.json` contains a verbatim statement quote for each citation in each of the eight steps. `searches.jsonl` is the unmodified output log of the prescribed search command.
2. Attachments: none. The nearest Lean file is `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpace.lean`. Lines 270–292 expressly say the canonical affine-line comparison is not constructed, and its existence theorem ends in `sorry`. Lines 356–397 give only existence of an affine-space isomorphism and explicitly disclaim construction of the comparison. Its inductive proof depends on the sorried line result. The sorry-free successor composition helper at lines 297–320 asserts a `Nonempty` isomorphism, not equality of the canonical comparisons and not coordinate invariance. `SixFunctors/Etale/Derived/OrientationDatum.lean` includes composition as an axiom of an orientation datum, rather than proving that the ordered comparison obeys it. No declaration attaches to this item.
3. WANTED: none for this split. The shared repository omits the literature files, but I located and read the same blueprint and Stacks sources in the read-only reference tree `/home/ubuntu/work-bp/sheaf/literature/`. The node's logical source paths remain the standard `literature/...` paths.
4. Errors repaired: the imported one-step proof cited the definition of exceptional inverse image as though its statement proved composition coherence. It also inferred equality of different coordinate towers solely from a positive Koszul sign. Reassociation does not interchange two operations; the new proof separates these arguments. It explicitly calculates the exceptional transpose as a tensor product of the single-coordinate integration maps using the existing relative compact-support Kunneth theorem and its symmetry/projection coherence. The imported permutation also contained the undefined `d'` in `d+d'`; the argument now consistently uses `d+e`.
5. Unfinished work: none in the one-level split. Its existing dependencies retain their own current statuses. No Lean was written, no compiler or Lake tool was run, and no delivery was pushed.

## STATEMENT-DISPUTED: implicit domains need to be bound

The imported display contains the unbound symbol `K` and only an implicit base `Y`. The expression `gamma_{p_e,K}` has declared source only for `K` in the finite-Tor category of `def-pur-affine-space-comparison`; `gamma_{p_d,Rp_e^!K}` additionally needs the exceptional-pullback preservation assertion. I made `Y` a separated finite-type `k`-scheme and bound `K` in `D^b_ctf(Y,A)`, with `Lambda=A`, exactly as in unit `sk-prop-an`, clause (ii), and its Step 6. This is an explicit scoping repair to the intended statement, not a restriction to different coefficients or a weakened conclusion. The formula, comparison, canonical composition morphism and permutation assertion are retained.

There is an unrelated arithmetic trap in the current `def-pur-affine-line-datum` and `lem-pur-finite-kummer-level`: they assume `e(E/Q_l)` divides `n`. That extra hypothesis is absent from this item and is unnecessary for its trace argument. I did not cite those nodes or import that restriction. Step 2 instead uses the already existing locally-free twist theorem, whose clauses (2) and (3) give the roots-of-unity reduction for every stage: choose any integer `r` with `l^r A=0`, and associate tensors to identify `Z_l(1) tensor A` with `mu_{l^r} tensor_(Z/l^r) A`. This works even when `A` is not free over `Z/l^r`, for example ramification index two and `n=1` or `n=3`. The ordinary projective-line interface accepts any finite torsion ring killed by the invertible integer `l^r`.

## Blueprint and route

I read the chapter record `sec-smooth-purity`, the whole `sk-prop-an` unit record (especially clause (ii), Steps 5 and 6), and the source node's Proof Steps 1–4. Whole-DAG and blueprint searches for `affine-space composition`, `composition-law`, `relative product`, and `mate` located the existing interfaces used below. The other imported affine-space compatibility node includes coordinate symmetry but explicitly depends on this item; it was not cited. The affine-space purity corollary also depends on this item and was not cited. I checked the dependency closures of all selected tools and found no return path to this item.

Steps 1–4 realize the source's ordered-tower and reassociation paragraphs. Steps 5–8 supply the actual interchange argument missing between the source's sign computation and its conclusion. This stays within unit Step 6, iterating the normalized affine-line comparisons. `thm-sf-kunneth-relative`, `lem-sf-kunneth-coherence` and `prop-sf-pf-coherence` are declared generic tool uses: they identify compact-support trace interchange with tensor interchange; they do not replace affine-line iteration by general smooth purity. Other off-unit finite-level interfaces are also declared in `split_report.tool_uses`, leaving the maintained `tool_uses` field untouched. No general support Kunneth assertion over a base is used.

## Mathlib audit

All queries were run through `/home/ubuntu/weil-launcher-nt/msearch.py NZ prop-pur-affine-space-composition-law` and copied exactly to the item. LeanFinder's first wording returned affine-space reindexing identities; I read `Mathlib/AlgebraicGeometry/AffineSpace.lean` lines 333–360. They express geometric permutation functoriality, not purity morphisms. The second semantic wording returned smooth-manifold sheaf and distribution lemmas, also unrelated. Loogle returned generic adjunction composition and triangle identities; I read `Mathlib/CategoryTheory/Adjunction/Basic.lean` lines 559–585, including `Adjunction.comp` at 567. Existing DAG nodes already cover these generic tools. The two grep searches found no exceptional purity framework in Mathlib (the one affine-space hit is its functor definition at line 365). LeanSearch returned HTTP Internal Server Error and is recorded as `unavailable`, never as an absence verdict. Thus the item is not a Mathlib leaf.

## Not duplicates

No new nodes were created. In particular no new node restates a clause of the item, an existing trace-invariance theorem, a definition, or a few-line tensor calculation.

## Review by NZ

I read the imported item alongside its original blueprint file and the unit's Step 6, not merely its dependency list. I also opened the full statement of every node used in the final proof; `citations.json` copies those statements verbatim so a second reader can verify each use. The mathematical checks, including the hypotheses that matter, are as follows.

Step 1 uses `thm-sf-ambient-adjoint-class` for its actual Hom bijection on bounded-below etale-origin inputs, and `thm-sf-preservation-class` for its explicit finite-Tor preservation clause. The latter belongs to `sec-six-functors/sk-prop-sf-rf-shriek-preservation`, not the apparent existence-unit path; I read its statement and checked its separated finite-type target hypothesis for every projection. `prop-weil-twist-preserves` states rank-one local freeness and finite-Tor preservation. `lem-sf-proetale-constructible-origin` gives etale representatives; `thm-weil-pbc-site-comparison` gives full faithfulness on bounded-below categories, not an equivalence on all unbounded objects. `lem-sf-class-compact-support-comparison` states exactly the comparison of the two compact-support functors for a common compactification. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is genuinely about ringed topoi, so it applies to the comparison morphism as well as to scheme morphisms. Its source is Stacks 07A4 (`lemma-pullback-tensor-product`), whose statement and proof I read at lines 3683–3724 of the reference `sites-cohomology.tex`. These are the interfaces used for the finite-level transport; no coefficient-category identification is silently assumed.

Step 2 uses the formulas defining the twist and clauses (2)–(3) of `lem-pur-twist-sheaf-locally-free`, not the narrower finite-Kummer-level lemma. In particular the quoted locally-free statement explicitly supplies `Z_l(1) tensor Z/l^r = mu_{l^r}`. The remaining equality is tensor associativity and quotient scalar extension; I wrote it out as an elementary step. This verifies the hypothesis of the ordinary torsion trace at ramified stages without requiring flatness over the chosen annihilator ring.

Step 3 uses the actual pasted-counit formula in `def-weil-pbc-composite-adjunction`, the associativity and identity sentences of `thm-sf-comp-composition`, and clauses (2) and (4) of `lem-weil-pbc-mate-pasting`. I read Stacks 0DV0 (`lemma-compose-counits`) and 0B65 (`lemma-transformation-between-functors-and-adjoints`) in `categories.tex` at lines 3542–3620, and checked the existing Mathlib mate node states pasting, not merely uniqueness of adjoints. The isomorphism direction is correct: the direct-image composition is `Rg_! Rf_! -> R(gf)_!`, whereas the displayed right-hand composite uses `c^{-1}` after the two purity maps. `lem-weil-pbc-proetale-derived-pullback-composition` states the pullback-composition map for constant coefficient ringed pro-etale topoi; I checked Stacks 0D6D's source location. Twist reassociation uses the actual positive tensor powers in `def-coefficient-twists-detailed`.

Step 4 is an induction, with both base and induction step written down. It uses `def-pur-affine-space-comparison` for the ordered recursion, `def-pur-affine-line-purity-comparison` for the projection-formula transpose, and `lem-weil-finite-compact-projection-formula` for its natural transformation on the precise finite-Tor domain. I read those two definitions' complete blueprint texts and the projection-formula node statement. The comparison's naturality is derived by transposing its defining natural composite; no existence-only Lean isomorphism is substituted. The coherence facts used in the induction are exactly those established in Step 3 and cited again. The only conclusion of this step is regrouping a fixed ordering.

Step 5 uses `lem-asd-ordinary-finite-p1-adjunction` because its statement specifies the actual projective trace and counit and says this normalization commutes with base change for every finite ring killed by an invertible integer. It is stronger and more precise than a bare existence-of-adjunction assertion. I read that node, the original `thm-amb-p1-adjunction` source, and `def-amb-p1-trace`. `lem-weil-pbc-etale-shriek-base-change-modules` is the module form of Stacks 03S6 (`lemma-shriek-base-change`), read at lines 11493–11513 of `etale-cohomology.tex`; it states the needed open-extension map and its naturality. `thm-cbc-finite-torsion` explicitly states naturality and pasting of the compact-support exchange for bounded-below etale complexes. The argument applies it to the displayed compactification map defining integration, yielding a written equality between the two traces, rather than merely asserting transport compatibility.

Step 6 uses the composite counit and mate clauses already checked, plus the definition of the line comparison. Its calculation retains `Rp_f! F_f(gamma_g)` until naturality of the transposed line map is applied. This checks the order and the object of every map; there is no interchange of an exceptional pullback with a Tate twist asserted without justification. `prop-sf-pf-coherence` explicitly states the composition pentagon and naturality required to collect the coefficient `K`. I read its full source `sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.md`, including the tensor/counit explanation. The finite projection formula gives the isomorphisms, and the coherence theorem identifies their canonical composites. The integrations `I_m` are local notation inside the proof, not hidden new nodes or extra assumptions.

Step 7 uses the exact four-map definition of `thm-sf-kunneth-relative` and the triple-product and projection clauses of `lem-sf-kunneth-coherence`. I read both full blueprint files in `sec-six-functors/sk-thm-sf-kunneth-relative`. The former's source explicitly decomposes its map into composition, inverse projection, and inverse compact-support exchange, so its statement says exactly what the induction needs. I verified its base is separated finite type and all factor objects are shifted rank-one local systems. `def-sf-datum` expressly allows using only named axioms; the step names A2–A4 and cites their finite-level concrete theorems, avoiding any use of the datum's duality axiom A6. The recursive formula for `I_m` is obtained by inserting Step 5's actual base-changed trace into those maps; this is the missing relation between a coordinate tower and a tensor product.

Step 8 uses the symmetry sentence of `lem-sf-kunneth-coherence`, not the symmetry of a different tensor object. `def-kun-derived-tensor` explicitly includes the signed interchange `(-1)^{ij}`, so the sign calculation for degree `-2` is from a cited definition. `prop-weil-twist-preserves` supplies a local generator of the rank-one line, and the step writes what the interchange does to that generator. Naturality of tensor maps then gives `(t tensor t) sigma = sigma (t tensor t)`, with the right symmetry at the tensor unit. The projection compatibility transports this equality to arbitrary `K`, and the actual exceptional Hom bijection reflects it. This corrects the imported proof's unjustified inference that an even sign by itself commutes two exceptional comparisons.

For small cases I checked `d=e=1` against the two-factor formula `(t tensor t) kappa_2`; its exchanged version agrees by the displayed tensor-naturality square. The induction also has an identity-stage base and works with an empty block although the requested statement only asks positive dimensions. It works for `K=0`, disconnected bases, and the empty scheme because every formula is functorial and no connectedness or global generator is assumed. The rank-one sign check is local and therefore includes nontrivial Tate local systems. The ramified `n=1` and `n=3` tests above detect the narrower-Kummer-datum pitfall. I checked all final dependency closures for a cycle to this item, and excluded the later affine-space purity/compatibility nodes that would have supplied a circular shortcut. No new statement needs a separate small-case audit, since no new nodes were introduced.

I checked delivery-errors B through E against the final files: all objects are scoped, sources and blueprint places are explicit, the only unavailable search is honestly marked, every non-elementary assertion is in a cited statement, coherence and signs are separate calculations, no proof content is moved into a new node, and no additional finite-stage hypothesis is smuggled in. The first dry run rejected the phrase `the item's comparison` in Step 2 as non-self-contained (B2). I replaced it with the actual named affine-line comparison and its citation. I also spelled out why the etale representative has finite Tor amplitude, using the exact fully faithful monoidal comparison already cited in Step 1. Validation is the prescribed `deliver.py NZ prop-pur-affine-space-composition-law --no-push` dry run; READY is issued only after it prints OK. The sandbox is left for a fresh second reader, who will repair and deliver it.
## Earlier second reading (a previous round; superseded)

Step 1: checked the explicit separated finite-type hypotheses and finite-Tor transport against `def-pur-conventions`, `thm-sf-preservation-class`, and the cited etale/pro-etale comparison statements; verdict sound.
Step 2: checked the finite-stage twist identification against `def-coefficient-twists-detailed` and clauses (2)--(4) of `lem-pur-twist-sheaf-locally-free`, including ramified stages; verdict sound and elementary.
Step 3: checked the direction and coherence of exceptional-inverse-image composition against `def-weil-pbc-composite-adjunction`, `thm-sf-comp-composition`, and `lem-weil-pbc-mate-pasting`; verdict sound.
Step 4: checked the induction base, induction substitution, naturality, and reassociation against the ordered affine-space and affine-line comparison definitions and the finite projection formula; verdict sound.
Step 5: checked the compactification trace, open extension by zero, and finite-torsion base-change maps against the three cited base-change/adjunction nodes; verdict sound.
Step 6: checked the pasted counit transpose and projection-formula pentagon against the complete statements of the cited mate, projection, and coherence nodes; verdict sound.
Step 7: checked the relative compact-support product, its hypotheses, and its triple-product/projection compatibility against `thm-sf-kunneth-relative`, `lem-sf-kunneth-coherence`, and the named finite-level interfaces; verdict sound.
Step 8: checked the adjacent-transposition calculation, degree signs, tensor naturality, and reflection through the adjunction against `def-kun-derived-tensor`, `prop-weil-twist-preserves`, and the cited symmetry/adjunction statements; verdict sound.
New nodes: none; there were no B1--B7 node statements to audit, and all proof dependencies are existing nodes.

I corrected no mathematical content in this second reading. I confirmed the worker's scoping repair of `Y` and `K`, the separation of regrouping from coordinate permutation, the explicit trace-interchange calculation, the absence of the unrelated ramification-divisibility hypothesis, and the recorded Mathlib search log. The report, citations, and item statement are ready for delivery.


## Returned delivery audit — 2026-10-16

Return inspected: independent stage-2 immutable head `1f60b23baaa3`,
`/home/ubuntu/weil-launcher-nt/reviews-stage2/NZ__prop-pur-affine-space-composition-law__1f60b23baaa3/review.md`.
The reviewer correctly observes that the submitted artifact is a stage-1 split,
with no Lean module, no `lean` record and no compiler evidence. Those omissions
match the assigned stage; they are not repaired by renaming this report.

H1 asks for a complete stage-2 Lean statement and its node record. This dispatch
explicitly assigns stage 1, gives only the stage-1 sandbox, and repeats the human
instruction never to write Lean or run a compiler. No Lean file or fabricated
record was added. H8 asks for stage-2 documentation and a Worker report tied to
that Lean statement; no such documentation can truthfully certify an absent
module. H10 asks for scompile evidence; none was fabricated or run in violation
of the explicit prohibition. All three points therefore remain unresolved.

I read GOAL.md, coord/dag-sync.md, coord/brief-stage1.md, delivery-errors B--E
and H, and the returned immutable review. coord/STATE.md contains a later
stage-2 pilot authorization, but the current direct worker brief expressly
restricts this worker to stage 1; the pilot paragraph also names NA, not NZ.
The generic stage-2 brief does not override the direct worker restriction.

Tool mismatch: the prescribed `/home/ubuntu/weil-launcher-nt/deliver.py`
reads this stage-1 sandbox, packages only DAG files and the report, preserves
maintainer-owned `lean` fields, and calls preflight without `--stage 2`.
`deliver2.py` instead reads `weil-newtargets-stage2-sandbox` and requires a Lean
record, module/docstrings and `## Worker report`. Thus passing the instructed
stage-1 dry run cannot establish repair of the stage-2 return. The dispatched
repair needs to be routed to a stage-2 worker with explicit Lean and scompile
authorization. The existing node split and recorded searches were preserved.
No push was performed.

Authorized validation: `deliver.py NZ prop-pur-affine-space-composition-law --no-push` exited 0 and printed `OK (not pushed) deliver/NZ/prop-pur-affine-space-composition-law at 0891b33fa5: preflight passed`. A read-only check of all eight proof steps and 40 citation entries found every quote in the current shared node statements. This is stage-1 validation only; H1/H8/H10 remain unresolved because they require the prohibited stage-2 work. Final status: BLOCKED by stage-mismatched repair dispatch, not READY for stage 2.


## Earlier second reading (a previous round; superseded)

This is a fresh stage-1 reading under the present dispatch. The earlier stage-2 return audit above records a different requested artifact; it does not override the current explicit instruction to review and deliver this stage-1 split. I read delivery-errors B--E, GOAL.md and coord/dag-sync.md. I opened the original blueprint proposition, the chapter and sk-prop-an unit (clause (ii), Steps 5--6), every cited node statement, and the reference Stacks sources under `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`.

Statement: checked every domain, the direction of `c`, the two block dimensions and permutation clause against the source proposition and unit clause (ii); verdict faithful after the worker's explicitly reported binding of Y and K. The scalar stage remains every A_E,n, including ramified stages; no new restriction is needed.

Step 1: checked the Hom domains, finite-Tor preservation, etale-origin equivalence, bounded-below full faithfulness, compact-support comparison and monoidal pullback against all seven cited statements and Stacks 07A4, `lemma-pullback-tensor-product`; verdict sound after clarifying that tensor-vanishing reflection is checked on cohomology sheaves, where exact faithful inverse image applies even if the tensor complex was initially unbounded.
Step 2: checked the quotient tensor calculation against the twist definition and clauses (2)--(3) of the locally-free twist node; verdict elementary and sound, including e(E/Q_l)=2 with n=1 or 3 and annihilator l^r. No flatness over Z/l^r is used.
Step 3: checked counit order and mate direction against Stacks 0DV0, `lemma-compose-counits`, 0B65, `lemma-transformation-between-functors-and-adjoints`, the complete mate-pasting node, Mathlib Mates.lean lines 170--225 and 300--340, and Stacks 0D6D, `lemma-derived-pullback-composition`; verdict sound after writing the identity-mate calculation explicitly.
Step 4: checked the induction base and substituted induction hypothesis against both comparison definitions, the natural finite projection formula and the coherent composition statements; verdict sound. Only associativity is used here, with no inference of permutation invariance from reassociation.
Step 5: checked the actual normalized projective trace and its Noetherian-base-change hypothesis against lem-asd-ordinary-finite-p1-adjunction; checked open-extension module base change against Stacks 03S6, `lemma-shriek-base-change`, and the exchange direction and pasting against thm-cbc-finite-torsion; verdict sound after defining the twist on P^1 before applying Rq_* and restricting the auxiliary base changes to the Noetherian schemes used by this item.
Step 6: checked every domain in the displayed pasted-counit calculation against the composite-adjunction and mate statements, and checked collection of K against the finite projection formula and prop-sf-pf-coherence's composition pentagon and naturality; verdict sound. The compact-support composition identifications are the canonical ones of Step 3. No commutation of an exceptional pullback with an arbitrary coefficient is presumed.
Step 7: checked the precise binary product against thm-sf-kunneth-relative and its symmetry/triple-product/projection clauses against lem-sf-kunneth-coherence, reading their full blueprint sources; verdict repaired. The second projection formula requires V_m=Rp_m!T_m itself to be finite Tor. The existing lem-amb-affine-space-top-trace at d=1 supplies U isomorphic to A_Y; induction using the binary product then gives V_(m+1) isomorphic to V_m tensor U and verifies this previously omitted hypothesis at every stage. Only the one-dimensional object isomorphism is used; equality of the particular integration maps is still proved by the pasted-trace calculation. No axiom A6 or all-dimensions purity theorem is assumed.
Step 8: checked the adjacent-transposition tensor-naturality square, degree -2 sign, rank-one local generator and injectivity of the exceptional Hom bijection against the four cited statements; verdict sound after making the block-generator calculation explicit. The coherence clause cited is the relative compact-support product's symmetry, not a supported product over a general base.
New nodes: none; B1--B7 create no separate obligations. The added dependency lem-amb-affine-space-top-trace already exists in this same unit; its source Proof paragraph d=1 gives the object isomorphism used, and its dependency closure has no path to this item. I did not modify it or attach any existence-only Lean isomorphism to the item.

Small cases: d=e=1 gives (t tensor t) followed by the binary product and is invariant by its naturality square; d=0 or e=0 reduces the tower to the identity comparison, although the stated range is positive; K=0 and Y empty give unique zero maps; Y=Spec(k) and disconnected Y satisfy the same functorial formulas. The local twist calculation does not require a global generator. The new finite-Tor induction starts with U of amplitude [0,0] and therefore covers non-field finite coefficient rings.

Changes made: (1) supplied the missing intermediate finite-Tor check in Step 7 using one existing same-unit node and added its verbatim citation; (2) typed the compactification map in Step 5 with a sheaf on P^1 and scoped its base-change schemes; (3) made the cohomology-sheaf reflection, identity mates and block-generator calculations explicit in Steps 1, 3 and 8. The statement and remaining proof steps were preserved. There is no replacement of the unit route, no new node restating a clause, and no new Mathlib leaf.

Independent Mathlib searches ran through msearch.py with different wording: grep `trace.*(permut|symmetr)|integrat.*(commut|tensor)|purity.*comp`, LeanFinder `Integration along a product of affine lines is independent of the order of integrating the coordinates`, and Loogle `CategoryTheory.conjugateEquiv, "comp"`. The grep and semantic hits concern matrix/operator traces and analytic integrals. Loogle finds generic mate/conjugate composition and module pullback identities; their types and Mates.lean confirm the existing generic mate node, without stating the affine-space purity comparison. The actual search records were appended by the tool and their results recorded on the item. No Lean file was written and no compiler, Lake or build tool was run.

Validation of this second reading: all 41 citations were checked verbatim against the current shared statements, and `deliver.py NZ prop-pur-affine-space-composition-law --no-push` exited 0 with `OK (not pushed) deliver/NZ/prop-pur-affine-space-composition-law at 8d165b18f2: preflight passed`. The stage-1 delivery is now submitted by the prescribed delivery tool.

## Repair of returned citation drift — 2026-10-16

The return has one point: the landing detected a changed statement for `lem-amb-affine-space-top-trace` and asked for a rebase and revalidation. The prescribed delivery tool rebuilds this item on the current `origin/newtargets-dag`; no manual git command was run. I reread the expanded current trace statement, its ordinary-etale convention and explicit counit, and its source in `sk-prop-an/lem-amb-affine-space-top-trace.md` (especially the one-dimensional paragraph). Its conclusion still supplies precisely the object isomorphism required to start Step 7, rather than the coordinate-invariance conclusion we are proving.

I changed Step 7 to instantiate that statement with `S=Y`, `d=1`, and `N=ell^r` from Step 2. The finite ring A is commutative and is killed by N; N is invertible because Y is over k of characteristic p different from ell. Its twist is exactly `mu_N tensor_(Z/N) A`, identified with the finite-level twist in Step 2. Its bounded-below comparison applies to the shifted rank-one sheaf T. The conclusion is therefore `U=Ra_!T` isomorphic to `A_Y`, so U has Tor amplitude [0,0]. Only dimension one is used. The iterative product proof still proves the equality of the integration maps itself, without relying on any higher-dimensional counit normalization or permutation assertion from the cited node.

The new statement makes the Noetherian-base hypothesis explicit. To justify it with a named statement instead of an uncited fact, Step 1 now cites the existing `lem-weil-pbc-finite-type-over-noetherian`. I read its whole statement and Stacks Tag 01T6, `morphisms.tex`, `lemma-finite-type-noetherian`: a finite-type scheme over a Noetherian base is Noetherian. A field has just its zero and unit ideals, so Spec(k) is Noetherian; all schemes in the finite-type coordinate towers thus meet the trace and projective-line interfaces' hypotheses. This is a generic tool use, declared in `split_report.tool_uses`, and creates no node.

The first correctly invoked dry run identified another changed statement, `prop-weil-twist-preserves`, in Steps 1 and 8. I reread its entire current statement. Its finite-coefficient clause explicitly gives invertible locally constant rank-one A-twists; its final paragraph preserves bounded constructibility, finite Tor amplitude and the exact amplitude interval. Those are exactly the facts used in Step 1 and the local-generator argument of Step 8. The changes at integral and rational coefficients are irrelevant here because the item fixes A=A_(E,n). I replaced both stale quotes by the current statement. I also replaced the old top-trace quote by its current passage defining the counit's source and asserting its isomorphism, and added the verbatim citation for the Noetherianity tool.

## Review by NZ

For this repair I reread the item and unit `sk-prop-an` (clause (ii), Step 6), the current statements of all cited dependencies, the two changed dependency statements discussed above, and the source of the added Noetherianity citation. Steps 1 and 8 still use only the finite-coefficient clauses of twist preservation. Step 7's use of the expanded top-trace statement is now fully instantiated, including every base, coefficient, twist and boundedness hypothesis. Steps 2 through 6 continue to use the finite twist reduction, composite-adjunction and mate-pasting formulas, ordinary-etale compact-support exchange, and the natural projection formula; their quotes remain verbatim. The relative product and its symmetry/coherence in Steps 7 and 8 still concern compact supports, not the invalid relative supports formula excluded in the unit. The temporary objects U, V_m and maps I_m are introduced in the proof; no hidden construction from a dependency's proof is used.

I checked B--E again with these changes: there are no new nodes or fresh search claims, no new definition, no moved clause of the item, and no change to its statement or route. The dependency added to Step 1 states exactly the non-elementary Noetherianity fact required. The special case d=e=1 remains the symmetric two-factor trace formula, while K=0 or an empty base gives the unique map. Ramified finite stages require only an annihilating power ell^r, not divisibility of n by the ramification index, and so still satisfy the changed trace statement. All 42 citation entries match the current shared statements. No Lean file, compiler, Lake invocation, build, or push is part of this repair; the final acceptance is the mandated stage-1 dry run below. This repair supersedes the obsolete stage-2 routing discussion earlier in the report.

Repair validation: the rebased dry run printed `OK (not pushed) deliver/NZ/prop-pur-affine-space-composition-law at 3410ac0365: preflight passed`. A final dry run includes this updated repair report and the unchanged validated node and citations; its stdout is retained in `repair-dry-run.log`. The sandbox is left for the required fresh second reader, with zero new nodes and zero Mathlib leaves.


## Earlier second reading (a previous round; superseded)

This is an independent stage-1 reading of the repaired split. I read delivery-errors B--E, GOAL.md, coord/dag-sync.md, the chapter and unit sources, the original proposition, and the full current statements of all cited nodes. The blueprint and Stacks files were read in the existing read-only reference tree `/home/ubuntu/work-bp/sheaf/literature/`; their standard logical source paths remain unchanged.

Statement: compared every hypothesis, the direction of c, both block dimensions, the displayed equality and coordinate-permutation conclusion with the original proposition and sk-prop-an clause (ii), Step 6; faithful, including the explicitly documented binding of Y and K.
Step 1: checked all eight cited statements, especially the separated finite-type target in thm-sf-preservation-class, D+ full faithfulness in thm-weil-pbc-site-comparison, and Noetherianity in Stacks 01T6, lemma-finite-type-noetherian; sound, with finite-Tor reflection checked on cohomology sheaves rather than an unbounded Hom comparison.
Step 2: checked the definitions and clauses (2)--(3) of lem-pur-twist-sheaf-locally-free; the displayed quotient scalar-extension calculation is elementary and valid without flatness of A over Z/ell^r, including ramified n=1 and n=3.
Step 3: checked the composite counit against Stacks 0DV0, lemma-compose-counits, conjugation against 0B65, lemma-transformation-between-functors-and-adjoints, and pasting/identity against the complete mate node and Mathlib Mates.lean lines 160--230 and 300--340; the direction and coherence of c are correct.
Step 4: checked both comparison definitions, the natural finite projection map and Step 3; the one-line base and substituted induction step prove regrouping of the ordered tower, with no permutation inferred from reassociation.
Step 5: checked the precise normalized counit and its Noetherian base-change hypothesis against lem-asd-ordinary-finite-p1-adjunction, and open extension against Stacks 03S6, lemma-shriek-base-change, together with the natural/pasting statement of thm-cbc-finite-torsion; the displayed map is correctly typed using bar T on P^1, and the base-changed trace is the same actual map.
Step 6: checked all domains in the pasted transpose against the composite-adjunction/mate statements and the naturality/composition pentagon in prop-sf-pf-coherence; the written naturality calculation yields tau_g composed with Rg_!(tau_f), and collecting K leaves precisely I_m.
Step 7: checked the binary product definition, the symmetry/triple/projection clauses and the full current top-trace statement; S=Y, d=1 and N=ell^r satisfy all hypotheses, and U isomorphic to A starts the finite-Tor induction for V_m before the second projection formula is applied. Only the existing one-dimensional object isomorphism is used; equality of integration maps is proved by the preceding counit and base-change calculations.
Step 8: checked the relative compact-support symmetry against lem-sf-kunneth-coherence, the signed complex symmetry against def-kun-derived-tensor and rank-one local freeness against the finite clause of prop-weil-twist-preserves; the displayed tensor-naturality square, local block-generator calculation and injective exceptional Hom bijection establish coordinate invariance without permuting K past a shifted factor.
New nodes: none; no elementary, duplicate, Mathlib, or restated-clause node requires removal, and there are no new B1--B7 statement obligations.

Small cases: for d=e=1 the trace is (t tensor t) composed with the binary product and is fixed by its symmetry square; the zero-coordinate extension uses the identity comparison. For K=0 or an empty Y all displayed maps are the unique zero maps. For Y=Spec(k) the same formulas apply, and the local generator argument also works on disconnected bases. The finite coefficient ring need not be a field; the amplitude induction uses U isomorphic to A, not regularity of A. I checked the statement/proof dependency closure of each of the 26 proof dependencies and found no return path to this item.

Independent Mathlib searches: grep `conjugateEquiv.*(comp|id)|mateEquiv.*comp|trace.*affine` returned 25 generic adjunction/pullback hits; the relevant declarations in Mates.lean were read and are already represented by the cited mate node. Loogle `CategoryTheory.Adjunction.conjugateEquiv, "comp"` rejected the identifier as unknown, so that attempt is not evidence of absence. Loogle `CategoryTheory.mateEquiv, "id"` returned zero hits. These actual outputs remain in searches.jsonl; the valid queries and their results are recorded in mathlib_searches. No new Mathlib leaf was justified. The inspected source Lean file still states existence-only isomorphisms and explicitly says the canonical comparison is not constructed; its line-purity theorem contains sorry, so it cannot close this item.

Changes made: expanded Step 7's top-trace citation from a conclusion-only excerpt to the complete current statement, so its coefficient, Noetherian, twist and adjunction hypotheses are visible in citations.json; recorded the independent search results; appended this second reading while preserving all earlier worker/review sections. The mathematical statement and all eight proof steps needed no further change. All 42 citation quotes were verified verbatim against the current shared node statements. No Lean file was written or compiler/build tool run. Required dry-run and delivery results follow below.

Second-reading validation: `deliver.py NZ prop-pur-affine-space-composition-law --no-push` exited 0 and printed `OK (not pushed) deliver/NZ/prop-pur-affine-space-composition-law at 8206271d74: preflight passed`; stdout is retained in `second-reader-dry-run.log`. The prescribed stage-1 delivery is now run with this report included.


## Repair of landing-lock return — 2026-10-16

The return names this delivery at head `8813e63635` and reports that landing
waited 120 seconds for `coord/.merge.lock`. The lock holder is explicitly
`merge_delivery.py NW lem-pur-affine-punctured-line-algebra`; the following
PID contraction, affine evaluation, Picard/cokernel, two-Mathlib-leaf and
missing-new-node-metadata text belongs to that NW command. I inspected the
entire NZ sandbox: it contains just the imported proposition, eight proof
steps, zero new nodes and zero new Mathlib leaves. Its `lean_audit` already
contains both branch records. There are therefore no NZ new-node
`created.by/date` or `lean_audit` omissions to repair. Adding `created` to
this imported item would misclassify it; editing NW's files is outside this
item. This is a lock/rebase return for NZ, not a request to fabricate two
new nodes. No lock or live file was modified.

I reread every current cited statement rather than assuming the old accepted
head still applies. All 42 per-step quotes remain verbatim, including the
expanded `lem-amb-affine-space-top-trace`, the finite-level clauses of
`prop-weil-twist-preserves`, and `lem-weil-pbc-finite-type-over-noetherian`.
There is no detected citation drift in this sandbox. The required delivery
tool reconstructs the delivery on the current fetched DAG in its own
worktree; no manual git command is used. I strengthened Step 7's domain
argument by writing the object induction `V_1=U ≅ A_Y` and
`V_(m+1) ≅ V_m tensor U ≅ A_Y`, with amplitude `[0,0]` at each stage.
This records explicitly why the second projection formula is permitted
before making any assertion about the ordered integration maps.

## Review by NZ

For this lock-return repair I read the chapter record, unit `sk-prop-an`
(clause (ii) and Step 6), the complete original proposition's four source
steps, and the current statements of all statement and proof dependencies.
The read-only literature copy remains `/home/ubuntu/work-bp/sheaf/literature/`.
I reread Stacks 0DV0 (`lemma-compose-counits`) and 0B65
(`lemma-transformation-between-functors-and-adjoints`) in `categories.tex`,
03S6 (`lemma-shriek-base-change`) in `etale-cohomology.tex`, and 01T6
(`lemma-finite-type-noetherian`) in `morphisms.tex`. I also read the full
relative-product, relative-product-coherence, projection-coherence and
affine-space-top-trace blueprint source files. No new source or new node is
needed by the added elementary tensor-unit induction.

Step 1 still uses the actual bounded-below exceptional Hom bijection,
finite-Tor preservation, etale-origin equivalence, fully faithful site
comparison, compact-support comparison, monoidal pullback and finite-type
Noetherianity statements. Each source and base in the tower is separated
finite type over k; no unbounded pro-etale adjunction is assumed.
Step 2 uses precisely the locally-free twist reduction clauses and the
coefficient twist definition; quotient tensor associativity does not
require A to be flat over Z/ell^r. Step 3 uses the pasted counit, mate
pasting/identity and associative direct-image comparison statements, with
c inverse in the direction needed by the display. Step 4 uses the ordered
comparison definition and the natural affine-line projection-formula
transpose; its induction regroups the same ordering and does not infer
coordinate symmetry from reassociation.

Step 5 uses the normalized projective-line counit and its base-change
clause, open-extension module base change, and natural compact-support
exchange. The annihilator N=ell^r is invertible on every Noetherian base
involved; bar T lives on P^1, so the compactification map has the stated
source. Step 6 uses the composite counit and mate formulas and the
projection-formula composition pentagon; the naturality calculation
collects K and leaves the same map evaluated at A, namely I_m. Step 7 uses
the *defined* four-map relative compact-support product and its triple and
projection coherence, with concrete finite-level A2--A4 inputs. The
one-dimensional top-trace statement gives only the object isomorphism
needed to start its domain induction. The added formula now makes every
V_m's finite-Tor hypothesis explicit without assuming equality of I_m
with a pre-existing higher-dimensional trace. Step 8 uses relative-product
symmetry, the signed cochain tensor definition, rank-one local freeness,
and the injective natural exceptional Hom correspondence. The tensor
naturality square and local generator computation establish invariance;
no unsupported inference from a positive sign alone is used.

I rechecked B--E: no new node or restated clause, no unsupported new search
claim, no borrowed proof-only construction, and no source/route or statement
change. The new Step 7 sentence is a few-line deduction from its already
cited product and trace statements. For d=e=1 it gives the same two-factor
trace symmetry; for K=0 or empty Y the comparisons are unique zero maps.
The argument is local for rank-one twists, hence does not require a global
generator or connected base. Non-field A and ramified n=1 or n=3 are
allowed: the domain induction uses A as a module over itself, and only an
annihilating power ell^r is required. A fresh source search still finds
only existence-level affine-space Lean isomorphisms and the sorried
canonical line result, not the canonical-comparison equality, so there
is no attachment. The statement and unit route are preserved. Only sandbox
files are written; no Lean, compiler, Lake, build or push is used. A fresh
second reader retains responsibility for delivery after this dry run.

## Second reading by NZ

Statement: compared the item against the source proposition in `sketch/35_smooth_purity.tex` (the Affine-space composition law) and the blueprint node at order 1977; the scoped finite-coefficient, separated finite-type base and bounded finite-Tor input are the declared repaired setting, and the displayed composite, composition isomorphism, even Koszul sign, and two block orderings agree hypothesis by hypothesis. I removed the imported extra sentence claiming invariance under every permutation, because that stronger conclusion belongs to the later corollary and is absent from this proposition.
Step 1: checked the separated finite-type projection hypotheses, Noetherianity, bounded-below adjunction, finite-Tor preservation, etale-origin transport, site comparison, compact-support comparison, and tensor pullback against the eight cited node statements; verdict sound, with finite-Tor reflection explicitly restricted to cohomology sheaves.
Step 2: checked the annihilating power, locally free torsion twist clauses, tensor calculation, pullback compatibility, and affine-line comparison domain against `def-coefficient-twists-detailed`, `lem-pur-twist-sheaf-locally-free`, and `def-pur-affine-line-purity-comparison`; verdict elementary and sound, including ramified stages without an extra divisibility hypothesis.
Step 3: checked the composite counit, mate direction, associativity and identity laws, pullback composition, and twist reassociation against the five cited statements; verdict sound.
Step 4: checked the induction base, substituted induction step, projection-formula naturality, reassociated exceptional inverse-image maps, and ordered affine-line definition against all five cited statements; verdict sound and separate from coordinate interchange.
Step 5: checked the projective-line compactification map, normalized counit base change, open-extension base change, compact-support exchange, and Noetherian hypotheses against the four cited statements; verdict sound.
Step 6: checked every transpose domain, the composite counit calculation, projection-formula pentagon, and the definition of the temporary integration maps against the six cited statements; verdict sound.
Step 7: checked the relative compact-support product, symmetry/triple/projection coherence, finite-level inputs, one-dimensional top-trace normalization, and the induction proving finite Tor amplitude for every product pushforward against the seven cited statements; verdict sound.
Step 8: checked the adjacent-transposition tensor square, signed derived-tensor symmetry, rank-one twist generator, block sign, and injective exceptional Hom correspondence against the four cited statements; verdict sound for the two block orderings stated by the item.
New nodes: none; therefore B1--B7 impose no new-node statements, source records, or Mathlib-leaf checks. Existing-node searches found the cited affine-space comparison, mate, projection, compact-support product, and trace interfaces; no duplicate node was created.

Changes made: (1) replaced the four stale citation quotes for `lem-pur-twist-sheaf-locally-free` and `thm-sf-comp-composition` with the current shared node statements verbatim, as required by the citation checker; (2) corrected the item statement by removing the stronger all-permutations conclusion and retaining the source proposition's two-block-order conclusion; (3) recorded this source comparison and the absence of new nodes here. Small cases checked were the identity/zero-coordinate extension, $d=e=1$, $K=0$, empty base, $Y=\operatorname{Spec}(k)$, disconnected $Y$, and non-field ramified finite coefficient stages. No Lean, compiler, Lake, or build tool was run.

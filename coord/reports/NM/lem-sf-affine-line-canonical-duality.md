# Worker report: lem-sf-affine-line-canonical-duality

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-affine-line-canonical-duality.json`: split into five steps; statement and statement dependencies unchanged; fresh actual searches appended to inherited search records.
- `dag/nodes/sec-six-functors-basics/lem-sf-affine-base-p1-trace-adjunction.json`: one new statement-only geometric input, unsplit; no Mathlib match. The statement concerns the proper projective line and an adjunction with its projection-formula counit, not the affine-line conclusion.
- `citations.json`: one verbatim statement quotation for each of the twelve step/node citations.
- `searches.jsonl`: the ten actual Mathlib searches for this item and the new projective-line input, retained with their actual results.

## Attachments

None. I searched the project library by the blueprint tag, by affine-line duality and adjunction names, and by projective-line adjunction names. `AlgebraicGeometry.Etale.AffineLineSmoothDuality` in `WeilConjectures/SixFunctors/Etale/Derived/SmoothDuality/AffineSpace.lean:137` is a predicate, not a proof. `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace` in `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpaceAdjunction.lean:50` has proof `sorry`. `AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange` in `WeilConjectures/SixFunctors/Etale/Derived/SmoothDuality/SmoothBaseChange.lean:80` also has proof `sorry`; it does not justify an attachment. The affine-space induction assumes the affine-line input and does not supply it.

## WANTED

None. The current blueprint files used below are present. The arbitrary-affine-base strengthening is explicitly agent-stated, rather than attributed verbatim to a narrower source.

## Problems found and corrected

The imported item has no proof. Its source points to the smooth tensor argument, while the projective-line and affine-space adjunction nodes currently in the DAG are restricted to Noetherian bases. Applying them to the item's arbitrary affine scheme would add a hypothesis. I have not changed the item: instead the new node isolates the missing arbitrary-affine-base projective input, with no extra claims about base-change or normalized Kummer traces. This preserves the unit's projective-line-then-affine-localization route. The new input is not an elementary generalization of its Noetherian counterpart: it still requires geometric diagonal/trace arguments over a general coefficient base, so it joins the queue unsplit.

A second issue is that an abstract identification of the right adjoint with twisted pullback does not alone establish the assertion about the actual theta map. Step 3 explicitly computes its transpose, using precisely the same counit as the new projective adjunction. Step 4 then uses the existing equality of canonical etale restriction maps, not merely endpoint isomorphisms.

The inherited `created.item` chain terminates at the maintainer-created smooth-dualizing node with a null parent. `tools/blueprint_refs.py ancestor` accordingly returns None. The new `from.node` is null, its `via` contains the item and the smooth-dualizing parent, and its place explicitly names unit step 3 and the current blueprint proof paragraphs. No unit record is edited, since this item is not its key node. `coord/dag-sync.md` referenced in the older standing brief is absent in this live read clone; the current direct-delivery brief supplies the repository and synchronization rules used here.

## What remains

The new projective-line adjunction node is deliberately statement-only. Its source route is the supported diagonal class, projective-line cohomology, and the two diagonal integral identities from the current `sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md`. Those produce an adjunction on all coefficient complexes, with a counit given by inverse projection followed by trace. In the arbitrary-base version its eventual split must justify those inputs in that range (rather than assume Noetherianity or obtain purity from the forbidden trace route). The present item does all the further work: it proves the canonical projective tensor comparison from that counit formula, restricts through the affine chart, and identifies the concrete Tate object. No proof of the whole affine-line result is moved into a renamed affine-line node.

## Not duplicates

lem-sf-affine-base-p1-trace-adjunction vs lem-asd-ordinary-finite-p1-adjunction: the existing node requires S Noetherian; the new node permits Spec R for every commutative R with N invertible. The existing node also asserts normalized Kummer decomposition and base-change compatibilities, which the new node does not need.

lem-sf-affine-base-p1-trace-adjunction vs thm-amb-p1-adjunction: the existing projective-line adjunction has a Noetherian base and uses its fixed trace; the new input is over an arbitrary affine base and specifies the counit by an existential derived trace.

lem-sf-affine-base-p1-trace-adjunction vs det-sp-p1-adjunction: the existing node uses Z/ell^n, a Noetherian base, and classical pro-etale categories. The new input uses every finite commutative coefficient ring killed by N and ordinary unbounded etale categories over arbitrary affine bases.

lem-sf-affine-base-p1-trace-adjunction vs det-sp-tower-p1-adjunction: the existing node uses a varying-coefficient tower and bounded-below etale-origin categories. It does not state this ordinary finite-ring adjunction on the entire unbounded category.

lem-sf-affine-base-p1-trace-adjunction vs cor-amb-affine-space-adjunction: the existing node concerns affine space over a Noetherian base, while the new input concerns the proper projective line over an arbitrary affine base, before taking the affine open chart.

lem-sf-affine-base-p1-trace-adjunction vs lem-sf-affine-line-canonical-duality: the new input concerns Rq_* on P1 and a projection-normalized counit. It contains no affine open immersion or affine exceptional comparison. The item's proof still has to identify the canonical tensor map and prove the restriction equation gives the requested result.

lem-sf-affine-base-p1-trace-adjunction vs lem-sf-etale-ambient-adjoint-projection: the existing node supplies an abstract right adjoint and projection isomorphism. It gives no description of that right adjoint as twisted pullback and no trace with the required counit formula.

## Mathlib and blueprint searches

Before creating the projective node I searched the whole DAG for projective-line/affine-line adjunction and trace statements, inspected the relevant statements, searched the entire blueprint via `blueprint_refs.py search` for `affine-line`, `projective-line adjunction`, `projection-normalized` and `Tate`, and searched the project Lean source. No existing statement covers this coefficient category and arbitrary-base range. Both same_as fields are therefore empty.

For each of the item and the new node I ran two different LeanFinder phrasings, Loogle, grep, and LeanSearch through the required msearch.py command. All ten services/commands answered; all returned hits were read. The closest module adjunction hits were checked in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:189-199: they are ordinary structure-sheaf pullback left adjoint to pushforward, and have neither etale coefficients nor the reversed proper duality adjunction. The only grep hit for the new projective search was Mathlib/Dynamics/Ergodic/Conservative.lean:37, the phrase Poincare recurrence, unrelated to duality. The remaining hits are generic adjunction/shift results, K-projective complexes, scheme etaleness or condensed internal projectivity. None specializes to either searched assertion in one line. No Mathlib leaf was created. Historical searches already on the repository item were preserved verbatim.

## Review by NM

I read the chapter record and unit `sk-prop-sf-rf-shriek-preservation` in full, especially its step 3, and the current blueprint `thm-asd-smooth-tensor.proof.md`, `cor-amb-affine-space-adjunction.proof.md`, and `thm-amb-p1-adjunction.proof.md`. I also read the current project Lean affine-space adjunction statement, its sorry body, the affine-line predicate and the smooth-duality induction. The item follows the unit's projective-line adjunction followed by open restriction. No source outside the allowed route is used.

For the new node I read the full diagonal-kernel proof and its containing `sk-prop-geo-p1-adjunction` unit, including (G6) and (G7) and both triangle identities. The statement deliberately records the projective geometric input needed by this item, with its precise right functor B tensor q^* and its precise counit, over the same affine bases as the item. I did not present the source's narrower standing range as an existing proof of the strengthening. The new node is left unsplit, and its source place says explicitly that the arbitrary-base formulation is agent-stated. Its statement introduces all schemes, rings, twists, categories, maps and hypotheses, and contains no proof sketch.

Step 1 uses the existing standard affine chart statement, which says the immersion is over S, and the proper-projective-space statement, which is explicitly valid for every S. I opened both statements. They justify all three open-then-proper factorizations; the ambient-adjunction node then defines exactly the compact-support functors used here. Passing the inverse of N through local ring maps checks invertibility upstairs without a Noetherian assumption.

Step 2 uses the new projective adjunction on this affine S. I opened `det-sp-unique-right-adjoint`: its statement gives a natural, mutually inverse, counit-preserving comparison for two right adjoints of one fixed functor. Thus it gives the particular e used here and the counit equation needed at A_S. The source and target of gamma_q are B and G_q A_S; the inserted right unitor makes them correctly typed.

Step 3 is elementary after those supplied adjunctions. I checked the definition of theta in the ambient node, and substituted the counit equation from step 2 into its transpose. Projection naturality replaces F(gamma_q tensor 1) followed by inverse PF with inverse PF followed by F(gamma_q) tensor 1; this is naturality of the very projection transformation already supplied. The displayed equality has source F(B tensor q^*K) and target K at every stage. The new node's counit formula is literally the final expression, so adjunction injectivity proves equality with e_K. No smooth-duality theorem is assumed here. In particular this is not an illicit use of the proof of a cited node.

Step 4 uses the open-immersion-etale statement and the arbitrary-base etale unit/tensor statement, both of which I opened. The latter explicitly includes open immersions and the chosen factorization (j,id). For separatedness the diagonal of an open monomorphism is the identity, so no finiteness assumption is hidden. I opened the tensor-transitivity node and used exactly its final displayed etale restriction equation with a=j and b=q. It supplies the counit-preserving lambda and identifies the actual pulled-back theta, which makes theta_p invertible. The general composition clause's tensor-invertibility hypothesis is not needed: the last restriction equation directly gives the conclusion.

Step 5 uses the existing finite-twist-pullback statement, read in full, whose assertion includes inverse image of roots of unity, the Z/N action, coefficient extension, and the shifted derived transport. The constructed gamma_p is an isomorphism T[2] to G_p A_S. Tensoring it with the identity preserves invertibility; composing with theta_p is exactly the map in the item. This last argument is elementary and neither assumes constructibility nor replaces the prescribed map by an unrelated one.

I checked B1-B10, C1-C8, D1-D5, and E1-E7 against the files and cited statements: the new input has no proof or proof dependencies, every non-elementary input has a node, no existing node is cited for a stronger statement than it says, all maps have their required source and target, and the route is not replaced by smooth purity. The new node is projective rather than a restatement of either affine clause. Each proof step has fewer than 1000 characters, so there is no long inline lemma hidden in a step. Small cases checked: S empty, A the zero ring, N=1 (forcing A=0), a finite field base with N prime to its characteristic, a nonreduced affine base, and a genuinely non-Noetherian affine base Spec(F_l[x_1,x_2,...]) with N prime to l. The chosen factorization and the new project's hypotheses make sense in each; no argument invokes an affine chart being Noetherian. For nonzero coefficients over a separably closed field, the shifts give B=A(1)[2] and dualizing cohomology in degree -2, as required, rather than the opposite shift.

The off-unit generic tools (uniqueness, projective chart/properness, open immersion etaleness, and concrete finite-twist pullback) are listed in split_report.tool_uses with their roles. They implement the unit's stated route; none substitutes another proof of smooth duality. Verbatim quotes were checked against the actual cited statement strings before writing citations.json.

## Validation

The required server dry run completed successfully: `OK (not pushed)` at `c9601d7560c`, with preflight passed. No Lean code or compiler/build command was run. After correcting the report-only declaration line reference from 52 to 50, the final dry run is repeated before direct delivery.

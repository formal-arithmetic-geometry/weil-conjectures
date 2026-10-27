

## lem-weil-finite-compact-projection-formula (2026-10-15 23:51 UTC, branch head 77721ecfa9)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-finite-compact-projection-formula: coord/.merge.lock held for 120 s by pid 3467334: /usr/bin/python3 tools/merge_delivery.py Q37 cor-pur-smooth-admissibility --stage 1 --reviewer NT-Codex-Q37-94d928c3b --head 94d928c3b817abe3f65d75f31f81ab670bb83b77 --spot-checked Read the item, all cited statements, sources and unit/chapter route; checked all eight steps, edge cases, duplicates and dependency cycles. Mathematics accepted. Corrected only proof_origin.by from document to agent, as required for blueprint-based proofs. Whole corrected JSON and detailed review.md written; all 1 Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-constant-coefficient-objects-constructible (2026-10-16 02:30 UTC, branch head a2a684eee5)

L: independent stage-2 immutable head a2a684eee5d4: stage-2 checks: (b) the item's stmt_deps gained lem-weil-integral-scalar-extension-constructible, which are neither new nodes of the delivery nor nodes landed on the base with a lean record (only those may be added, or a statement correction with statement_change)

## lem-sf-finite-cd-derived-upper-bound (2026-10-16 05:28 UTC, branch head d35074b9b1)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sf-finite-cd-derived-upper-bound: lem-sf-finite-cd-derived-upper-bound: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-pur-support-exact (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2182 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2182 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-verdier-preservation-strata (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2083 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2083 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-per-smooth-pullback-support-dimension (2026-10-17 20:30 UTC, branch head 84c88221dc)

L: independent stage-2 immutable head 84c88221dc47: H3: the Lean conclusion provides only an unrelated Nonempty isomorphism, without tying it to the normalized truncation comparisons, so it does not state the node’s canonical cohomology identification. Review written in review.md; both files compile via scompile.py.

## sk-def-localizing-closure (2026-10-18 02:36 UTC, branch head 13075641de)

L: independent stage-2 immutable head 13075641def3: H3/H7 (§1(C)): the item renders Λ=Q̄_ℓ as Profinite.continuousMapRingObj (PadicAlgCl ℓ) = C(−,Q̄_ℓ), following a stage-1 node fault. The source's condensed Q̄_ℓ is sk-def-sfb-qlbar-condensed (padicAlgClRingObj, finite-subextension-valued, explicitly not C(−,Q̄_ℓ)). The sibling det-def-localizing-closure-ctf-equals-bc and at least 12 of the 66 citers use that ring, and all landed project Lean uses padicAlgClRingObj; with the delivered hΛ these citers cannot instantiate at Q̄_ℓ. Required: correct the item statement under §1(C) (Q̄_ℓ = condensed ring of [sk-def-sfb-qlbar-condensed]; add it to stmt_deps; statement_change with all 66 citers; ## Statement corrected), replace the sixth set entry in both declarations with Mon.mk (Profinite.padicAlgClRingObj ℓ) (variant checked: compiles clean, 2.5 s), update the docstrings and lean.note, and supply an independent second reading (the current one is an author self-check). All else verified: every other clause, edge cases (empty scheme, zero ring, empty coproduct, E=Q_ℓ), recorded ConstantModelConstructibleFiniteTor and condensedRingObj, ambient DerivedCategory of Mod, IsTriangulated + IsClosedUnderIsomorphisms + coproduct closure over Type w with universes {w,u}, nonvacuity probe, no hollow def, no sorry, docstrings, no duplicate notion; delivered file compiles clean with nt_compile (2.9 s).

## lem-per-algebraic-valuation-coarsening-correspondence (2026-10-19 01:47 UTC, branch head 71c3c35abfc)

L: approved by the reader, but the landing refused it: NOT MERGED lem-per-algebraic-valuation-coarsening-correspondence: lem-per-algebraic-valuation-coarsening-correspondence: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-per-support-condition (2026-10-21 15:33 UTC, branch head 316a88c75fa)

I read the master order-2738 source, the delivered item, the report and the statements of every cited node. The STATEMENT-DISPUTED point is correct: def-trf-dualizing-complex is a finite-field, finite-A functor on D^b_ctf, so it does not accept a Q̄_ℓ object over an arbitrary field k. The defining formulas are kept exactly and the worker's small cases are right (K[1] on a point separates SuppCon from CosuppCon; uniformizer torsion has empty support). The repair still fails. C4/C7/E1: D_X now comes from lem-per-qbar-arbitrary-field-duality, which is dropped (side-live route-pivot-dropped.txt line 1836) and listed in removed_deps of repair-notes/lem-per-artin-gabber-affine-curve.json, which forbids arbitrary-field Q̄_ℓ duality. The live split artin-gabber node cites this item and reads it at finite Λ. The second new dependency, lem-per-adic-heart-pullback-fibres, is also in those removed_deps. No step justifies either. No live node gives arbitrary-field Q̄_ℓ Verdier duality (trf is finite-field and finite-A; thm-coef-qbar-verdier, the sf biduality and package nodes, and a1-qbar-curve-duality are F̄_q only), so a reviewer FIX is impossible and the repair needs a maintainer scope decision: a coefficient-parametric or finite-Λ definition, or ω as a representing object as in the recorded Lean QbarCosupportCondition. Batch-5 flags: def-pod-lisse is a general definition, and the universal catenarity of regular rings is general commutative algebra, so neither forces a RETURN by itself. The drop finding does. There are no new nodes, no proof and no fixes. This has the same stmt_deps as the RETURNed NU 31c07351, NO c9ae2850, NU 6ec74f68, NE a0c0c705, NI c9c9a8df, NG 08f9846c and ND b6463bc5; it is a dispatch loop, and the maintainer must decide the scope or write a repair note.



## lem-sfb-stable-pointed-isom-finite (2026-10-22 07:30 UTC, branch head no branch)

(the landing tools, head 24e28cba6) the delivery did not land: (merge queue) your landing 20261022T043752-NY-1054456-81 was taken out of the candidate: the global build of 3975127db4 failed in Sheaf.Algebra.Homology.DerivedTensorTruncationWindow Sheaf.Algebra.Homology.RingedSiteTorFlatModel Sheaf.Algebra.Homology.SitePerfectLowerModel Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract Sheaf.Algebra.Homology.SitePerfectTorWindow Sheaf.Algebra.Homology.SitePerfectUpperModel; this change is a possible cause


## det-prop-p1-adjunction-rational-unit-counit (2026-10-22 10:41 UTC, branch head no branch)

(the landing tools, head e328197e9) the delivery did not land: (merge queue) your landing 20261022T093638-NY-501278-264 was taken out of the candidate: the global build of 6f91d92f05 failed in Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality Sheaf.Paper.RationalLocalizedHom; this change is a possible cause

## lem-pur-transport-qbar-common-stage-counit (2026-10-23 21:55 UTC, branch head 47c7fb8e133)

E1/E7, C4, E5. The item was statement-only on the base, and the delivery edits its hypothesis although the report says no target statement is edited. On the base, the finite adjunctions were compatible via the transitive comparisons of sk-lem-sp-field-extension, with def-coefficient-twists-detailed twists. Now they are 'transported to the condensed categories by det-sp-rational-localized-hom' and compatible with 'transitive scalar comparisons on these condensed categories'. A parenthetical claims these are the sk-lem comparisons on the integral models, with no proof. The twists are switched to sk-def-sp-tate-twist. This is the same swap returned for Q126 a02d, NF 6d05, NP 3bd6, O4 8f86 and others. The only citer, sk-thm-purity-transport Assembly step 4, gets the hypothesis from lem-pur-transport-rational-hom-counit. That node only says that the sk-lem comparisons intertwine the bijections, and sk-lem defines b, a and their transitivity on the raw def-weil-rationalization-karoubi localizations. No node relates these to the condensed γ^! and pullback/twist comparisons. Searched with rg -L: the candidates are det-sp-rational-localized-hom (one fixed E, no coefficient change), det-sp-field-extension-towers (integral and raw), lem-pur-rationalized-smooth-adjunction-diagrams (raw) and the convention nodes. The main-20261024 blueprint's new det-sp-purity-coefficient-change (clause 3) makes the same conflation, and the nodes its proof needs (det-sp-qbar-adjunction, det-sp-rational-adjunction, sk-thm-sfb-rationalization-comparison) are not in the DAG. Step 2 uses b_{L/F} and a_{L/F}, which are never defined. The colimit conjugation needs b_{Ω,F}∘T(b_{F/E})=b_E, but det-prop-scalar-six-compact-support has no coefficient-composition clause. Steps 4, 6 and 7 inherit this ('chain ending at Ω … transitive comparisons'). Given the hypothesis, the rest of the algebra is correct: Step 3 descends finitely many arrows and relations, the Step 4 counit formula has the right direction, Step 5 c^G T(γ_E)=γ_Ω a_E holds by transposes, the Step 6 conjugation and Step 7 cancellation work, Step 8 uses the composite counit, and Step 9 is now closed. The new node lem-pur-condensed-compact-support-scalar-exchange is correctly typed: both sides go T v^*F_f M → F_{f'}u^*TM. Identity coefficients, the identity square, j=id and zero objects all check. It is not a duplicate of lem-pur-compact-scalar-base-change, lem-fix-direct-image-scalar-exchange or lem-weil-pbc-coefficient-exchange-mates, and it is not a clause of the item. Acceptable, but it does not fix the main fault. Batch-5 flags: sk-thm-existence, sk-def-sfb-(shriek-)base-change-morphism, det-prop-scalar-six-compact-support/pullback, det-sp-rational-localized-hom, sk-def-sfb-filtered-two-colimit and sk-thm-sfb-shriek-base-change are generic six-functor foundations, not steps of the proof of the trace formula or of Poincaré duality. Accepted. Repair needs a raw-to-condensed bridge node: at finite E the sk-lem b, a equal γ^! and the condensed pullback/twist comparisons, transitively through Q̄_ℓ. No fixes written.

## lem-sfb-split-torus-representation-weight-decomposition (2026-10-24 17:33 UTC, branch head cd30295bb0a)

L: independent stage-2 immutable head cd30295bb0a4: H7 (field part)/(b): item proof_deps adds lem-sfb-central-torus-faithful-weight-blocks vs the 13-entry base (no proof step uses it); check_statement_change refuses ('changed in proof_deps without a statement correction'); not fixable (fixes cannot edit item proof fields; --revert-statement would drop landed def-sfb-tori-multiplicative-type whose splitTorus the module uses). Correction: restore base proof_deps exactly (drop lem-sfb-central-torus-faithful-weight-blocks), keep everything else. Otherwise correct: Lean byte-identical to the mathematically accepted 9fe1 module; new existing:true def nodes def-sfb-finite-representation-basis (FiniteIndex/finiteBasis = finBasis reindexed) and def-sfb-character-point-scalar (characterScalar = ΓSpec pullback of T 1) are real-data, source-correct, no other owner in side-live; H2 resolved; statement re-read vs node (all-algebras weight equalizers, finiteness, IsInternal, homogeneous basis, diagonal matrix for every A,t; r=0, V=0, any char, zero algebra). No compile (no file changed).

## lem-per-conormal-extension-class-cokernel (2026-10-24 17:47 UTC, branch head defd38acce2)

L: independent stage-2 immutable head defd38acce29: Sheaf.RingTheory.MarkedSquareZeroExtension declares names that other modules already declare:
  Algebra.SquareZero.Extension: also in Sheaf.RingTheory.SquareZeroAlgebraExtension
  Algebra.SquareZero.Hom: also in Sheaf.RingTheory.SquareZeroAlgebraExtension
  Algebra.SquareZero.IsSplit: also in Sheaf.RingTheory.SquareZeroAlgebraExtension
Import and reuse the existing declaration. Renaming yours only hides the collision and leaves the same fact proved twice; rename only when the two declarations say different things.

## lem-sfb-stack-big-etale-derived-base-change (2026-10-24 17:48 UTC, branch head e45f122316d)

L: independent stage-2 immutable head e45f122316d3: the new node def-sfb-stack-big-etale-module-functors exists on sheaf-dag now (another delivery created it): return the delivery


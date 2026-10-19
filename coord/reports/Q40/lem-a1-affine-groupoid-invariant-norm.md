# Stage-1 repair report: lem-a1-affine-groupoid-invariant-norm

1. **Files written.**

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-invariant-norm.json`: split statement, unchanged statement; three direct proof steps replace the returned two-step specialization. Mathlib verdict remains no exact match.
- `citations.json`: seven verbatim statement quotes for every citation in the three replacement steps.
- `report.md`: this repair, current source review, and the retained earlier report below.
- No new nodes; no new Mathlib leaves. Existing sources, searches and ancestry are reused.

2. **Attachments.**

None. The retained source searches found no attachment, and the repair re-ran the item-id, determinant-trick and groupoid/norm terminology search under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, with no matching declaration. No upstream-master sorry declaration is counted as finished.

3. **WANTED.**

None. All source passages used are available in `literature/stacks-project/`.

4. **Return and repair.**

The return concerns reviewed head `a8757dc6d2`: landing refused it because the cited `lem-a1-affine-groupoid-polynomial-norm-invariant` statement changed after review. I compared the retained sandbox item and its quotes with the current shared item and cited statements. The scalar item statement is unchanged. The current polynomial statement adds explicit references to the norm-chart and determinant nodes, and its reviewed proof now applies this scalar item. Although the retained conclusion quote still occurs verbatim, the old proof is now circular. The required initial dry run confirmed exactly the two-node cycle between this item and the polynomial node.

I removed the polynomial citation and wrote the direct proof of Stacks 03BH. Step 1 constructs both pullback squares explicitly using composition and inversion. Step 2 computes the two pullbacks of the same norm on finite-free charts, citing the existing affine tensor-product identification and the determinant definitions. Step 3 uses equality of the pulled-back elements and basis independence, then glues the equality. This changes the mathematical proof, rather than only rebasing the rejected content. The normal delivery tool will package these changed fields on the current server base; no manual git command or write to the shared repository was used.

The previous polynomial-ring citation is no longer needed. `lem-pd-finite-locally-free-norm-charts` and `def-weil-endomorphism-determinant` were re-read in full and their old statement quotes remain valid. The other new proof citations are existing nodes, not newly created nodes. The statement and its statement dependencies remain unchanged. The norm-chart construction is declared as a generic tool in `split_report.tool_uses`; it supplies local norm sections without replacing the determinant-trick route. The other proof citations are definitions or Mathlib leaves.

5. **What I could not finish.**

Nothing remains in the mathematical split. This is stage 1 only: no Lean was written and no compiler, Lake, or build tool was run.

## Review by Q40

I read the item against `groupoids.tex` Tag 03BH (`lemma-determinant-trick`, lines 4251–4288), including its equalizer definition immediately before the lemma. The hypotheses are affine U and R and finite locally free s and t, with a groupoid functorially on all test schemes. The statement here gives exactly the same norm and equalizer conclusion. It assumes neither a constant rank nor reducedness nor that the arrows form a free relation. No correction to the item statement is needed. I also read `groupoids-lemma-diagram` at lines 2525–2550, `exercises-exercise-trace-det` (02DU) and `exercises-exercise-trace-det-rings` (02DV) at lines 1586–1625, and `divisors-lemma-finite-locally-free-has-norm` (0BD2) at lines 3788–3813. The latter is stated at fixed positive degree: only its local matrix construction is used, independently on each free chart. The existing norm-chart node expressly supplies charts without constant rank, positivity or surjectivity.

For step 1, I re-read the full statement of `def-pc-fibre-product`: it supplies the projections and universal property, including uniqueness. The displayed map (a,b) ↦ (a∘b,b) has inverse (h,b) ↦ (h∘b⁻¹,b); the source conditions make both composites defined. Composing these maps gives (a,b) and (h,b) respectively by associativity and inverse laws. Hence the right-hand square is a pullback; the left-hand square is the defining one. The equality t∘c=t∘p₀ is a groupoid identity, so it gives the equality of the two functions. This is an elementary argument in the stated groupoid laws and cited universal property; no omitted groupoid-diagram theorem is assumed.

For step 2, `lem-pd-finite-locally-free-norm-charts` says exactly that the norm section restricts to the finite-free norm on an affine chart at every point. I checked its finite, flat and locally finitely presented hypotheses against the item's finite-locally-free assumption. I read `lem-weil-pbc-fibre-product-affine-spectra` and its sources, Schemes 01I4 (`lemma-fibre-product-affine-schemes`, lines 984–1020) and 01JQ (`lemma-fibre-product-affines`, lines 3181–3193). Its statement identifies the whole section algebra and both projection maps with the tensor product and its inclusions; thus it supplies precisely the scalar-extension identifications used here. On an affine refinement W of s⁻¹(V_s) ∩ t⁻¹(V_t), these two identifications apply to the two squares established in step 1. I wrote the basis and multiplication coefficients after extension explicitly. `def-weil-endomorphism-determinant` identifies the multiplication determinant and states its independence of the finite basis. `def-weil-pbc-matrix-determinant` gives the exact finite signed sum of products; applying the ring map to that formula proves the scalar-extension equality. Thus the proof does not cite a definition for an unproved base-change theorem. The only non-elementary inputs in this step are the two existing construction/theorem statements just named. The remaining comparison is a few lines of matrix arithmetic from the cited definitions and is not a new node.

For step 3, the common section algebra on p₁⁻¹(W) has two pulled-back bases. Step 1 identifies the elements defining its two multiplication endomorphisms. The basis independence explicitly stated by `def-weil-endomorphism-determinant` therefore identifies the determinants. `def-pc-scheme` supplies a locally ringed space, hence the equality axiom for its structure sheaf makes equality on the covering W global. Finally, membership in C is the defining equality in the item. This is elementary after the earlier steps. Each cited sentence was copied verbatim into `citations.json`; I checked every quote against the current shared statement. The removed polynomial citation is absent from both `uses` and `proof_deps`.

Small cases checked: the identity groupoid has rank 1 and gives N(f)=f; a finite constant group acting trivially gives f to the order of the group; disjoint components with different group orders test varying rank; the empty U case is vacuous. Although nonempty groupoid source fibres cannot have rank 0 because of e, the determinant computation also covers the empty basis (its determinant is 1). Nilpotents in the base do not affect either the explicit groupoid inverse or the finite sum/product identity. No division, reducedness, global basis, affine intersection of two arbitrary opens, or constant-rank argument is used: the intersections are refined by affine opens.

Against delivery-errors B–E: there are no new nodes, so there is no new statement-only, duplicate, or unsearched-leaf issue. Existing sources and their tag/label pairs were read, and the proof is the source's argument rather than a restatement of the item as a new lemma. Every non-elementary input in step 2 has a cited statement that supplies it; the cartesian identification and determinant comparison are written explicitly. The two-node circularity diagnosed by the initial dry run is removed. All replacement steps are below 2000 characters. The original Mathlib search log was read and reused because the item statement and search question are unchanged; no unrun search was added. There is no SGA citation or change to a chapter, unit, launcher file, or other worker's node.

## Retained report from returned head a8757dc6d2 (superseded proof)

The following preserves the previous attempt's report and search findings. Its polynomial-specialization proof is superseded by the repair above; it does not describe the current proof.

# Stage-1 report: lem-a1-affine-groupoid-invariant-norm

1. **Files written.**

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-invariant-norm.json`: statement node, split; Mathlib search verdict: no exact match.
- No new nodes were needed. The existing same-unit node `lem-a1-affine-groupoid-polynomial-norm-invariant` is a strict polynomial generalization used by the proof.
- `citations.json`: four verbatim statement quotes covering the two proof steps.

2. **Attachments.**

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its groupoid/norm terminology, and the likely determinant-trick names; no project declaration states this item, and no sorry-free attachment exists.

3. **WANTED.**

None. The required sources are present: Stacks `groupoids.tex` Tag 03BH, `exercises.tex` Tags 02DU/02DV, and `divisors.tex` Tag 03JE.

4. **What was wrong or needed correction.**

The imported item was unsplit and had empty proof data. Its statement agrees with Stacks Tag 03BH, including the absence of constant-rank, reducedness, and arrow-relation freeness hypotheses. I retained the statement. The proof now uses the already existing stronger polynomial invariant node and then checks, chart by chart, that the constant-polynomial norm is the norm section in the item. No duplicate node was created: the existing polynomial node states the same conclusion for every `F ∈ A[T]`, while this item is its constant-polynomial specialization with the sheaf norm section made explicit.

5. **What I could not finish.**

Nothing remains mathematically unfinished. No Lean source was written and no compiler or Lake/build command was run, as required for stage 1.

## Earlier review (before the dependency changed)

I read the imported item, its unit `sk-p-real-rankin`, the ancestor route through `lem-a1-affine-hc0`, and the full relevant Stacks passages. In `groupoids.tex` Tag 03BH (lines 4251–4288), the groupoid diagram identifies the two pullbacks of the target function; norm compatibility with base change then makes the source and target pullbacks of the source norm equal. I also read the polynomial-coordinate norm statement already recorded in `lem-a1-affine-groupoid-polynomial-norm-invariant`, whose hypotheses exactly match the present affine groupoid and finite-locally-free source and target maps. Step 1 specializes its quantified `F ∈ A[T]` to the constant polynomial `f`, taking precisely its displayed conclusion `Q_F(T) ∈ C[T]`.

For Step 2 I read `lem-pd-finite-locally-free-norm-charts`: it supplies the global norm section and says its restriction on each finite-free affine chart is the finite-free algebra norm. I checked the determinant definition in `def-weil-endomorphism-determinant` and the coefficientwise polynomial-ring definition in `def-weil-polynomial-ring`. On a chart, adjoining `T` leaves the multiplication matrix for the constant element unchanged and hence leaves its determinant as a constant polynomial; evaluating the coefficientwise equality at `T=0` gives the item’s `N_σ(τ(f)) ∈ C`. The cited nodes therefore state exactly what each step uses, and all hypotheses (affineness, groupoid identities, finite locally free `s,t`, and the equalizer definition of `C`) are present in the item statement. I tested the specialization on the identity groupoid (where the norm is `f` to the rank of `s`) and on rank-zero/empty charts covered by the norm-section statement. The Mathlib searches were run twice with distinct phrasings for LeanFinder, Loogle, grep, and LeanSearch; they found only unrelated determinant, representation, or pullback results. The server `check_dag` precheck passed.

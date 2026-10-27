# Q42 stage-1 report: lem-pur-system-proper-open-invertibility

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-system-proper-open-invertibility.json`: item, statement unchanged, split into five steps; no Mathlib match.
- `citations.json`: ten verbatim statement quotations covering every proof-step citation.
- `searches.jsonl`: the actual search-command log, retained.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script.

There are zero new nodes and zero new Mathlib leaves. The sandbox initially contained no node, proof, report, citations or search log. The live item was copied and its inherited citations, blueprint provenance and search records retained. The new searches are appended, with the exact logged tool and query text.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, proper/open and semilinear/system notions found no declaration giving the varying-ring derived-system assertion with its finite normalization. In particular `AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar` in `SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Proper.lean:110` concerns the proper identification for one fixed coefficient category. Its statement does not supply the item, so it is not an attachment.

## WANTED

None. The sources used are present. The system extension is explicitly agent-written: Stacks 0F7B supplies the finite etale theorem, not the varying-ring realization or its evaluation compatibilities.

## Corrections and scope

The item's statement was not changed. Its empty imported proof was replaced by an assembly from existing statements. No assertion about equality of arbitrary derived-system morphisms being detected by evaluations is used. The proof first constructs the given system map, then computes its evaluations, and uses conservativity solely to infer that this map is invertible. It does not choose independent lifts of finite maps or assume that evaluation preserves K-injectivity. No SGA source, compiler, Lake or Lean-writing tool was used.

The nearest blueprint ancestor was checked with `blueprint_refs.py ancestor`. The ancestor's actual main-20261015 proof says that coherence consists of compatible finite-level statements; this split supplies the proper/open input needed in the already specified system projection-formula refinement. Blueprint searches for `proper open`, `proper/open`, `clopen`, and `varying-ring` gave no blueprint node stating this varying-ring result. Whole-DAG searches by 0F7B and the same notions located and reused the constant-tower calculus and evaluated-mate nodes. No chapter/unit route is changed and no unit realization record is due: this item is an auxiliary descendant, not the unit key statement.

## Unfinished work

None in this one-level split. Its existing dependencies remain separate DAG items, with their own statuses; this report does not assert that their proofs or the Lean library are finished.

## Not duplicates

No new nodes were created. The constant-ring tower theorem is used by applying it, separately for each n, to the constant tower on H_n over B=A_n. It is not restated as a new varying-ring lemma.

## Review by Q42

I read the item's chapter and unit records, its blueprint ancestor proof, and the sources underlying this assembly. In `literature/stacks-project/more-etale.tex` I read Tag 0F7B (`lemma-shriek-proper-and-open`), including the explicit K-injective comparison through the equality of proper-support subsheaves and the proof of the torsion-ring case. Open immersions satisfy the separated locally quasi-finite hypothesis of that source. Here the coefficient ring A_n is finite and torsion, but the proof actually invokes the existing constant-tower node on bounded etale-origin inputs. I also read `sites-cohomology.tex` Tag 07A7 (`remark-base-change`), whose counit-defined adjunct explains the mate convention, and Tags 0GL1 / 0E8I (`lemma-j-shriek-and-tensor`) in `sites-cohomology.tex` / `sites-modules.tex`. The latter provide the ringed-site foundation of the existing open-normalization result; they are not represented as a quoted theorem about semilinear systems. For constructible origin I read the existing statement and the master blueprint's `lem-sf-proetale-constructible-origin.md`, including its bounded-complex assertion and comparison argument. No new-node source is needed because there are no new nodes.

For Step 1 I opened `lem-cbc-strict-tower-proper-open-calculus` and checked that its statement allows arbitrary commutative proper/open squares, asserts that the induced s is clopen, gives bs=k and qs=r, and specifies the identity/zero projector. I only transfer that explicit projector across varying coefficients by the written equation t(1,0)=(1,0)t, not by assuming a geometric theorem for varying rings. This is the elementary coefficient check. The open compositors are the same section-preserving exact ones; no new theorem is hidden there.

For Step 2 I opened `lem-sf-open-tensor-normalization`, `lem-coef-semilinear-derived-sections`, and the constant-tower calculus. The first explicitly covers arbitrary inverse coefficient systems on ringed diagram topoi and defines beta inverse by the open-unit adjunct. The second explicitly says evaluation commutes with the specified adjunction transposes, pullback compositions and units. The third gives exactly the same open-unit definition for constant coefficients. These are matching statements, so equality of the evaluated beta follows by the adjunction bijection; evaluating the identity/zero projector then identifies alpha. This is a comparison of constructed maps, not an appeal to faithful evaluation.

For Step 3 the simultaneous-sections statement explicitly identifies evaluation of derived direct image and preserves units and counits. I substituted those identifications into each of the three factors of the item's displayed gamma. The resulting word has the source J_i R_r H_n and target R_p J_k H_n with the same proper adjunction units/counits. There is no unstated scalar-extension comparison in this calculation.

For Step 4 the constructible-origin node (ii) gives a bounded constructible etale witness for every intrinsic bounded constructible H_n, with the exact finite coefficient ring A_n. For each fixed n I checked all hypotheses of the constant-tower calculus: constant ring B=A_n, identity ring map B to Lambda_j=A_n at every tower index j, the constant tower on H_n with identity transitions, bounded-below witness L_n at every j, proper r,p and quasi-compact open k,i. The calculus says its gamma is invertible and its evaluation has precisely the named finite normalization. I opened `lem-cbc-tower-mate-evaluation-scalars`; its statement says that this evaluation is exactly the single-level clopen-projector unit-square-counit word. Thus it is the word computed in Step 3. This is the actual bridge between constant and varying rings; the two system categories are never identified. Repeating the same argument for any witness identifies the same intrinsic mate and proves witness independence without asking for compatible choices of L_n.

For Step 5 the simultaneous-sections statement explicitly says evaluations jointly detect isomorphisms on the ordinary unbounded derived category. That proves invertibility of the already constructed gamma. Its inverse and the finite inverses agree because functors preserve inverses and inverses are unique; inverse naturality follows by multiplication of the naturality equation. The constant-tower geometric statement explicitly includes refinement sections and non-Cartesian squares, so neither case was dropped.

I checked the small cases directly. If A is empty then both objects on which gamma is evaluated are zero. If the square is Cartesian, s is identity and the projector disappears. If r=1 the projector selects the clopen section, rather than being replaced by a cartesian beta. A genuinely non-Cartesian test is D=C=Spec(k), B=Spec(k) disjoint union Spec(k), A the first component, p the fold and r=i=1; the formula selects the first summand and gives the expected identity on H. Identity vertical maps likewise reduce to the open-extension identity. The family H_n=A_n[n] with zero quotient transitions has bounded constructible levels with no common lower bound; the proof treats it level by level. Nothing requires quotient maps A_m to A_n to be flat or these zero transitions to be normalized.

I checked delivery-errors B through E against the written split: no new statement to be under-specified, no proof tucked into a new unsplit node, no clause relabelled as a new lemma, every non-elementary invoked fact has the existing statement just described, and each of the ten quotations is an exact substring of that statement. All five steps are below 2000 characters. The only elementary step writes its coefficient-compatibility argument. No target, source route or statement was weakened.

The first dry run required a longer quotation for Step 4: its short invertibility sentence was below the tool's 40-character minimum. I replaced it with the full invertibility and finite-normalization passage, and checked that it is verbatim.

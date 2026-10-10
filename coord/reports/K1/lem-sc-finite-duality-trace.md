# lem-sc-finite-duality-trace

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-finite-duality-trace.json`: split into four proof steps; Mathlib has no trace comparison.
- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-curve-dualizing.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-proper-upper-shriek-composition.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-flat-duality-evaluation.json`: statement, unsplit; no Mathlib match.
- `citations.json`: verbatim statement excerpts for all ten citation occurrences, with the finite-flat node used twice.

## Attachments

None. `AlgebraicGeometry.Scheme.exists_isIso_pushforwardHomObjComparison_unit` at `WeilConjectures/AlgebraicGeometry/Curve/SerreDuality.lean:536` has exactly the item's hypotheses and conclusion, but its body at line 541 is `sorry`; the sorry map marks `s:true`. The comparison map itself and the remaining cited setup nodes have no new attachment here.

## Wanted

WANTED: Stacks Project, `duality.tex`, Tags 0BRT and 0ATX, for `lem-sc-smooth-proper-curve-dualizing` and `lem-sc-proper-upper-shriek-composition`.

WANTED: Stacks Project, `discriminant.tex`, Tags 0BVI and 0FKW, for `lem-sc-finite-flat-duality-evaluation`.

The local literature tree has only the catalog and citation tables, not the Stacks text. I read the official Stacks tag pages online and wrote the item's proof as an agent proof, recording the missing local source files above. The blueprint ancestor is `lem-sc-finite-duality`, whose first proof step requires the trace identification. The blueprint and DAG searches found no duplicate coherent-duality node; their similarly named étale dualizing-complex nodes have different coefficient theories. The source Lean theorem is the target statement here, not an independent proof.

## Issues found

The imported item was an unsplit statement with no proof or proof dependencies. Its source field points to the sorried Lean theorem. I retained the statement and its definition dependency, and made the construction of the trace and the evaluation identity explicit. No statement was weakened. The parent blueprint's brief reference to a codifferent computation cannot justify division by ramification index in characteristic dividing that index; this split uses coherent duality and applies to inseparable maps as well.

## Review by K1

I compared the item, hypothesis by hypothesis, with `exists_isIso_pushforwardHomObjComparison_unit`: an arbitrary field, an arbitrary scheme smooth of relative dimension one over it, a finite flat morphism to the standard projective line over the field, and existence of a trace whose unit-module comparison is an isomorphism. The Lean declaration is sorried, so the item still needs a split. I read Stacks 0BRT (smooth proper dimension-one dualizing complex), 0ATX (composition of upper shriek), 0BVI (finite flat duality and trace), and 0FKW (finite-morphism evaluation). Each new statement has precisely the corresponding scope: smooth proper curves, proper composable maps, or finite flat maps with an invertible target. Each is statement-only, introduces its own schemes and maps, and has the Stacks tag and label in its source field. LeanSearch returned HTTP 500; LeanFinder, Loogle, and source grep gave no coherent-duality match. I searched the whole DAG, the blueprint with `blueprint_refs.py`, and the Lean source by concept and declaration before creating them. None is a renamed clause of the item: each applies independently of this particular map to the projective line.

In step 1, `lem-pc-projective-proper` says a projective morphism is proper, `lem-weil-pbc-finite-proper` says a finite morphism is proper, and `lem-weil-pbc-proper-composition` says their composite is proper. `lem-weil-pbc-finite-type-over-noetherian` gives Noetherian source and target once the base is a field and both maps are proper. `def-sc-p1-standard` supplies the affine charts of the standard projective line; checking that their coordinate rings are polynomial rings in one variable gives smooth relative dimension one. I checked that proper maps are finite type, that the finite map is over `k`, and that the base field is Noetherian. The projective-line projection is projective by its `Proj` construction.

In step 2, the full statement of `lem-sc-smooth-proper-curve-dualizing` gives each shifted differential sheaf. The full statement of `lem-sc-proper-upper-shriek-composition` identifies the dualizing complex of the composite with the iterated upper shriek. The shift cancellation is formal for an exact derived right adjoint. Step 3 uses the rank-one clause of `lem-pc-projective-space-canonical` to verify the invertible-target hypothesis of `lem-sc-finite-flat-duality-evaluation`; that node explicitly gives the $f_*\mathcal O_X$-linear Hom comparison. Step 4 uses its evaluation-at-$1$ and $a$ clause verbatim, which is exactly the comparison map of the item after defining $\tau$. I opened each cited node statement; no step asks for a fact found only in a cited node's proof. The two off-unit nonclosed nodes are generic setup tools and are declared in `split_report.tool_uses`.

I checked the new statements on the identity of $\mathbf P^1_k$, a finite disjoint union of copies of $\mathbf P^1_k$, and Frobenius $t\mapsto t^p$ in characteristic $p$: evaluation gives the identity or summation in the first two cases, while the last requires the duality trace rather than division by $p$. For upper-shriek composition, an identity factor yields the expected identity isomorphism. For smooth duality, $\mathbf P^1_k$ gives $\mathcal O(-2)[1]$. The empty finite flat source gives zero on both sides of the Hom comparison. The statement-only nodes make no unsupported separability or connectedness assumption. I corrected the finite-duality source path to `discriminant.tex` and changed a too-short citation quote to the finite-proper node's whole sentence. Nothing remains unfinished at this one-level split.

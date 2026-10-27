## Worker report

This is the stage-2 statement delivery, following Q148's accepted stage-1 split. The previous Q140 ending concerned an unchanged stage-1 split; the current node has no Lean record and is a stage-2 queue item. `coord/brief-stage2.md` §0 explicitly distinguishes these stages. There was no interrupted delivery or Lean file in this sandbox. No repair note exists for the item.

The module is `lean/Sheaf/SixFunctors/ClopenComparisonTensorSquare.lean`, namespace `SheafOfModules.ClopenComparisonTensorSquare`, primary declaration `clopenComparisonTensorSquare`. Its only postponed proof is that theorem. The other declarations are real definitions or record types packaging its specified operations and equations; there is no chosen object obtained from a mere existence sorry. The original statement and accepted split are unchanged. There are no new nodes or dependency-record repairs.

### Hypotheses and constructions

| Node text | Lean rendering |
| --- | --- |
| Schemes A, B, C, D | `{A B C D : Scheme.{u}}`, with `u` explicitly bound. |
| k and i quasi-compact open immersions | `k`, `i`, `[IsOpenImmersion k]`, `[IsOpenImmersion i]`, `[QuasiCompact k]`, `[QuasiCompact i]`. |
| r and p proper | `r`, `p`, `[IsProper r]`, `[IsProper p]`. |
| pk=ir | `h : k ≫ p = r ≫ i`; Lean composition runs from left to right. |
| B_C, b, q | `input` has `U' := Limits.pullback p i`, `j' := pullback.fst p i`, `gU := pullback.snd p i`. The chosen Cartesian square uses the actual pullback symmetry and both projection equations. |
| s=(k,r) clopen | `StrictTower.squareLift k r p i h`, literally `pullback.lift k r h`; the dependency's `squareLift_open` and `squareLift_closed` give the geometric instances from the original hypotheses. |
| Ordinary pro-etale sites or vertical sequence sites | The unrestricted binder `m : Mode` covers `.ordinary` and `.systems`. The imported `Site`/`topology` are respectively `X.ProEt` and `ℕ × X.ProEt` with the vertical topology. |
| Arbitrary O_D, O_B | `R : Sheaf (topology m D) CommRingCat.{u+1}` and `S : Sheaf (topology m B) CommRingCat.{u+1}`. No constant-coefficient restriction. |
| Structural p inverse-image ring map | `c : R ⟶ (baseChange m p).sheafPushforwardContinuous.obj S`. This is the adjoint form of the specified `p⁻¹R ⟶ S`, the same convention as the dependency's `Input`. It is an arbitrary ring morphism. |
| O_C and O_BC restricted rings, induced q map | The dependency's `restrictRing m i R`, `restrictRing m b S` and `cornerCoefficient t`; its `SiteSquare.first` and `Operations.rightSections` fix the fibre-product section map. |
| O_A=k⁻¹O_B and compositors | Use the canonical iterated-restriction presentation `restrictRing m s (restrictRing m b S)`. Since `s ≫ b = k`, this is O_A under the open-composition identification. `k_!` is presented as `J_s ⋙ J_b`, `P_k` as `P_b ⋙ P_s`, and `P_r` as `P_q ⋙ P_s`. These are the composite adjunction presentations, retaining their composed units, not additional arbitrary compositor choices. |
| Unbounded derived categories | The imported `Mod`, `Der`, `TensorModel`, `Pullback`, `OpenExtension` and exact localization are used directly. `Der` is ordinary `DerivedCategory (Mod R)`, with no boundedness predicate. Site objects live in `Type (u+1)` and site Hom types in `Type u`; no equality of these universes is imposed. |
| Canonical mu_p and mu_q | `Data.tensorP` and `.tensorQ` are `PullTensor` presentations. The ordinary `pure_unit` equation fixes the canonical comparison by the specified ordinary adjunction; `representative` pins its derived comparison to the published `totalMap` on flat K-flat complexes, with `derivedPullbackComplexComparison` from the actual derived counit. This helper permits nonexact ordinary pullback; it does not replace p by a flat morphism. |
| Canonical mu_b and mu_s | `Data.tensorB` and `.tensorS` retain ordinary restriction of pure sections and the dependency's `TensorComparison`, including its signed-total representative equation. |
| Normalized delta_i and beta | `a : Assertion o` gives `a.gamma` and `a.beta`, with their inverse-transpose/open-unit normalizations. The parameters `t`, `o`, `a` are exactly the already stipulated choices of these canonical models, supplied for either mode by `openTensorNormalization`. |
| Normalized delta_b and delta_s | `OpenTensor.delta` and `inverse_transpose` use the fixed exact open adjunction and the canonical tensor comparison. |
| rho_s=(1,0) | `Data.rightAdjunction` is the reverse ordinary clopen adjunction. `counit_normalization` identifies its counit with the inverse of the ordinary open unit. This determines the first-factor adjunction and its unit. `Data.rho` is the unit of `exactDerivedAdjunction rightAdjunction`, so it is the localized component projection, not an unconstrained morphism. |
| delta_k independently normalized | `Data.deltaK` is an isomorphism for the composite open operation. `inverse_transposeK` specifies its inverse using the composite open adjunction unit and the composed canonical tensor comparison. Its equality with the pasted delta_b/delta_s is asserted separately. |
| alpha | `alpha` is beta followed by `b_!rho_s` at `P_q H`. The final k/r identifications are represented by the composite functors just described. |

The conclusion includes existence of the remaining simultaneous normalized data and then the equations for **every** such datum. Thus there is no missing coefficient hypothesis or assumed tensor square disguised as a record parameter. The records contain the canonical constructions and their defining normalizations; none of the tensor equalities to be established appears in those input records.

### Every conclusion clause

`Equations a v` is a conjunction of the following four universally quantified map equalities, in the displayed order.

1. The first conjunct is (1). Its left route is `P_p(a.gamma)` then `a.beta` at `H tensor P_i N`, then `b_!mu_q`, then `b_!(1 tensor theta.inv)`. Its right route is `mu_p`, `(beta_H tensor 1)`, then `delta_b`. The final theta inverse is exactly the node's identification `P_q X = P_b Y`, spelled out rather than silently treating isomorphic objects as equal.
2. The second conjunct is the first sentence of (2), for **all** `F V : Der O_BC`: `rho_(F tensor V)` then `s_!mu_s` equals `(rho_F tensor 1_V)` then `delta_s`. The map is on the derived category itself, not on its cohomology.
3. The third conjunct is the composite-open sentence of (2), for all `M : Der O_A`, `N : Der O_B`: `delta_b` followed by `b_!delta_s` equals the independently normalized `deltaK`.
4. The fourth conjunct is (3). Its left route applies `P_p(delta_i)`, `alpha_(H tensor X)`, and `k_!mu_r`; the latter is explicitly `P_s(mu_q)` followed by `mu_s`. Its right route is `mu_p`, `(alpha_H tensor 1_Y)`, and `deltaK`, followed by `k_!(1 tensor P_s(theta.hom N))` to use `T=P_r X` on both routes. This is the node's canonical pullback identification `P_kY=P_rX`. The common source is `P_p(i_!H tensor N)` and the common target is `J_b J_s(P_s P_q H tensor P_s P_q P_i N)`.

Naturality is that of the constituent functors, natural isomorphisms, adjunction units and the beta/projector composite. No coefficient evaluation appears in any equation. Arbitrary strict semilinear transitions are part of the ring sheaf on the whole vertical site. The variables H,N,F,V carry no boundedness, flatness, constructibility or Tor-amplitude assumptions. Flatness occurs only for the resolving representatives in the **definition of the canonical comparison**, not as a restriction on these derived objects. No proper projection map is inverted or assumed an isomorphism.

### Dependencies and sources

Read the statements and Lean records of all seven statement dependencies and the source signatures/docstrings. `def-weil-scheme-morphism-properties` is a convention node: it delegates to the actual Mathlib `IsOpenImmersion`, `QuasiCompact`, `IsProper` declarations. `def-pc-fibre-product` is Mathlib `CategoryTheory.Limits.pullback`, including `fst` and `snd`. `def-weil-pbc-proetale-site` is Mathlib `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`. `def-coef-semilinear-system-models` supplies `WeilConjectures.SemilinearSections.Systems` in `Sheaf.Paper.SemilinearSystemModels`; the same module-sheaf and whole sequence-site encoding is used by the open-normalization Mode API.

The other public imports are `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` (`CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`, arbitrary structural maps and independent site object/Hom universes), `Sheaf.SixFunctors.OpenTensorNormalization` (`openTensorNormalization`, `Input`, `SiteSquare`, `Operations`, `Assertion`, `exactDerivedAdjunction`) and `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` (geometric `StrictTower.squareLift` and its clopen instances). The last import is used for coefficient-independent geometry, never to specialize the rings to a constant ring. The `ProjectionRestriction` aliases, canonical signed `totalMap` and `TensorComparison` are reexported by the open-normalization dependency; there is no second definition of a module category or tensor product.

The proof-only imports cover `lem-sfb-ringed-projection-tensor-structure` (`ProjectionCoherence.ringedProjectionTensorStructure`) and `lem-pur-clopen-ringed-module-gluing` (`Scheme.ProEt.clopen_ringed_module_gluing`). `def-weil-exact-derived-adjunction` is already publicly imported as `OpenTensorNormalization.exactDerivedAdjunction`. The main theorem's docstring contains all seven accepted proof steps, including the exact clopen Hom adjunction needed to compare arbitrary unbounded morphisms before evaluation.

Read the local Stacks sources: `sites-cohomology.tex` Tag 07A4 (`lemma-pullback-tensor-product`, including the flat K-flat totalization construction), Tag 0GL1 (`lemma-j-shriek-and-tensor`), and `more-etale.tex` Tag 0F7B (`lemma-shriek-proper-and-open`, proper/open geometric context). The three simultaneous tensor identities are the accepted agent refinement, not a purported verbatim theorem of Stacks.

### Edge cases and searches

Checked empty A, empty C (hence B_C empty), the empty complementary component (s an isomorphism), zero rings and zero derived inputs: the clopen unit is the first-factor projection, and the equations reduce to zero maps or the normalized identity comparisons. Non-Cartesian proper/open squares remain allowed. A nonflat p or structural ring map is allowed: neither the API nor the theorem asserts ordinary pullback exact. Nonflat coefficient transitions remain allowed because no scalar reduction/evaluation detects equality in the assertion. Arbitrarily unbounded H,N,F,V remain allowed. The identity-open and arbitrary-lift cases are included through the same composite adjunctions and actual pullback lift.

Searches actually run with `msearch.py` for Q140 and this item:

- LeanFinder, `clopen projection open base change derived tensor compatibility square`: 8 hits, ordinary scheme pullback/tensor-product projection identities (`Scheme.Pullback.Triplet.*`, `pullbackSpecIso_*`); none states these derived tensor squares.
- Loogle, `CategoryTheory.NatTrans, CategoryTheory.Adjunction`: 0 hits.
- Mathlib grep, `clopen.*tensor|tensor.*clopen|open.*baseChange.*tensor`, in `CategoryTheory`: 0 hits.
- LeanSearch, `canonical clopen projection extension by zero derived tensor compatibility`: 8 hits (linear algebra tensor zeros, spectrum clopen basic opens, Tor, and unrelated topological instances); no match.

Also searched the exact item tag in `lean/WeilConjectures`, and clopen/tensor/comparison names in `lean/WeilConjectures/SixFunctors` and `lean/Sheaf`. The existing `ClopenIdempotent` constructions concern fixed coefficients, and `SystemClopenTensorCompatibility` concerns the downstream projection-mate assertion on a more specialized system domain. `ProperOpenProjectionMate` contains the motivation in its docstring and the downstream mate theorem, not this arbitrary-ring three-square statement. The generic normalization and ringed tensor foundations are reused. No exact existing declaration covers the item.

No STATEMENT-DISPUTED flag, node fault, statement correction or citer change is needed. The sandbox contains the new module, the item node changed only in `lean`, and this report. All compilation and delivery checks use the authorized server wrappers.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

Item: `lem-sf-projection-base-change-common`, group ND, stage 2, 2026-10-28 UTC.

Attach the exact existing declaration
`WeilConjectures.sixFunctorProjection_baseChange_common` in
`Sheaf.Paper.ProjectionFormulaCoherence`, source file
`lean/Sheaf/Paper/ProjectionFormulaCoherence.lean:648–673`, with `existing: true`.
No Lean module is added. The theorem currently has `sorry`; this delivery records
its statement and does not certify a proof. The node changes only in `lean`, whose
`statement` was extracted verbatim from the theorem keyword to immediately before
`:= by`. No dependency node, mathematical statement, proof plan or dependency list
is changed. There is no repair note for this item in the read clone.

I read the node's statement, source (including its retained exact header), six
proof steps, and all six statement dependency records and their declaration
signatures/docstrings. I also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`
`prop-sf-pf-coherence.md`, its `.proof.md`, and `_section.md`. The node is the
common-coefficient specialization of the displayed base-change square there.

The existing theorem renders each hypothesis and clause as follows:

| Node hypothesis or clause | Existing Lean expression and meaning |
| --- | --- |
| Finite field of characteristic p and its algebraic closure k | Section parameter `{D : FiniteFieldDatum.{u}}`; `FiniteFieldDatum` carries p, its primality, a positive exponent, k₀, its finite-field cardinality, k and `IsAlgClosure k₀ k`. |
| Prime ℓ distinct from p and fixed algebraic closure of Qℓ | `{C : D.CoefficientDatum}`; `C.l`, the prime instance, `C.different`, `C.Qbar`, and its algebraic closure instance. |
| Finite extension E/Qℓ and n ≥ 1 | `{E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}`. The valuation ring and quotient/uniformizer convention are those of the operation datum's existing coefficient constructions; they are not extra free comparisons in this formula. |
| Six-functor datum with its specified operation/comparison data | `(S : SixFunctorDatum D C E n hn)` extends `SixFunctorOperationDatum D C E n hn`. Its inherited `closure` gives the actual common-stage functors, tensors and exchange data. |
| Work at Qbar in the common finite-stage category | Both inputs have type `generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar ...`, the literal finite-field pair category, with Hom direct limits, not a Karoubi envelope. |
| Cartesian square of finite-type k-schemes | `∀ (Q : SixFunctorCompactifiedSquare D)`; its objects are `SixFunctorSpace D`, the full subcategory of `Over (Spec (.of D.k))` with locally finite type and quasi-compact structure maps. `Q.square` is the displayed `IsPullback`. |
| f separated; no separatedness of g or any structure morphism | `[IsSeparated Q.f.hom.left]` is the only separatedness binder of this theorem. Neither `SixFunctorSpace` nor `SixFunctorCompactifiedSquare` requires any of the excluded separatedness assumptions. |
| Supplied compactification c and its Cartesian base change c′ | `Q.i`, `Q.p`, `Q.i'`, `Q.p'`, their open/proper fields, `factorization`, `factorization'`, `properSquare`, and `openSquare`; `Q.compactification` and `Q.compactification'` retain these very factors. |
| U_u, F, F′ | `S.closure.commonStage.pull u`, `.support Q.f Q.compactification`, and `.support Q.f' Q.compactification'`. |
| Specified P_f(K,L) | `(S.closure.commonStageExchange Q).projectionComponent K L`. `projectionComponent` inserts only the stage's recorded functor equalities around the supplied proper-counit/open projection. |
| Specified e_M with only endpoint identifications | `sixFunctorProjectionExchange (S.closure.commonStageExchange Q) M`; its body is the recorded `stage.compactExchange.app M` conjugated by `eqToHom` of `horizontal`, `compactSupport`, `compactSupport'`, `horizontal'`. |
| Canonical normalized μ_u(A,B) | `sixFunctorProjectionCommonMu S u A B`; its body conjugates `canonicalCommonStagePullbackTensor C.l C.Qbar u.hom.left A B` by the datum's `commonStagePullback` and `commonStageTensorNormalization` equalities. It constructs no arbitrary tensorator. |
| Exact κ_L | `(S.closure.commonStage.pullComposition Q.g' Q.f).inv.app L ≫ eqToHom (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj L) Q.squareComm) ≫ (S.closure.commonStage.pullComposition Q.f' Q.g).hom.app L`. This is the inverse compositor, equality transport, then forward compositor in the stated direction. |
| Completed integral/rationalized/common finite-field conventions | Inherited `S.higher`, `S.integralNormalization`, `S.coefficientIntegralNormalization`, and `S.closure` are the operation datum's normalized stages. `commonStageComparison` and `commonStageExchangeComparison` use the recorded rational-stage inclusions and scalar comparisons, with identity/tower coherence. No field-to-finite reduction is introduced. |
| First composite | The theorem's left side is `U_g.map (projectionComponent K L) ≫ sixFunctorProjectionExchange ... (K ⊗ U_f L) ≫ F'.map (μ_g'.hom ≫ (tensor.obj (U_g' K)).map κ_L)`. Lean's `≫` orders these arrows from source to target, giving exactly the displayed mathematical composite. |
| Second composite | Its right side is `μ_g.hom ≫ ((tensor Y').map (sixFunctorProjectionExchange ... K)).app (U_g L) ≫ projectionComponent (U_g' K) (U_g L)` using `commonStageExchange (compactSupportProjectionSquare Q.f' Q.compactification')` for P_f′. This last identity square keeps precisely c′. |
| Common source and target | The left route starts with `U_g(FK ⊗ L)` and ends with `F'(U_g'K ⊗ U_f'U_gL)`; the right route starts with μ_g at that same source and ends with P_f′ at that same target. No independent endpoint isomorphism is an argument of the theorem. |
| Arbitrary K and L; no extra Tor condition | `(K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.X.obj.left)` and `(L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.Y.obj.left)`, with no predicate or extra proof binder on either input. |

Dependency declarations read and reused by the existing statement:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum` (A1–A6,
  extends the operation datum).
- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`
  and its `closure`/higher coefficient normalization fields; its public dependency
  `SixFunctorOperationDatumStages` supplies `SixFunctorSpace`,
  `SixFunctorCompactifiedSquare`, `SixFunctorCommonStages`, and
  `SixFunctorExchangeData.projectionComponent`.
- `Sheaf.Paper.ConstructibleProjectionMates`:
  `WeilConjectures.CompactSupportFiniteProjection.component` and
  `WeilConjectures.compactSupportProjectionSquare`. The former is the finite-domain
  construction required by that definition node; this theorem is about the
  recorded common-stage components, not a substitute finite-domain theorem.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`,
  `.compactExchange`, `.projection`, `compactificationExchangeFromData`, and
  `compactificationProjectionFromData`. These are the specified mate followed by
  open comparison and proper counit projection followed by open projection.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `WeilConjectures.canonicalCommonStagePullbackTensor` and its representative
  uniqueness characterization. This supplies μ inside the exact existing helper
  `WeilConjectures.sixFunctorProjectionCommonMu` (same existing theorem module,
  lines 617–635).
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` (lines 681–690).

Edge cases checked by reading the statement and its constructors: n=1 is allowed;
n=0 is intentionally outside `hn`. Identity f or g and identity compactifications
are included. Empty schemes and zero K or L are not excluded by any binder.
Nonseparated horizontal g and nonseparated structure morphisms are admitted by
`SixFunctorSpace`/`SixFunctorCompactifiedSquare`; properness occurs only on the
specified compactifying factors. K and L may start at different finite coefficient
fields, since the category is the common-stage pair category. κ's orientation
was checked from `pullComposition`: its inverse starts at U_g′U_f, its middle
transport uses `Q.squareComm : g' ≫ f = f' ≫ g`, and the final hom ends at U_f′U_g.
The tensor map of κ acts in the second variable; the tensor of e_K with identity
acts by the first-variable map followed by `.app`, so neither factor is reversed.
No false statement or required correction was found.

Searches actually run on 2026-10-28 (via the prescribed msearch.py where applicable):

- LeanSearch: `Projection formula for compact support derived direct image commutes
  with Cartesian base change` → 8 hits on proper/separated/universally closed base
  change and unrelated sheaf/categorical facts; no exact common-stage formula.
- LeanFinder: `For algebraically closed l-adic common finite coefficient field
  constructible derived sheaves the canonical compact support projection formula
  commutes with Cartesian base change and monoidal pullback comparisons` → 8 hits,
  principally `SheafOfModules.pullbackComp` and pullback-free comparison lemmas;
  no compact-support common-stage equality.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal` → 12 hits on
  monoidal unit/counit laws and adjunction lifts; no exact match.
- msearch grep in Mathlib/CategoryTheory:
  `projection.*baseChange|baseChange.*projection|rightAdjointProjectionMap`
  → 0 hits.
- `rg -n 'sixFunctorProjection_baseChange_common|projection.*baseChange|baseChange.*projection'
  lean/WeilConjectures` → fixed-coefficient etale projection/base-change results,
  including `LowerShriekProjectionBaseChange`; these have different categories,
  and are not the datum's common-stage equality.
- `grep -rn 'lem-sf-projection-base-change-common' lean/WeilConjectures` → no hits.
- `rg -n 'sixFunctorProjection_baseChange_common|sixFunctorProjectionCommonMu'
  lean/Sheaf` → the exact theorem at `ProjectionFormulaCoherence.lean:648` and its
  canonical μ helper at line 617. The full signatures, helper bodies, section
  parameters and docstrings were then read, not inferred from their names.

The search therefore requires reuse, not another module. The existing theorem's
proof docstring names the open-factor equation, the proper counit/mate equation,
compactification pasting, equality before finite evaluation, and rational/common
coefficient passage. This agrees with the retained node proof route; stage 2 does
not replace that route or prove it. Validation uses deliver2.py's real server
existing-declaration probe and preflight; there are no new delivered Lean files.

## Second reading by ND

Performed as a second pass by the same dispatcher-started worker, without claiming
an independent second agent (the assignment explicitly prohibits starting agents).
The maintainer's independent review is still required. I reopened the theorem,
μ/exchange helper bodies, compactified-square constructor and node statement.

I checked every row of the hypothesis/clause table above against the full header.
In particular: the only explicit separatedness is Q.f; both inputs are unrestricted
common-stage objects; Q carries all three Cartesian squares and both factorizations;
the left side first pulls P_f back, then exchanges at the tensor object, then maps
μ_g′ followed by 1⊗κ under F′. The right side first applies μ_g, then e_K⊗1,
then P_f′ for the identity square of the very same c′. The expression for κ has
inverse/com-mutation/forward order, and the two uses of μ are the canonical
comparison conjugated solely by the datum's recorded equalities. I also checked
that the category is the recorded pair category, not a field-specialized finite
coefficient category or a new completion. No mismatch was found and no mathematical
statement or helper was changed. The only change is attaching the pre-existing
full theorem and recording its exact source signature.

## Validation

The prescribed `deliver2.py ND lem-sf-projection-base-change-common --no-push`
passed the server preflight and compilation on 2026-10-28 UTC (dry-run commit
`10359cbf30d`). A direct comparison also confirms that only `lean` changes,
its signature matches the existing source verbatim, and the node retains
one-space JSON indentation, Unicode text and its final newline.

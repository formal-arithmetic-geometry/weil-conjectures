## Worker report

The module `Sheaf.Paper.WfConstructibleTensorKoszulUnit` states the three parts of
`lem-wf-constructible-tensor-koszul-unit`, as three named theorems, each with whole proof
`sorry`. There are no new definitions. The item statement is unchanged. The added statement dependencies cite the already landed owners of the interfaces
used by the signatures. The ownership corrections required by both returns are recorded
below; the mathematical statement and all three Lean declarations are unchanged.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{u}` supplies the primes/base-field side: `D.p` is prime,
  `D.exponent_pos : 1 ≤ D.a`, `D.cardinality_eq : D.q = D.p ^ D.a`, the finite field
  `D.k₀` with `Nat.card D.k₀ = D.q`, and its algebraic closure `D.k`.
- `c : D.CoefficientDatum` supplies `c.l`, `Fact c.l.Prime`, `c.different : c.l ≠ D.p`,
  the specified algebraic closure `c.Qbar` of `Padic c.l`, and its algebra structure.
  `E : Padic.FiniteCoefficientFields c.l c.Qbar` is the finite intermediate extension.
  `pbcFiniteField.{u} c.l c.Qbar E` is the existing canonical shrink model, not a new
  coefficient field. `pbcStageDatum` and `pbcStageUniformizer` use the existing valuation
  ring and chosen uniformizer on that model.
- `W₀ : Over (Spec (.of D.k₀))`, `[hsep : IsSeparated W₀.hom]`,
  `[LocallyOfFiniteType W₀.hom]`, `[QuasiCompact W₀.hom]` are precisely the separated
  finite-type scheme over the finite field. `include hsep` retains separatedness on all
  three declarations. `W = (D.geometricFiber W₀).left` is the actual specified base change.
- The ambient category is `PbcCompletedDerived W (pbcStageDatum ...)`: the derived
  category of modules over `pbcAdicCompletion W (pbcStageDatum ...)`. This is the
  inverse limit of the positive quotient sheaves on the small pro-etale site. The
  site has object universe `u+1`, morphism universe `u`, coefficients in `u+1`.
  No equality of site object and morphism universes is imposed.
- Integral objects `M,N` are `PbcBoundedConstructibleComplete W (pbcStageDatum ...)`, the
  full integral subcategory underlying the recorded Weil category. All ambient arrows
  are retained. No Weil structure is required on an integral input.

Conclusions, clause by clause:

1. `wfConstructibleTensorCategories` gives the membership equivalence between
   `sfIntegralConstructible` (the category of `lem-fix-constructible-tensor-completion`)
   and `PbcIsBoundedConstructibleComplete`, after the existing `integralDetailedTransport`.
   This transport is restriction along the projection-normalized completed ring
   isomorphism `integralDetailedCoefficientComparison`; its inverse is exact restriction
   along the inverse ring map. Hence this identifies full subcategories of the same
   mathematical D(B), rather than identifying two unequal Lean presentations by fiat.
   Its second conjunct is a natural isomorphism of each reduction functor, between
   `integralDetailedTransport ⋙ pbcConstantReduction` and
   `scalarReductionDerivedExtension ⋙ pbcDerivedRestrict` along the specified finite
   quotient equivalence `integralCoefficientULift`. This expresses the identical
   reductions under the canonical coefficient presentation, including every positive
   exponent, with `n : ℕ` meaning exponent `n+1`.
2. `wfConstructibleTensorKoszulComparison` supplies `ρ` as an isomorphism of functors
   from the whole ambient D(B). Its source is exactly
   `completedReductionTower ⋙ completedRlim` and its target is exactly
   `wfCompletion ⋙ ObjectProperty.ι _`. Thus naturality of ρ is part of its type.
   For every ambient K it explicitly requires
   `(completedQuotientCompletionUnit W d).app K ≫ ρ.hom.app K = wfCompletionUnit ... K`.
   In particular at the ordinary tensor T this is `ρ_T ∘ χquot = η_T` as in the node.
   The quotient unit is the published derived adjunction unit followed by Rlim of the
   specified strict quotient augmentation. The intrinsic unit is the published Koszul
   product mapping-fiber unit `(u,0)`, transported from its genuine representative.
   Neither arrow is an existentially chosen replacement. The node's proof step 3
   explicitly states this comparison for every ambient object V, which is why the
   natural isomorphism has this domain.
3. `wfConstructibleTensorKoszulUnit` uses `wfOrdinaryDerivedTensor` to form precisely
   `T = M ⊗ᴸ_B N`, before any completion. Its first two conjuncts assert
   `PbcIsBoundedConstructibleComplete W d T` and that same predicate for
   `((wfCompletion ...).obj T).obj`. The latter `.obj` only forgets the complete full
   subcategory; the object is the specified intrinsic Koszul fiber.
4. The third conjunct is `IsIso (wfCompletionUnit ... T)`, so it is specifically η_T
   that is invertible. Together with ρ's unit equation this also makes the specified
   quotient unit invertible, as required by the proof route.
5. The final quantified equation takes any `f : M ⟶ M'` and `g : N ⟶ N'`, with no
   IsIso assumptions. `wfOrdinaryDerivedTensor.map (Prod.mkHom f.hom g.hom)` is
   `f ⊗ᴸ_B g`; `((wfCompletion ...).map ...).hom` is C applied to that arrow, in D(B).
   The displayed Lean equation is `h ≫ η_T' = η_T ≫ C(h)`, exactly the node's equation
   with Lean's left-to-right composition convention.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its public coefficient constructions in
  `Sheaf.NumberTheory.Padics.CoefficientExtension` (integers, uniformizer, ideal and
  quotient rings). The data are those of `def-weil-l-adic-coefficient-extension`.
- `Sheaf.Paper.PbcWeilCategory`: `WeilConjectures.WeilD`, `WeilDQbar`,
  `weilGeometricFiber_coefficientHypotheses`; its integral coefficient source is the
  `PbcBoundedConstructibleComplete` full subcategory. The imported `FiniteFieldDatum`,
  `CoefficientDatum`, `pbcFiniteField`, `pbcStageDatum`, `pbcStageUniformizer` and
  `geometricFiber` supply the fixed arithmetic and geometric data.
- `Sheaf.Paper.WeilTensorProduct`: `AlgebraicGeometry.Scheme.wfOrdinaryDerivedTensor`,
  `WeilConjectures.wfUniformizer_generates`. The former is the actual localized K-flat
  tensor bifunctor with the recorded small-site coefficient universes.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: `completedKoszulFiber`,
  `completedIntrinsicCompletionMap`, `IsCompletedIntrinsicallyDerivedComplete`.
  `Sheaf.Paper.IntrinsicCompletion` transports that same fiber and `(u,0)` unit through
  the canonical completed-ring presentation. `Sheaf.Paper.WeilCompletedTensorReflector`
  supplies `wfCompletion`, `wfCompletionUnit`, `wfCompletionObj`, and the morphism
  action uniquely determined by its Hom bijection. These are reused directly.
- `Sheaf.SixFunctors.ConstructibleTensorCompletion`:
  `WeilConjectures.constructibleTensorCompletion`, including its actual ordinary
  tensor localization, quotient-tower comparison and zero shifted-fiber coordinate.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectDetailed`; its public coefficient transport module supplies
  `integralDetailedTransport` and `integralCoefficientULift` with their full signatures.
- `Sheaf.Paper.CompletedQuotientUnitNormalization`:
  `completedQuotientCompletionUnit`; public imports supply `completedReductionTower`
  and `completedRlim`. `Sheaf.Paper.PbcUniformReductionProfile`:
  `pbcConstantReduction`, the existing reduction plus finite coefficient comparison.

The recorded, stated proof dependencies are imported privately: finite-type dimension,
`IntegralAmbientOperationModels.integralAmbientOperationModels`,
`ConstantCompletion.equivalence`,
`ringedStrictTowerHomotopyLimitIndependentCoefficients`,
`integralOperations_preserve_constructible`, `IntegralUniformCoefficient`,
`BoundedConstructibleTower`, and `wfCompletionReflector`. Statement dependencies use
public imports. Mathlib's recorded base-change stability and qcqs/Noetherian permanence
facts are available through these public dependency imports. The docstrings retain all
five proof steps: geometric hypotheses/category identity, strict quotient reassociation,
unit-preserving Koszul comparison, constructibility transport with witness data, and
naturality on arbitrary arrows.

Edge cases checked before writing: the empty scheme is permitted by the structure-map
hypotheses and has the same zero-category constructions. Zero integral objects and zero
arrows are allowed; no nonvanishing or invertibility of input arrows appears. Identity
arrows and equal input objects are covered. The first tower index is exponent 1, so
there is no unintended exponent-0 quotient. The case `a=1` and every pair of distinct
primes is covered by the datum. Ramified finite coefficient fields use their actual
uniformizer; no unramifiedness is assumed. No common cohomological interval is imposed
on the two inputs. The generator tuple has length one because the recorded ideal is
principal, with its generation equality given by `wfUniformizer_generates`. The site
and coefficient size conventions are the existing ones and were checked by the server
compiler with auto-implicit variables disabled.

Searches for an existing complete statement:

- `msearch.py leanfinder`, query "ordinary derived tensor of bounded constructible adic
  sheaves has an invertible Koszul completion unit agreeing with the quotient completion
  unit": returned ordinary module results `AdicCompletion.ofTensorProduct*`,
  `tensor_map_id_left_eq_map`, and `BDeRhamPlus`; none states the derived-sheaf result.
- `msearch.py leansearch`, query "bounded constructible adic sheaf derived tensor is
  complete and its quotient and Koszul completion units agree": returned ordinary
  `AdicCompletion` module/tensor results only.
- `msearch.py loogle`, query `AdicCompletion.ofTensorProduct_naturality`: one ordinary
  module-completion naturality lemma, not a derived constructible assertion.
- `msearch.py grep`, query `Koszul.*tensor|constructible.*[Tt]ensor|[Tt]ensor.*[Cc]ompletion`:
  five ordinary adic-completion tensor hits in Mathlib, no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, for the item id, constructible/Koszul
  combinations, and proposed declaration names: no existing statement of all clauses.
  `WfTensorCompletion.integral` already states the constructibility/unit-naturality
  portion, but lacks the natural ρ and its actual quotient-unit equation and the
  explicit category/reduction identification, so it is not an existing match.
  `ProjectionWeilTensorDomainBridge` cites this item in its proof docstrings and is a
  consumer, not its statement. All canonical constructions found were reused.
- `rg` of the three new declaration names in Mathlib, upstream project, project modules,
  and `dag/lean_names_upstream.json`: no name collision.

Sources read: the current `literature/blueprint/latest` projection-formula proof,
Stacks `proetale.tex` at `lemma-naive-completion` and `algebraization.tex` at
`lemma-derived-completion-koszul`, the node and every statement-dependency record and
its declarations/docstrings. No statement correction or mathematical dispute was needed.

Validation: `scompile.py Q93 lem-wf-constructible-tensor-koszul-unit` compiled the module
as a sandbox and at its library path, with no errors or warnings. The first probe found
that `pbcConstantReduction` needed an explicit public import of its owning module; that
was added. A subsequent section-inclusion syntax error was repaired by putting
`include hsep` before the docstrings. All three final proofs are exactly `by sorry`.


## Repair of returned delivery

The immutable-head review required ownership-correct statement dependencies. I replaced
`lem-weil-pbc-integral-stratified-perfect-characterization` with its actual definition owner
`def-sfb-integral-completed-coefficient-transport`, and made its module public. I added the
reflector owner `lem-weil-pbc-ringed-koszul-completion-reflector` to `stmt_deps` and made
`Sheaf.Paper.WeilCompletedTensorReflector` public. I also cited the direct owners of every
notation used in the public signatures: `def-weil-derived-complete-integral-detailed` for
`sfIntegralConstructible`, `def-weil-integral-derived-reduction` for
`scalarReductionDerivedExtension`, `def-weil-pbc-bounded-constructible-tower` for
`pbcDerivedRestrict`, and `def-pur-completed-rlim-functor` for `completedRlim`.
The statements and proofs are unchanged.


## Repair of head 095b8ba0967b

Replaced `prop-weil-pbc-rlim-functoriality` in `stmt_deps` with the existing definition
owner `def-pur-completed-rlim-functor`. Its `existing: true` record names exactly
`AlgebraicGeometry.Scheme.completedRlim` in `Sheaf.Paper.CompletedRlimFunctor`. Reading
the full declaration confirms that this is the total right derived functor of the actual
`completedTowerLimit`; the public signature does not use its computation or Roos theorems.
The public import of `Sheaf.Paper.CompletedRlimFunctor` remains. The Lean file, item
statement, proof dependencies and recorded Lean signature are unchanged from the returned
head. This is a dependency-owner correction, not a statement correction or unchanged push.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence` states
`AlgebraicGeometry.Etale.immersionEvaluationCoherence`, with `sorry` as its entire
proof. One real helper construction packages the five-arrow comparison. The two
evaluation-normalized stratum isomorphisms are explicit data with their exact
normalization hypotheses. No new DAG notion, dependency
repair, or statement correction is needed.

The source is Stacks `sites-cohomology.tex`, Tag 08J9 and equation 08J8, together
with the six-step cartesian mate calculation in this node. The local source was
opened at lines 8830–8945: it gives the tensor-Hom transposition bijection and its
Yoneda uniqueness for ordinary unbounded ringed-site derived categories.

Hypothesis and clause correspondence:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`; all six schemes are `Scheme.{u}`. This is the recorded small-etale
  coefficient size convention, including every finite ring up to the usual lift.
- The fixed factorization is `i : S ⟶ U`, `j : U ⟶ X`, with
  `[IsClosedImmersion i] [IsOpenImmersion j]`; the primed pair has the same two
  properties. Thus `s = i ≫ j` and `s' = i' ≫ j'`. No separate arbitrary immersion
  functor is substituted.
- Cartesian pullback of this factorization is `hi : IsPullback gS i' i gU` and
  `hj : IsPullback gU j' j gX`. Their pasted commutative square is used for exchange.
  Giving the induced two pullback squares is precisely giving the pulled-back
  factorization; it adds no condition on the original immersion or `gX`.
- Ordinary unbounded categories are `DerivedCategoryModule A T`, definitionally
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  `P` and `M` have exactly the stratum and ambient types in the node; there are no
  boundedness, constructibility, perfectness, smoothness, or field hypotheses.
- `Rs_!` is the dependency's `immersionLowerShriek A i j`; `Rs^!` is
  `immersionUpperShriek A i j`; `Rs_*` is `R((i ≫ j)_*[ModuleCat A])`.
  The corresponding primed functors use `i'`, `j'`. `H` is expanded as
  `((derivedHom ... S).obj (op P)).obj ((immersionUpperShriek A i j).obj M)`.
- Derived tensor is the existing `derivedTensor`, on morphisms `derivedTensorHom`;
  derived internal Hom is the existing `derivedHom` with its tensor adjunction.
  These are the existing six-functor encoding of precisely the two dependency
  notions, also used in the stratum-mate dependency. The general
  `derivedInternalHomOfUniverses` module remains publicly imported through the
  projection dependency; its different `SheafOfModules` carrier is not silently
  substituted for constant-coefficient `DerivedCategoryModule`.
- All scheme inverse images use `L(upperStar ...)`; the constant-coefficient
  inverse image is exact, so this is the canonical unbounded inverse image,
  identified with the termwise `D(upperStar ...)` used inside `immersionUpperShriek`.
- `b` is exactly `immersionLowerShriekBaseChangeMap A hi hj`: the canonical open
  extension-by-zero inverse mate followed by finite closed exchange. The
  dependency `immersionProjectionFormula` supplies its invertibility.
- `e_H` is `derivedBaseChangeMap ... (hi.toCommSq.vert_comp hj.toCommSq)` at `H`.
  It is the adjunction mate of `derivedSquareUpperStarIso`, never an arbitrary map.
  For module coefficients this is the original tensor-compatible exchange;
  `exactDerivedBaseChangeMap` is the same exchange transported to termwise exact
  inverse images, and its module is retained as a proof-dependency import.
- The exceptional comparison is the explicitly typed morphism `a`. `hCounit`
  is exactly `b_N ≫ Rs'_!(a) ≫ ε' = gX^*(ε)`, the node's exceptional counit
  identity written in Lean's left-to-right composition order.
- `hProjection` is the canonical projection compatibility assumption for all
  `C,Q`, written verbatim in the orientation of the final equality of
  `immersionProjectionFormula`. It uses the dependency's
  `immersionProjectionBaseChangeTensorMap`; no independently chosen square or
  tensor identification is introduced. Projection invertibility is already
  supplied by that dependency rather than added as another hypothesis.
- `θ` and `θ'` bind the two stratum-Hom isomorphism components specified in the
  node. `hθ` and `hθ'` are exactly the universal tensor-transpose characterization
  of `immersionInternalHomIso`, at the fixed pairs `(P,M)` and `(gS^*P,gX^*M)`.
  They quantify over every test object and every map into the ordinary direct
  image. These equations uniquely determine the two isomorphisms by injectivity
  of transposition and Yoneda; the recorded dependency supplies them. Thus these
  binders spell out the node's "evaluation-normalized isomorphisms", rather than
  adding hypotheses on the schemes or complexes or using arbitrary isomorphisms.
  Binding the specified data avoids the kernel's expensive checking of a new
  `Classical.choose` wrapper around the dependency's large existential theorem.
- `immersionEvaluationComparison` has exactly the five arrows in the node:
  `gX^*(θ.hom)`, `e_H`, `Rs'_*(β)`, `Rs'_*(Hom(1,a))`, `θ'.inv`.
  The inner β is spelled out using `derivedTensorHomAdjunction.homEquiv` applied
  to the inverse canonical `leftDerivedUpperStarTensorIso` and pulled-back
  adjunction counit. Thus β is the actual transpose of evaluation, with real data.
- The first conjunct states that tensoring with `b_P`, then transposing the
  composite using `immersionHomEvaluation`, equals the inverse tensor pullback
  identification followed by `gX^*` of original evaluation. This is precisely the
  requested tensor-transpose identity.
- The second conjunct is the claimed equality with canonical β. Its left side
  composes the five-arrow map with `(derivedHom ...).map b_P.op`, evaluated at
  `gX^*M`. This makes the first Hom input `gX^*Rs_!P`, exactly the identification
  required in the node. Its right side is the literal canonical β transpose
  formula. Without this input identification the raw displayed β and composite
  would have different codomains; the node's explicit identification resolves it.
- The theorem assumes no `IsIso` for `e_H`, `a`, or the inner β; it never inverts
  any of these. There is no hidden arbitrary map or extra isomorphism hypothesis.

Dependency declarations read and used (full signatures/docstrings were opened):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, with its carrier in the imported Coefficients
  module; the current source was retrieved with `scompile.py --source` because
  the old local checkout lacks this promoted module.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its K-injective-model
  comparisons; used through the existing etale specialization in the stratum API.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and `.Hom`:
  `derivedTensor`, `derivedHom`, `derivedTensorHomAdjunction`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; current source retrieved with
  `scompile.py --source`, retaining its exact constant-ring module interface.
- Mathlib `AlgebraicGeometry.Morphisms.ClosedImmersion` and
  `AlgebraicGeometry.OpenImmersion`: `IsClosedImmersion`, `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and Mathlib pullbacks:
  the fiber-product convention, rendered as `IsPullback` for arbitrary chosen
  cartesian squares; current promoted source read with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`:
  `exists_functorial_distTriang_openClosed` and the imported exact open extension
  by zero. Its bounded-below triangle is not imposed on the present categories.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, supplying the exact
  ordinary unbounded adjoint used in the dependency's `immersionUpperShriek`.
- `Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection`:
  `immersionLowerShriek`, `immersionProjectionMap`,
  `immersionLowerShriekBaseChangeMap`, `immersionProjectionBaseChangeTensorMap`,
  `immersionProjectionFormula`.
- `Sheaf.AlgebraicGeometry.EtaleGenericStratumMate`:
  `immersionUpperShriek`, `immersionLowerUpperShriekAdjunction`,
  `immersionHomEvaluation`, `immersionInternalHomIso`.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `derivedBaseChangeMap` and its defining square/adjunction mates.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarTensorComparison`.

The stated proof dependencies with usable modules are imported, directly or
through the statement dependencies. `lem-sfb-ringed-derived-monoidal-comparisons`
has no Lean record, so no module import can be added for it. This is a proof-only
prerequisite; the current statement needs no missing object from that theorem.
The six steps in the docstring preserve the node's full proof plan.

Edge cases checked: empty stratum and empty ambient scheme; zero `P` or `M`;
the zero finite commutative ring; identity closed/open factorization; identity
base change; unrestricted unbounded complexes and arbitrary scheme morphisms.
All remain admitted by the binders. The zero/empty cases give the same typed
zero evaluation identities. No nonemptiness or nontrivial-ring hypothesis is used.

Searches for an existing statement and definitions:

- `msearch.py leanfinder`: “Evaluation coherence of the immersion stratum internal
  Hom base change comparison with exceptional counit and projection formula”
  returned only open-immersion structure-sheaf identities, not this statement.
- `msearch.py leansearch`: “Evaluation coherence of derived internal Hom base
  change and the stratum adjunction for an immersion” returned `ihom.ev`,
  `ihom.ihom_adjunction_counit`, evaluation naturality and unrelated hits.
- `msearch.py loogle`: `"mate", "evaluation"` returned rigid-category dual-mate
  identities requiring dualizable objects, not this unrestricted internal-Hom
  assertion.
- `msearch.py grep` of Mathlib:
  `(internalHom.*baseChange|baseChange.*internalHom|exchange.*evaluation)`:
  zero hits.
- `rg` of upstream `WeilConjectures` for the node id: zero hits; of the etale
  derived sources for Hom comparison/pullback: no immersion coherence theorem.
  Reading `Derived/Hom.lean` and `Derived/UpperStarMonoidal/Comparison.lean`
  located the actual Hom adjunction and canonical tensor maps used here.
- `rg` of `lean/Sheaf` for evaluation coherence and immersion internal Hom found
  the stratum-mate dependency, not this theorem. Searching etale generic files
  located `inverseImageHomExchange` in the downstream
  `EtaleGenericExchangeAlgClosed` module. Its full construction was read, also
  confirmed by `scompile.py --source`; the β formulas in this delivery use that
  identical adjunction/tensor expression inline. Importing the downstream
  theorem's module would make an import cycle when it imports this proof
  prerequisite, so this delivery neither imports it nor defines a second β.
- `rg` of upstream-name inventory, upstream source and side source for the candidate
  declaration names returned zero hits before writing.

No `STATEMENT-DISPUTED` flag or node fault was found. The natural statement is
unchanged. Compilation and preflight results are recorded below after checking.

## Second reading by Q109

The worker reread the node against the final source: the ring, both factorizations,
two cartesian squares, `P,M`, arbitrary `a`, exceptional counit equation, and full
projection compatibility occur in the theorem's binders. The two conclusions
retain both the tensor-transpose identity and equality of the actual canonical
maps. Contravariance of Hom on `b_P` is essential for the second equality's typed
codomain. The inner β and outer β use the same left-tensor evaluation transpose;
the first conclusion uses the dependency's right-ordered evaluation through its
canonical symmetry. The specified θ and θ' have exactly the dependency's universal
normalization hypotheses, so are uniquely determined. No extra boundedness or isomorphism assumptions
were found. This is the worker's consistency reread, not an independent worker
review; per the current brief the maintainer supplies the independent review.

Validation: `scompile.py Q109 lem-sf-etale-generic-evaluation-coherence
lean/Sheaf/AlgebraicGeometry/EtaleGenericEvaluationCoherence.lean` passed both the
sandbox check (33.5 seconds) and the library-module check (28.8 seconds), with no
errors or warnings. The default 60-second limit and default heartbeat limit were
retained. Earlier wrapper experiments were confined to `scratchpad/`; the final
module has no profiling options, chosen-isomorphism wrapper, or diagnostic code.

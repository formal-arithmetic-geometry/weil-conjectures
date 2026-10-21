## Worker report

Item: `lem-weil-isomorphism-comparison-natural`. Group: Q119. Date: 2026-10-21 UTC.

The new module `Sheaf.Paper.IsomorphismComparisonNatural` states the finite and
integral cases in two theorems, each with proof `sorry`. There are no definitions,
new nodes, dependency repairs, or changes to the mathematical node. Only its `lean`
record changes. No statement fault or dispute was found.

### Hypotheses and objects

Both theorems explicitly bind `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]`,
`[Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. These are the prime and finite
coefficient extension in the node. The coefficient constructions, including the
valuation ring, its fixed uniformizer, quotient rings and transitions, are exactly
those of `Padic.coefficientExtensionRing` and the recorded completed-coefficient
modules; no coefficient system is supplied as an extra parameter.

`{X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]` is the given scheme isomorphism.
`hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` and the analogous `hY` express
invertibility of l on both schemes. There are no geometric finiteness, separation,
constructibility or completeness hypotheses.

The existing categories `integralOperationsFiniteModules l E W n` and
`integralTowerModules l E W` use `Scheme.ProEt.topology W` on `W.ProEt` and the
constant quotient sheaf and actual limit coefficient sheaf, respectively.
`DerivedCategory` is the ordinary unbounded localization. Site universe `t` and
coefficient universe `u` stay independent. The existing module categories have
object size `max (t+2) (u+1)` and morphism size `max (t+1) u`, and the existing
standard localizations retain these sizes. No equality of site object and morphism
universes is imposed. All universes and parameters are explicitly bound;
`set_option autoImplicit false` enforces this.

### Every finite clause

`inverseImagePullbackComparisonFinite_natural` binds `(n : ℕ)`; in the recorded
construction this means quotient exponent n+1. Thus it covers exactly all positive
exponents, including the residue-field level n=0.

The conclusion supplies
`κ : inverseImageFiniteDerived l E g n ⟶
(integralOperationsLevelPullback l E g n).mapDerivedCategory`.
The source is the exact module inverse image with scalar action through c_A inverse.
The target is the canonical coefficient-sized module pullback, derived by exactness.
It is the finite derived pullback in the node. In particular this avoids restricting
E to `Type t` just to use the older intrinsic-presentation name `finiteDerivedPullback`.
The dependency's `inverseImageFiniteIntrinsicPullbackComparison` identifies these
presentations whenever that older name is applicable.

The first conjunct fixes `κ.app (DerivedCategory.Q.obj K)` to
`inverseImagePullbackComparisonFinite l E g hX hY n K` for EVERY complex K.
That recorded map is the localized `inverseImageFiniteComparisonComplex` transported
through `mapDerivedCategoryFactors` on its two ends. Its sections are the sheafified
x tensor 1 maps, as fixed by `inverseImageFiniteComparison_existsUnique`; its data
are reused and never replaced by arbitrary components. A morphism of functors is a
natural transformation, so its `naturality v` says
`G.map v ≫ κ.app N' = κ.app N ≫ P.map v`, exactly the node's displayed square in
Lean composition order. This quantifies over ALL derived morphisms. It includes
`Q.map` of chain maps and `inv (Q.map w)` for every quasi-isomorphism w, not merely
maps of chosen complexes. Equality on every Q(K), together with essential
surjectivity of Q, fixes the transformation on the entire derived category.

The second conjunct binds any `(T : Type r) [Category.{s} T]`, the node's S and H,
and `ρ : H ⟶ G ⋙ S`. It gives `η : H ⟶ P ⋙ S` whose components are precisely
`ρ.app N ≫ S.map (κ.app N)`. This is the final consequence in the node, with
unrestricted target object and morphism universes r and s.

### Every integral clause

`inverseImagePullbackComparisonIntegral_natural` supplies
`κ : inverseImageIntegralDerived l E g ⟶ integralDerivedPullback l E g`.
The former functor transports the action through the inverse of the constructed
limit coefficient map; the latter is exactly the ambient completed pullback.
The first conjunct fixes every component to
`inverseImagePullbackComparisonDerived l E g hX hY N`, the recorded choice of
representative and K-flat resolution, conjugated through its representative iso.
Its `naturality` is the displayed equation for every ambient derived morphism.

The second conjunct states equality at Q(K) with
`inverseImagePullbackComparison l E g hX hY K P q` for EVERY good complex P and
quasi-isomorphism q : P.obj ⟶ K. This fixes the same entire-cone map under all the
canonical resolution comparisons: that definition already composes the inverse
of G(Q(q)), the actual zero-homotopy Roos lift, and the normalized representative
identification with completed pullback. Equality is of entire derived morphisms,
not just equality after finite projections. The resolution is only a representative
of the arbitrary ambient object and does not restrict that object.

The third conjunct expresses the normalization clause. For each coherent recorded
`C : CoefficientDerivedSystemCalculus l E Y`, it gives a natural isomorphism
`θ : integralDerivedPullback l E g ≅
(C.reduction ⋙ coefficientSequenceLimit l E Y) ⋙ inverseImageIntegralDerived l E g`
and the equation
`κ.app N = G.map (C.adjunction.unit.app N) ≫ θ.inv.app N` for every ambient N.
The completion is exactly simultaneous reduction followed by the specified strict
system limit, and u is the actual adjunction unit. The existence/coherence theorem
for C is already `coefficientDerivedSystemEvaluationCalculus`; coherence is bound
inside this normalization conjunct and is not an additional hypothesis on κ or N.
The normalization theorem dependency supplies precisely this family of θ
isomorphisms and its naturality; packaging that family as a natural isomorphism
changes no mathematical content. The specified κ and its resolution formula are
retained, including the zero shifted-coordinate convention. No inverse of u and
no isomorphism claim for κ on incomplete N occurs.

The fourth conjunct is the same arbitrary T, S, H, ρ consequence as at finite level,
with components `ρ.app N ≫ S.map (κ.app N)` on the whole ambient category.

### Dependencies read and used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its public coefficient constructions.
- `def-weil-scheme-morphism-properties` and `def-weil-size-convention` are convention
  records without declarations; scheme isomorphism, stalk units and universes are
  bound directly using Mathlib and the existing site/module categories.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `AlgebraicGeometry.Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, with its actual quotient
  cone and `completedIntegralCoefficientSheafUnrestricted` retained publicly.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived` and the publicly
  retained `inverseImagePullbackComparison`, `inverseImagePullbackComparisonFinite`,
  `inverseImageFiniteDerived`, `inverseImageIntegralDerived`, and the coefficient
  maps/module inverse images. Read the full original comparison module as well.
- `Sheaf.Paper.DerivedPullbackTensorHom`: its finite/integral construction imports,
  with the recorded `commonStageDerivedInternalHom_existsUnique` signature/docstring
  also checked. The rational/common-stage portions are not part of this item.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: recorded
  `WeilConjectures.IntegralOnSlice.completedTensor` signature/docstring read; the
  ambient `WeilConjectures.integralDerivedPullback` and
  `integralDerivedPullbackComparison` from its public construction are used here.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`:
  `WeilConjectures.isomorphismDerivedPullbackComparisonNormalization`; its full
  signature gives the normalization and naturality on ALL ambient objects. Its
  extra complete-object argument only supplies the separate inverse assertion;
  it does not restrict the ambient θ family used in this item's proof plan.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.CoefficientDerivedSystemCalculus`,
  `CoefficientDerivedSystemCoherence`, `coefficientDerivedSystemEvaluationCalculus`,
  `coefficientSequenceLimit`, and the actual `adjunction.unit` field.
- Proof imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
  (`SheafOfModules.cochainModulesMonoidal`),
  `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
  (`AlgebraicGeometry.ProEtale.finiteCoefficientModulePullback_exact`),
  `Mathlib.CategoryTheory.Sites.Sheafification` (`presheafToSheaf`,
  `sheafificationAdjunction`), and `Mathlib.CategoryTheory.Localization.Predicate`
  (`Localization.lift`, `fac`, `liftNatTrans`, `liftNatTrans_app`, `natTrans_ext`).
  The last node is a Mathlib leaf whose `mathlib_match` gives these declarations;
  its absent `lean` record does not require a repair.

The source of the entire ambient comparison is explicitly agent-written in the
node. I read its blueprint motivation
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`
and the normalization's source
`main-20261015/blueprint/sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
clauses (2)--(3). The docstrings distinguish these constructions from Deligne's
motivating statements and carry the complete relevant node proof steps.

### Edge cases checked

The finite n=0 index is exponent 1, not exponent 0. All levels are covered.
Zero objects, zero complexes and the empty scheme are permitted by all binders;
invertibility on an empty scheme is vacuous as it should be. Identity isomorphisms
and arbitrary unbounded derived morphisms are permitted. The comparison is not
assumed invertible at integral coefficients: for incomplete objects it is
G(u) followed by θ inverse, so the completion obstruction remains visible.
No boundedness, constructibility, perfectness, or derived completeness assumption
was introduced. Independent site/coefficient and arbitrary target category
universes were preserved. No chain-map-only or finite-projection-only replacement
of the naturality assertion was made.

### Searches and validation

All remote searches used `msearch.py Q119 lem-weil-isomorphism-comparison-natural`:

- `leanfinder`: "Naturality of the specified tensor unit inverse image to derived
  finite or completed pullback comparison for a scheme isomorphism on the ambient
  unbounded pro etale derived category". Eight hits, beginning with
  `AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality` and
  `pseudofunctor_left_unitality`; none states the finite/completed pro-etale
  comparison. They concern ordinary scheme-module pullback coherence.
- `loogle`: `Functor.mapDerivedCategoryNatTrans, Localization.liftNatTrans` initially
  returned zero hits with unknown identifier `Functor.mapDerivedCategoryNatTrans`.
  Retried with `CategoryTheory.Localization.liftNatTrans`: ten hits, the localization
  lift and its identity/composition/app lemmas. These are the existing generic
  descent tool, not this coefficient comparison.
- `grep`: `liftNatTrans|mapDerivedCategoryNatTrans` in Mathlib `CategoryTheory`:
  25 hits, including `Localization/Predicate.lean:326,332` and its consumers.
  Read the lift/app/uniqueness signatures and docstrings directly.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`: inverse-image comparison
  and naturality patterns, the item id, and both proposed declaration names.
  The comparison definition, normalization lemma and its integral consumers exist;
  no finite/integral naturality theorem for the specified components exists.
- `rg` for both proposed names in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no declaration-name collisions.

Required `scompile.py` validation compiled the module separately as sandbox and
library module: clean, no warnings/errors (12.8 s sandbox, 6.4 s library on the
first pass). All subsequent validation and delivery use the same prescribed wrappers.
No shared source was changed and no Git command was run directly.

## Second reading by Q119

After the first clean compile I reopened the node, dependency signatures and the
whole delivered Lean file. This is a worker self-check; the dispatcher explicitly
forbids starting other agents, and the maintainer supplies the independent review.

The finite conclusion is pinned on every complex to the existing section-normalized
map, so the existential transformation cannot be replaced by an arbitrary map.
The integral component equation is pinned to the existing derived construction,
and the resolution conjunct quantifies over every P and q, rather than merely the
worker's chosen resolution. The θ equation uses the actual C.adjunction.unit and
an isomorphism of functors; it leaves incomplete objects in scope. Both composition
clauses have precisely the order ρ_N then S(κ_N). Object sizes and morphism sizes
remain independent, including arbitrary target category universes. All geometric
and coefficient assumptions match the node. I added explicit imports of every
recorded statement-dependency module, including the conventions' underlying
Mathlib site/derived-category modules. No mathematical statement correction was needed.

## Worker report

Repaired the returned H3 packet rather than re-pushing its arbitrary existential
adjunction predicates. The item is stated by
`WeilConjectures.PurityFiniteSetting.finiteClopenExceptionalRestriction` in
`Sheaf.Paper.FiniteClopenExceptionalRestriction`. The associated definition module
`Sheaf.Paper.ClopenStrictSystemComparison` gives the actual comparison packages and
normalization equations. Only the item's final theorem has a postponed proof; its
docstring contains all eleven natural-language DAG proof steps. Definitions and
instances contain actual data or invoke recorded, object-determining constructions.
No statement correction is made.

Hypotheses and clauses, read against the node:

- `P : PurityFiniteSetting` supplies the algebraic closure of a finite field, the
  distinct prime, the finite coefficient extension, valuation ring and uniformizer.
  The positive coefficient levels are explicitly `n + 1` for every `n : ℕ`.
- `X Y : Over (Spec (.of P.field.k))` and the locally-finite-type/quasi-compact
  instances express finite-type k-schemes. `g.IsOver`, `IsSeparated g`,
  `LocallyOfFiniteType g`, and `QuasiCompact g` express a separated finite-type
  morphism of these k-schemes. Component finite-type instances express the inherited
  finite-type property of the clopen subschemes; they add no geometric restriction.
- `{I : Type w} [Finite I]`, the family `Xi`, the morphisms `j`, open and closed
  immersion instances, `hdisjoint` and `hcover` express exactly the finite disjoint
  clopen cover. Every component morphism is literally `(j i).left ≫ g`.
- The first conjunct quantifies over every `n : ℕ` and compactification `c` and is
  a natural isomorphism from the canonical compact-support functor, restricted to
  bounded constructible inputs, to `finiteBiproductFunctor` of the actual component
  pullback/compact-support functors. `c.precomp (j i).left` keeps the proper part
  unchanged. The biproduct is pointwise categorical, including its maps and empty sum.
- The second conjunct supplies `ClopenExceptionalAllCoefficients` for every
  compactification and component. Its `base.finite n` is the natural finite-coefficient
  exceptional comparison on all bounded constructible inputs, not just reductions of
  integral inputs. `base.finiteMate n` identifies it with the right-adjoint comparison:
  the restriction, compact-support and exceptional functors are lifts of the recorded
  functors (their formula isomorphisms are fields), insertion is both adjoints of
  restriction with normalized unit, and `ClopenCounitComparisonCoherence` is precisely
  the node's counit equation. the `comparisonMap` conjunct of `ClopenFiniteAdjointComparisonCoherence`
  identifies the displayed finite map with this comparison after the inclusions.
- `StrictClopenExceptionalComparison` uses the recorded actual strict etale system
  categories, with component inverse image and direct image from
  `CoefficientSystemDerivedImage`. It includes the system comparison and every level
  comparison. Its coherence equation says evaluation of the system map is the finite
  map after the specified evaluation isomorphisms, including the target evaluation
  identification. `StrictClopenCompactSupportNormalization` fixes the compact-support
  map by the common proper direct image of open-extension composition: its right mate
  is the canonical restriction composition, normalized on underlying finite-level
  sheaves and termwise localization. It also fixes the reverse clopen adjunction unit
  to the inverse of the ordinary restriction counit.
- `ClopenSystemComparison` reuses the complete recorded etale/pro-etale ordinary and
  derived system interfaces. `ClopenSystemSquare` retains the ordinary square, its
  finite evaluations, the underlying geometric comparison-pullback equation and the
  derived localization equation. Thus the site comparison commutes on actual system
  arrows, not merely on the isomorphism classes of their evaluations.
- `ClopenSequenceRealization` identifies those strict systems with the actual ringed
  sequence site. The ring isomorphism is fixed on constant quotient generators;
  scalar restriction leaves underlying sections unchanged; evaluation and transitions
  commute; the derived realization factors through the ordinary termwise functor.
- `clopenExceptionalSystem` is explicitly the composite of the actual single-K-flat
  reduction system, sequence realization, derived comparison direct image, strict
  etale exceptional functor, comparison inverse image and sequence realization.
  The `systemMap` equation identifies its component comparison with the strict-system
  comparison and geometric square. `finiteSystemMap` identifies evaluation of this
  very system morphism with `finite n` on the constructible reduction.
- `integral` and `integralI` take values in the recorded integral constructible
  categories; `integralFormula` and `integralFormulaI` identify their inclusions with
  this actual system functor followed by `coefficientSequenceLimit`. That recorded
  functor first restricts scalars on strict systems and then applies the total derived
  inverse limit. The `inverseLimitMap` equation requires the integral comparison to be
  the image of the system morphism under that functor, using the displayed restriction
  comparison. There is no lift of a diagram specified only in an ordinary derived
  category, and no separate arbitrary tower or inverse-limit object.
- The rational functors have the integral functor's objects and the exact pure-tensor
  map formula `a ⊗ f ↦ a ⊗ integral.map f`. The `rationalComparisonMap` equation fixes
  their component comparison to the scalar localization of the integral comparison.
- For algebraically closed coefficients, `stage` supplies this same normalized
  package at every finite coefficient subfield. `action`, `actionI`, their stage
  identifications and their scalar-mate equations fix the transition comparisons to
  the counit mates of the recorded compact-support coefficient action. The latter
  includes identity and composition coherence. `commonStageMap` identifies the
  comparison on an actual pair with the same-stage representative of
  `stageComparison`, including the identity transition. Thus common-stage descent
  concerns the actual representative morphisms, as required by the source.
- `finiteUnitComparison`, `integralUnitComparison`, `rationalUnitComparison` and
  `commonStageUnitComparison` evaluate these very natural isomorphisms at the actual
  coefficient unit on Y. Their sources are pullbacks of the exceptional image of that
  unit, and their targets are the component exceptional images of that same Y-unit.
  They are exactly the stated dualizing-object comparisons.
- There is no smoothness, purity orientation, section or tensor-invertibility binder.

Recorded dependencies reused (module and declaration):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- Mathlib `Morphisms.Proper`, `Morphisms.FiniteType`, `OpenImmersion`,
  `Morphisms.ClosedImmersion`: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback` and the recorded
  common-stage pullback, through `P.clopenCommonStagePullback`.
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`:
  `finiteClopen_constructible_equivalences`, `clopenResidue_isUnit` and the actual
  integral/rational/common-stage units and restrictions.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `ProEtale.rightDerivedLowerShriekOfCompactification`; its intrinsic-coordinate
  presentation is `Scheme.sfIntrinsicCompactSupport` in
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `ProEtale.sfFiniteExceptionalAt`;
  `Scheme.finiteExceptionalInverseImage` is used in intrinsic coordinates, with an
  explicit fixed-compactification comparison in `fixedFiniteFormula`.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`: `StrictEtaleCompactSupport`,
  `StrictEtaleExceptionalAdjoint`, their functors, adjunctions and evaluations.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `CoefficientSystemOrdinaryImage`, `CoefficientSystemDerivedImage`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceDerived`,
  `coefficientSequenceDerivedEvaluation`, `coefficientSequenceLimit`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, whose reduction is the actual strict
  reduction system used here.
- `Sheaf.Paper.CompactSupportCoefficientAction`: `SfCompactSupportCoefficientAction`.
  `StageSystem.Morphism.functor` and `PairCategory.mkHom` give the genuine common-stage
  functor and representative, rather than an existential adjunction predicate.

Edge cases: `Finite I` allows `I` empty; `hcover` then forces X empty and the first
conclusion has the empty biproduct. Empty individual components are allowed and give
zero factors. All finite positive levels occur, including level one (`n = 0` in the
code). Arbitrarily large finite index types use the independent universe `w`. The
small sites retain object universe `u + 1` and morphism universe `u`; the coefficient
ring is lifted to `u + 1` and the system derived categories use `u + 2`. No universe
equality has been added. Identity coefficient extensions are included in the
common-stage coherence, and coefficient units are on the target Y throughout.

Searches retained from the saved packet and checked during repair:

- LeanFinder, "finite clopen cover exceptional inverse image restricts componentwise":
  eight unrelated finite clopen/topological partition hits; no matching statement.
- Loogle, "sfIntrinsicCompactSupport, finiteExceptionalInverseImage,
  finiteDerivedPullback": zero hits (the custom first name is unknown to Loogle).
- Mathlib grep, "exceptional.*clopen|finiteClopenExceptionalRestriction": zero hits.
- LeanFinder, "normalized clopen exceptional inverse image comparison on strict
  coefficient systems and etale proetale comparison": eight unrelated algebraic
  geometry normalization or etale-pair hits, no comparison package.
- Loogle, "StrictEtaleCompactSupport, CoefficientSystemDerivedImage,
  ClopenSystemSquare": zero hits (custom identifier unknown).
- Mathlib grep, "StrictClopenExceptionalComparison|ClopenSequenceRealization|
  ClopenSystemSquare": zero hits.
- LeanSearch, "strict coefficient systems clopen restriction exceptional adjoint
  counit comparison": generic monadicity, representation restriction and scheme
  module adjunction results; none state this comparison.
- `rg` of the named source tree and shared `lean/Sheaf` for these new declarations:
  no duplicates. `blueprint_refs.py search "clopen strict"`: zero blueprint nodes.
  DAG text search finds the present theorem, system adjunction and decomposition
  nodes, all of which are reused, but no existing normalized comparison definition.

No `STATEMENT-DISPUTED` finding and no source-statement correction.

## New nodes

`def-pur-clopen-strict-system-comparison` owns
`Sheaf.Paper.ClopenStrictSystemComparison`. It defines normalized comparison data
for the actual strict-system, finite-evaluation, geometric comparison-site and
sequence-site presentations, with the counit, quotient-generator and termwise
localization equations from proof steps 4--9 of this item. It does not assert their
existence. It is required to express the source's compatibility clauses, which the
returned packet had replaced with arbitrary adjunction predicates. Its searches are
recorded verbatim as JSON results, including LeanSearch, LeanFinder/Loogle and grep;
the existing system adjunction and clopen decomposition notions remain dependencies.
This fixes the saved packet's unowned-module failure: each module now belongs to
exactly one node, and the item cites the new definition node.

## Second reading by Q66

Reread both modules, the item and its eleven proof steps, the dependency records and
the blueprint source. The saved report claimed all coefficient comparisons while
its delivered head used arbitrary adjunction predicates; it also lacked an owning
record for the retained helper module. The repaired packet has actual strict-system
functors and comparison morphisms with counit and evaluation equations, a geometric
comparison-site square, scalar restriction and derived-limit map equations, pure-tensor
rational map equations, and common-stage representative and scalar-mate equations.

A further mismatch found on this reading was that the compact-support conclusion
only displayed P.level. It now quantifies explicitly over every positive level.
The finite natural isomorphisms now additionally carry `finiteMate`, identifying them
with the finite right-adjoint comparisons on all bounded constructible inputs. The
coefficient-unit maps evaluate the same four comparisons at Y's actual units. Empty
covers, empty components, level one and identity coefficient extensions are retained.
No hypothesis has been added to the geometric theorem. The helper's data/coherence
refactor retains every normalization equation and avoids repeated elaboration of
large dependent structure fields. No original node field outside `lean` and the
allowed added statement dependencies is changed.

Two direct proof imports, `Sheaf.Paper.CompactificationCoherence` and
`Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`, were tested and omitted because
their older upstream import path reimports the retired duplicate
`ProEtale.rightDerivedLowerShriekOfCompactification`. The diagnostic identified
`ComparisonGlobalCohomology` importing `ProEtale.Derived.LowerShriek` after the
preferred `ProEtale.FiniteCoefficient.Derived.LowerShriek` declaration. The
current finite-coefficient and intrinsic operations remain imported; the complete
proof-dependency plan and these two steps remain in the theorem docstring.

## Worker report

The module `Sheaf.Paper.ClopenRoosIntegralDescent` states the entire node as a family
of named theorems. Every theorem body is `sorry`; no theorem is proved. Its helper
constructions supply the canonical completed-coefficient transport and ordinary exact
restriction needed to state the comparisons on the actual component coefficient rings.
No statement correction, new DAG notion, or dependency-record repair is needed.

Hypotheses and clauses, in the order of the node:

- `P : PurityFiniteSetting.{u}` supplies the fixed algebraic closure of the finite
  field, the prime different from its characteristic, and the finite coefficient
  extension inside the fixed coefficient closure. Its `extension`, coefficient
  valuation ring, uniformizer, quotients and completed sheaves are the existing
  constructions. A level `n : ℕ` always denotes positive exponent `n+1`.
- `X : Over (Spec (CommRingCat.of P.field.k))`, `LocallyOfFiniteType X.hom` and
  `QuasiCompact X.hom` state finite type over the fixed field. The family `Xi`,
  arrows `j`, open/closed immersion instances, `hdisjoint` and `hcover` give exactly
  the finite disjoint clopen covering. `I : Type w` with `Finite I` permits every
  finite index type, including the empty one. No separatedness or nonemptiness
  hypothesis is introduced.
- Sites are the original `Scheme.ProEt` with object universe `u+1` and morphism
  universe `u`. Modules have section universe `u+1`; the coefficient extension
  and schemes use the common convention of `PurityFiniteSetting`. No site object
  universe is equated with its morphism universe.
- `clopenConstantMap` is the sheafification-adjunction lift of the constant
  presheaf unit along the actual open site inclusion. The uniquely characterized
  `clopenCompletionMap` commutes with every quotient projection. Its data comes
  from an existence-and-uniqueness theorem determining that very map, not a mere
  existence choice of an unspecified object. `clopenIntegralRestriction` is the
  existing sectionwise restriction followed by scalar restriction along this
  isomorphism. Its exact derived functor is ordinary unbounded restriction; it
  does not apply completion to an arbitrary restricted object.
- `finiteClopen_strict_tower_equivalence` uses `CochainComplex (ℕᵒᵖ ⥤ Mod) ℤ`:
  complexes and their chain maps at every level, with strictly commuting
  transitions. Its equivalence functor is exactly the tuple of those restrictions.
  The inverse's additive section comparison `φ` is the product over the component
  base changes. Equations specify its scalar action, site restrictions, tower
  transitions, differential and strict morphisms.
- `finiteClopen_strict_roos_comparison` gives one natural chain isomorphism `θ`.
  The product comparison is the canonical `piComparison`, so its projections are
  the restricted original projections. Its invertibility identifies the termwise
  products. The endomorphism equality identifies the two `roosU = 1-s` formulas.
  The equation in `roosχ` coordinates fixes BOTH cone summands by that same product
  comparison, with the recorded signed shifted cone. Naturality is built into the
  natural isomorphism; the `roosEval` equation retains every level projection.
- `finiteClopen_derived_roos_descent` asserts existence of the derived countable
  products and the unbounded restriction equivalence. For every transition system,
  source object, specified first map `c` and specified connecting map `δ`, it gives
  an equivalence between the original `IsDerivedLimitTriangle` and every component
  triangle. Both middle objects use the SAME projection-normalized product
  isomorphism; the last map uses its inverse and the canonical shift comparison.
  This retains the triangle, rather than asserting only an isomorphism of objects.
- `finiteClopen_augmented_reduction` is a natural isomorphism of the actual
  reduction-tower FUNCTORS, and its equation carries each canonical derived
  adjunction unit to the component unit. Tower naturality includes every transition.
  `finiteClopen_resolution_reduction` separately uses the dependency's recorded
  `canonicalIntegralReductionTower` and `canonicalIntegralReductionTowerMap` on
  a chosen K-flat resolution; its equation retains the actual `[q]⁻¹ γ_n` through
  the exact derived-localization comparison.
- `finiteClopen_integral_membership` first renders recorded derived completeness as
  `IntegralOnSlice.IsComplete ... none`, which is the original global predicate.
  That definition retains the canonical first map into the product. The next two
  equivalences are exactly `sfIntegralConstructible` and
  `finiteTorConstructibleIntegral`, with no completeness assumption on the input
  object. The final two fixed-interval equivalences quantify over EVERY positive
  reduction with the SAME `a,b`. Thus every common interval bounding the finitely
  many components, uniformly in `n`, bounds the global reductions; both cohomological
  support and Tor amplitude are stated, and the converse is included.
- `finiteClopen_integral_subcategories` gives equivalences on both actual full
  subcategories. Their compositions with component ambient inclusions are naturally
  isomorphic to the original unbounded restriction; these are not new categories
  with arbitrarily supplied predicates or arbitrary equivalences.
- `finiteClopen_completed_tensor_unit` uses the recorded
  `IntegralOnSlice.completedTensor ... none` and the existing regular completed
  coefficient object. `finiteClopen_strict_tensor_reductions` explicitly compares
  the strict reduction and total-tensor tower functors, normalized on sheafified
  scalar tensor generators and EVERY `(p,q)` total-tensor summand. As natural
  tower isomorphisms they commute with differentials, chain maps and all quotient
  transitions. This states the strict-tower computation underlying tensor preservation.
- `finiteClopen_integral_scalar_extension` uses exactly the recorded
  `integralScalarExtensionOfUniverses`. It quantifies over every finite target
  field and coefficient algebra embedding, including identity extensions and
  ramified extensions. Its second clause is a natural isomorphism of the ACTUAL
  `integralScalarTowerFunctor` strict models, normalized on every coefficient
  tensor generator via the canonical finite constant map. Taking `s=1` retains
  the level maps; naturality in the tower index retains all transitions. No
  arbitrary replacement scalar functor is supplied.
- All finite-partition theorems include the empty partition. Their hypotheses
  contain no `Nonempty I`. When `I` is empty the covering equation forces `X` to
  be empty, and the sheaf axiom gives zero module/complex/derived categories.
  Products, transitions, units and triangle assertions then concern zero objects;
  the membership predicates have interval `[0,0]`, and every ordered fixed interval
  works in the last two bound clauses. Empty individual components behave identically.

Dependency declarations and source interfaces read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  fixed field/coefficient data.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType`, `OpenImmersion`, and
  `Morphisms.ClosedImmersion`: `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsClosedImmersion`.
- Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its retained
  `CompletedIntegralCoefficients` source: `completedIntegralCommRingSheafUnrestricted`,
  `integralCoefficientCommRingSheaf`, `completedIntegralCommRingProjectionUnrestricted`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules`, `restrictScalars`, cochain complexes and derived categories
  are used directly, including the exact functor's localization factorization.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`, `towerTransitionEndomorphism`.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosU`, `roosχ`, `roosEval`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete` (global branch);
  `SfIntegralConstructible`: `sfIntegralConstructible`, its full subcategory.
- The recorded `FiniteTorAmplitudeSites` publicly retains `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral` and its full subcategory are the integral clauses
  of that very definition node. Its ordinary-etale primary declaration is not used
  as if it had an integral domain.
- `IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`; its retained
  strict-model source supplies `integralOperationsTensorTowerFunctor` and
  `integralOperationsTotalTensorSection`. `ConstantCoefficientObjectsConstructible`
  supplies `integralConstantCoefficientObject`.
- `IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`; its
  retained well-definedness source supplies `integralScalarTowerFunctor`,
  `integralScalarTensorSection`, the specified level maps and quotient transitions.
- `DerivedScalarExtensionRestrictionAdjunction`: `scalarReductionSource`,
  `scalarReductionDerivedExtension`; `IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower`, `canonicalIntegralReductionTowerMap`.
  The retained `SfIntegralReductionTower` gives the SAME normalized functorial
  reduction system `sfDerivedReductionRestricted`, `sfDerivedReductionTransition`,
  `sfDerivedReductionUnit`; there is no private copy of coefficient reduction.
- `FiniteClopenDerivedDecomposition` is imported for its existing DATA HELPERS
  `clopenSiteInclusion`, its continuity instance, `clopenRingRestriction`,
  `clopenRestriction` only. No theorem of the downstream parent is invoked to
  prove this node; no dependency edge back to the parent is introduced.
- Proof-plan imports: `ProEt.countableProducts_exact` and
  `CategoryTheory.derivedCategory_countableProducts_core`. The three recently split
  clopen proof lemmas have no recorded Lean interface locally and are not required
  to TYPE this statement; they remain the node's unchanged proof dependencies.

Sources opened: `literature/stacks-project/derived.tex`, labels
`definition-derived-limit` and `lemma-products` (Tags 08TC and 07KC), including
nonuniqueness of a bare derived-limit cone; the current main-20261015
`sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`;
Bhatt--Scholze PDF, Definitions 3.4.10 and 3.5.2 (pdftotext inspection), especially
the specified natural map in completeness. The node's ten proof steps are rendered
in the theorem docstrings at their relevant clauses.

Edge cases checked before writing: empty partition/empty scheme, empty components,
one component and identity immersion, zero towers, constant towers, zero reductions,
unequal component intervals and larger common intervals, arbitrary positive exponent,
identity coefficient extension and ramification. No mathematical statement fault or
STATEMENT-DISPUTED flag was found.

Searches actually run through the prescribed `msearch.py Q54` wrapper:

- LeanFinder: “Finite clopen restriction commutes with strict tower products and
  shifted Roos cones and detects integral derived completeness”. Eight unrelated
  profinite/condensed hits; none states this node.
- Loogle: `CategoryTheory.IsDerivedLimit, CochainComplex.mappingCone`. Zero hits;
  the service reports unknown project identifier `CategoryTheory.IsDerivedLimit`.
  The project's actual declaration was read in its recorded source instead.
- Mathlib grep: `clopen.*(Roos|roos)|roos.*(Clopen|clopen)`, subdirectory
  `CategoryTheory`: zero hits.
- Local `rg` in BOTH `lean/WeilConjectures` and `lean/Sheaf` for clopen/Roos,
  the exact node id, completed ordinary restrictions, strict reduction and scalar
  tower helpers. The parent `FiniteClopenDerivedDecomposition` has related but
  weaker statements: its strict-cone theorem lacks product/coordinate/projection
  normalization, its integral bounds assume constructible membership, and it lacks
  the arbitrary completeness and specified augmentation assertions. Thus no exact
  existing attachment covers this node. Its reusable data helpers are imported.

## Second reading by Q54

This is the author's consistency check; the dispatcher supplied one worker and
forbade subagents. The independent mathematical reading is the maintainer's review.
I checked the source node against every clause above, especially ordinary restriction
versus completed pullback, the two signed cone coordinates, the actual first triangle
map, uniform positive-reduction bounds and the empty partition. No node statement
was changed. The chosen-resolution comparison uses explicit universes from the
recorded dependency rather than adding any size equality to its hypotheses.

## Validation

The prescribed scompile.py compiled the entire module against the live server
library with no errors or warnings (sandbox 29.2 seconds; library 31.6 seconds).
The explicit named native site-smallness instance resolves coefficient-universe
inference without adding a hypothesis or changing the mathematical statement.
All declarations are listed in the node record, every variable and universe is
explicit, all source lines are at most 100 characters, and the node differs from
the read-only original only in `lean`.

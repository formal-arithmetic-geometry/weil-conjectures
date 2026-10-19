## Worker report

The module `Sheaf.Paper.BoundaryProEtaleProjectionComparison` states
`AlgebraicGeometry.ProEtale.BoundaryComparison.boundary_proetale_projection_comparison`.
Its sole theorem is postponed with `sorry`; every helper has actual data. The exceptional Hom transport and counit definitions are in the imported sibling module `Sheaf.Paper.BoundaryExceptionalComparisonData`. The helpers expose
canonical maps and the two displayed compatibility propositions. The original item statement and proof are retained; its statement dependencies gain the new helper definition node.

Hypotheses and clauses, with the node and source open:

- The global datum is `D : WeilConjectures.FiniteFieldDatum`; its `k` is the specified algebraic
  closure of the finite field, and its characteristic is `D.p`. `Fact l.Prime` and `_hl : l ≠ D.p`
  give the prime and the prime-to-characteristic hypothesis. `Field E`, `Algebra (Padic l) E`
  and `FiniteDimensional (Padic l) E` give the finite extension. Writing the coefficient level
  as `n + 1` ranges over exactly all integers at least one; it does not omit any allowed level.
  The ring throughout is the existing `Padic.coefficientExtensionRing l E (n + 1)`, with its
  canonical `ULift` to the established module/sheaf universe. Its valuation-ring ideal is the
  existing power-of-maximal-ideal presentation, equal to the uniformizer-power presentation.
- `Z.Over (Spec (.of D.k))`, `T.Over ...`, and `i.IsOver ...` give the two schemes and their
  morphism over k. On EACH structure morphism, `LocallyOfFiniteType` and `QuasiCompact` give
  finite type, and `IsSeparated` gives separatedness. `IsClosedImmersion i` is precisely the
  closed immersion hypothesis. Properness follows by the existing closed-immersion instance;
  no extra properness or ambient exceptional-adjoint hypothesis is introduced.
- The etale category is `Etale.DerivedCategoryModule (ULift A) W`; the pro-etale category is
  `DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat (ULift A)))`. These are the
  ordinary constant-module categories explicitly requested by this node, using the fixed-scalar
  presentation of the recorded coefficient realization. `comparison` is literally the existing
  `comparisonUpperStar.mapDerivedCategory`. On D+, this is the functor of
  `siteComparisonDerivedPullbackPlus`, through its standard inclusion compatibility.
- `isBoundedConstructible` is the recorded predicate: finite-value constructible cohomology
  and vanishing outside one finite interval. `finiteTorConstructibleEtale` is the already
  published etale presentation in `Sheaf.Paper.FiniteTorAmplitudeSites`: this predicate AND
  `∃ a b : ℤ, a ≤ b ∧ hasTorAmplitudeIn ... a b K`. The latter tests ALL degree-zero module
  sheaves, not just constructible ones, in one common interval. Finite Tor amplitude is not
  replaced by mere boundedness.
- `etaleImage` and `proetaleImage` are the existing ordinary right-derived direct images.
  The ordinary exceptional functor `etaleExceptional` is the existing
  `Etale.rightDerivedUpperShriek`. `exceptionalAdjunction` uses its recorded adjunction,
  normalized to ordinary direct image by the canonical proper forget-supports isomorphism
  `Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`. This is the identity-open
  compactification normalization, with no attempted definitional equality between an arbitrary
  chosen compactification and `(id_Z,i)`.
- `proetaleExceptional` is an abbreviation of the recorded `sfFiniteExceptionalFixed A
  (Compactification.ofIsProper i)`. In particular it is exactly `Rν_* ⋙ G_e ⋙ C_Z`; no ambient
  pro-etale exceptional adjunction is assumed. `exceptionalPlus` uses the existing preservation
  of D+ by `G_e`; the needed `CompactSpace T` in the interface is obtained from finite type
  over the field inside the theorem statement, not imposed as an additional hypothesis.
- `pullbackSquare` is the levelwise canonical sheaf comparison square, converted to the
  actual left-derived pullbacks by `leftDerivedFunctorIsoMapDerivedCategory`.
  `directImageMate` is its `mateEquiv` for the actual ordinary pullback/direct-image
  adjunctions. Thus its ordinary counit normalization is built into its construction.
  It is not a chosen isomorphism between functors. The first conjunct asserts this exact
  mate is invertible on every bounded-below etale H. Its inverse is eta wherever used.
- `homTransport` spells out, in order, precomposition with `b_H`, comparison adjunction,
  ordinary exceptional adjunction, and applying `C_Z` to the resulting morphism. The second
  conjunct asserts `Function.Bijective` for every H and L in the exact D+ categories in the
  displayed Hom chain, without adding constructibility assumptions on H or L.
- For N, the third conjunct has BOTH hypotheses: N bounded constructible and `G_e N` bounded
  constructible. `exceptionalOriginMap` is `C_Z G_e` of the actual comparison unit at N.
  `CounitComparison` asserts it is invertible and characterizes the transported counit μ by
  requiring its `homTransport` image to be this very map. Under that origin identification,
  this is the preimage of the identity. Its second equality is precisely
  `μ = b.inv ≫ C_T.map (exceptionalAdjunction.counit.app N.obj)`. The isomorphism b is explicitly
  constrained by `b.hom = directImageMate.app (G_e N)`; μ is constrained by the specified Hom
  chain, whose bijectivity is independently included above.
- The final conjunct quantifies over B in D+ with recorded bounded constructibility and M
  in D+ with the published etale finite-Tor constructibility predicate. Thus these are exactly
  the node's `D^b_c` and `D^b_ctf` objects. `tensorObject` is Q = B tensor Li_e^* M.
- `etaleProjection` is the recorded `Etale.rightDerivedLowerStarProjectionMap` at B,M.
  `proetaleProjection` is its existing pro-etale counterpart at C_Z B,C_T M. Both are the
  actual `Adjunction.rightAdjointProjectionMap` of the ordinary derived adjunction and the
  canonical tensor comparison. Their defining transpose is tensor comparison followed by
  counit tensor identity; `Adjunction.homEquiv_unit` gives exactly the node's displayed
  unit/R(image-of-transpose) formula.
- `tensorComparison` is the component of the existing
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`, which uses the actual
  `leftDerivedTensorComparison` and exact/left-derived identifications. `tensorTargetIso` is exactly the specified
  h from C_Z Q to C_Z B tensor Li_p^* C_T M. `projectionSourceIso` is t_C followed by
  b_B tensor identity; `projectionTargetIso` is b_Q followed by R i_p* of h.
  `ProjectionComparison` requires Q in D+, fixes both b components to the canonical mate,
  and asserts `π_p ≫ target.inv = source.inv ≫ C_T.map π_e`.
  After the two displayed tensor identifications, this is the node's eta equation with
  precisely its source and target. Its final clause quantifies over an isomorphism e whose
  hom IS π_e, supplies an isomorphism ep whose hom IS π_p, and asserts
  `target.hom ≫ ep.inv = C_T.map e.inv ≫ source.hom`, the inverse of the very same square.
  The conditional inverse claim asserts no extra independent projection-formula theorem.

Dependency declarations and source modules used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (also reexported by the finite
  exceptional interface): `Padic.finite_coefficientExtensionRing`; the original coefficient
  ring `Padic.coefficientExtensionRing` is reused throughout.
- Mathlib finite-type/proper/closed-immersion modules: `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsProper`, `IsClosedImmersion`; `Morphisms.Finite` gives the proper instance.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategoryModule`, `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` and
  `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`: the recorded fixed-scalar
  coefficient coordinates, `sfFiniteExceptionalFixed`, `sfPositiveCoefficient_finite`.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`; the underlying `comparisonUpperStar` and
  `comparisonLowerStar` are from `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`;
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `hasTorAmplitudeIn`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `.UpperShriek`, and
  `.LowerShriekToLowerStar`: compact-support candidate, exceptional functor and adjunction,
  canonical proper normalization. The identity-open compactification is the existing
  `Compactification.ofIsProper`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection`:
  the two `rightDerivedLowerStarProjectionMap` declarations and their actual tensor comparisons.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`:
  `derivedComparisonAdjunction`; `.Comparison.Monoidal` and `.Comparison.Flat` give
  the real monoidal and flatness structures. The finite-coefficient import family is used
  consistently to avoid duplicate legacy declarations.
- The node's existing proof-dependency modules are imported for the documented stage-3 plan:
  `ProjectionCompactification`, `ProEtaleConstantRingOperations`, `EtaleExceptionalAdjoint`,
  `CompactSupportComparisonUnit`, `FixedComparisonDirectImageMate`,
  `SupportComparisonPullbackCoherence`, `ComparisonPullbackExact`, `FiniteCoefficientFlatModel`,
  `ProjectionMateExact`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `ProEtaleConstantRingMap`. The general ringed-monoidal-comparisons node presently has no
  recorded module and remains a proof dependency; no unrecorded theorem is assumed in a definition.

Edge cases checked before writing: empty source or target and zero complexes leave the same
canonical adjunction composites and impose no nonemptiness condition. Identity closed immersion
uses the same canonical identity normalization, rather than an arbitrary identity isomorphism.
The level n=0 in the Lean parameter means coefficient level 1, not the forbidden level 0.
Different finite Tor intervals and shifts are allowed; no numerical amplitude is fixed in advance.
Arbitrary bounded-below H,L remain in the Hom claim. The inverse claim is conditional precisely
on invertibility of the named projection component. Both N and its exceptional value must have
the two constructibility hypotheses; neither was dropped.

Searches (full wrapper results are retained in sandbox `searches.jsonl`):

- LeanFinder: `Compatibility of etale proetale comparison with derived projection formula and
  transported exceptional counit`; eight hits, including generic derived-adjunction counit
  lemmas, no statement of this compatibility.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor`; generic adjunction constructors
  and accessors, no scheme comparison statement.
- Wrapper grep: `ProjectionMap|mateEquiv`, subdirectory `CategoryTheory/Adjunction`;
  Mathlib `Adjunction/Mates.lean` supplies `mateEquiv`, not this theorem.
- LeanSearch: `etale proetale derived projection formula canonical comparison`;
  eight etale/formally-etale hits, none stating this node.
- `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` for derived projection maps,
  comparison tensor isomorphisms, finite exceptional functors, and the item id found the
  canonical ingredients above. The item-id search found no existing theorem. The existing
  projection-comparison invertibility declarations do not give the transported exceptional
  counit and equality of the named maps and their inverses required here.

No statement correction, hollow definition, or statement dispute is required. The new definition node below owns the specified Hom transport and its counit property.
The generic-coefficient version compiles cleanly through scompile.py: the exceptional module takes about 6–8 seconds and the projection module about 8 seconds per file. The final records and formatting are checked again by the required delivery dry run.

## Second reading by Q125

The dispatcher explicitly forbids starting another agent. This is the worker's own second
reading; the maintainer's independent delivery review remains required. The node, recorded
interfaces, Stacks 0B56/0E48/0B65/0DV0, and Lean were reread clause by clause as above. The earlier
partial draft's tautological projection equality and unconstrained counit were replaced by
canonical mate constructions, the specified Hom transport, and the two actual commutative-square
identities. Missing separatedness and constructibility conditions were restored. The chosen
compactification is related to ordinary direct image by the canonical proper isomorphism,
rather than being treated as definitionally the identity-open compactification. The module has
one named postponed theorem with the full eight-step proof plan in its docstring. No independent
second reader is claimed by this worker report.

## New nodes

`def-weil-boundary-exceptional-comparison-data` owns the prescribed exceptional Hom transport,
its comparison-unit origin map, and the exact `CounitComparison` property. Its module is
`Sheaf.Paper.BoundaryExceptionalComparisonData`; every definition has real data and a source
docstring. It introduces no new adjoint or comparison isomorphism: the existing functors,
adjunctions and canonical mate supply all factors. The source is Stacks 0B65/0DV0 applied to
the displayed Hom chain in this item's boundary-duality realization. Semantic LeanSearch and
LeanFinder searches, Mathlib grep, upstream and Sheaf searches, DAG search and blueprint search
found no definition of this specified composite or its origin-counit property. The related
`lem-coef-site-closed-counit-transport` is a theorem with no recorded Lean declaration; it does
not already define these maps. The helper node factors the previously inline definitions
into a separate file for the required per-file compile limit. The original theorem imports
and uses these exact definitions; its mathematical statement is unchanged. On second reading,
the helper's map (without asserted bijectivity), exact canonical b, actual origin unit, and
two defining equations were checked against every clause of its new definition statement.

The projection constructions are parameterized by the existing generic coefficient-category
API, with its closed symmetric monoidal and functorial flat-resolution structures and the
existing flat-preservation classes. The main theorem specializes them to `coefficients A`,
a pure abbreviation for the established `ModuleCat (ULift A)`. Every structure at that
specialization is synthesized from the published module-category instances and finite-ring
flat-preservation theorem. No such structure is added as a hypothesis to the main theorem.
This keeps the kernel from repeatedly checking expanded concrete module-category structures
in each tensor-comparison definition; it does not change the specified tensor product or maps.

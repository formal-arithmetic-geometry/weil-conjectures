## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison` states the
constructible comparison theorem, with its proof postponed as one named theorem.
Its three supporting constructions give the canonical constant-section coefficient
map, Mathlib's actual module pullback (module Kan extension and sheafification),
and its termwise prolongation to cochain complexes.
A dependency module supplies the discrete constant-ring presentation of the bounded
constructible object predicate. Their
data contain no sorry. These helpers specify the constructions appearing in this
node, not extra assumptions on them.

Source read: the current main-20261015 unit `_section.md`, its four-step DAG proof,
and Stacks `proetale.tex`, definition-constructible, lemma-compare-constructible,
lemma-compare-derived and lemma-compare-constructible-derived (09AJ/09AK/09AL).
The statement and proof of the node are unchanged. The stage-1 repair note is
resolved; it required retaining this statement and using the existing stratification
gluing lemma instead of reproving it inside step 1. The Lean proof docstring does so.

Hypothesis and clause correspondence:

* A scheme X is `(X : Scheme.{u})`; the first assertion is on an arbitrary scheme.
* A discrete commutative Noetherian coefficient ring is
  `(A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]`.
  The constant sheaf uses the underlying ring with discrete coefficients; no
  topology on A, finite underlying set, or Noetherian hypothesis on X is imposed.
  Independent `v` allows coefficients larger than the scheme universe. The recorded
  AsSmall sites retain the original schemes, morphisms, topologies and covers.
* Constructibility in paragraph 1 is the existing
  `Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F`.
  The first conjunct of the theorem identifies this with
  `∀ x, ∃ U, x ∈ U ∧ ∃ S, ...`: a Zariski neighborhood of each point and a finite
  locally closed scheme stratification. `S.n`, `S.stratum`, `S.domain` and
  `S.immersion` retain the finite partition, locally closed immersed scheme
  representatives, disjointness and coverage; `Topology.IsConstructible` is
  required for every stratum in U. The composite `S.immersion a ≫ U.ι` is the
  inclusion into X, so restriction is to the actual stratum scheme.
* On each stratum, `IsCoefficientModelLocallyConstantFinite` uses a covering sieve
  and a module-sheaf isomorphism to the sheafification of a constant module.
  It requires `Module.Finite A M`, so this is finite type, including infinite
  underlying sets. The recorded affine-local predicate uses finite presentation;
  these are equivalent over a Noetherian ring by
  `Module.finitePresentation_iff_finite`. This matches the finite constant models
  of `sk-def-sfb-constructible` specialized to discrete coefficients.
* Quasi-compactness and quasi-separatedness appear only in the second conjunct,
  as `∀ [CompactSpace X] [QuasiSeparatedSpace X], ...`. They apply to the classicality
  and two equivalence clauses, exactly as in paragraph 2. There is no separation,
  reducedness, affine, or finite-type hypothesis on X.
* Classicality is asserted for every F satisfying the recorded constructibility
  predicate. It is written with the dependency's actual `continuityMap`, for every
  `AffinePresentation X I` and every small cofiltered `I : Type (u + 1)`.
  `coefficientModelFixedScalars` restricts along the canonical constant-section
  map, and `AsSmall.up.op` reads those sections on the original site. `IsIso`
  is required of the map in `ModuleCat A`, with colimit over the opposite index.
  This is precisely clause 3 of the recorded continuity definition, using its
  already universe-polymorphic module continuity construction. We do not replace
  classicality by existence of an arbitrary antecedent or introduce a second
  classicality predicate.
* The sheaf equivalence has source the recorded
  `Scheme.CoefficientConstructibleEtaleModuleCategory X A` and target the full
  subcategory of the recorded pro-etale constructible predicate. In particular,
  it retains all ambient linear morphisms, identities and compositions. The
  natural isomorphism after the two inclusions identifies its forward functor
  with `constructibleComparisonPullback X A`, the actual canonical inverse image.
  This prevents an unrelated equivalence from satisfying the statement.
* The derived source is the recorded
  `Scheme.CoefficientBoundedConstructibleEtaleCategory X A`. The target is
  `(coefficientBoundedConstructibleProEtale X A).FullSubcategory`. Its definition requires
  constructibility of every integer cohomology sheaf and an ordered finite interval
  of vanishing. Both ambient derived categories use `ConstantCompletion.D`, i.e.
  Mathlib's ordinary standard localization; no completeness condition is added.
  This is the discrete constant-ring encoding of the bounded-constructible
  definition, not the derived category of the smaller constructible-sheaf category.
* `D` is the induced functor on ordinary derived categories, normalized by the
  natural isomorphism `Q ⋙ D ≅ constructibleComparisonComplexPullback X A ⋙ Q` on
  ALL cochain complexes. The localization universal property determines such D
  up to natural isomorphism. The final inclusion square identifies the bounded
  equivalence's forward functor with this D. Thus the claimed derived equivalence
  is induced by nu*, rather than a bare Nonempty equivalence of categories.

Dependency interfaces read and used:

* `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `ConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelBoundedConstructible`.
  These specify the finite constant model meaning of Cons and Dbc. For discrete
  coefficients the theorem uses the existing intrinsic constant-ring specialization
  below, keeping arbitrary coefficient sizes.
* `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`, reexporting
  `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible` and
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`:
  `boundedConstructible`, `BoundedConstructible`, `mem_boundedConstructible_iff`.
  Boundedness means ordinary derived cohomology vanishing outside a finite interval.
  The triangulatedness theorem is not assumed or restated.
* `Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules`:
  `Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf` and
  `Scheme.coefficientProEtaleFixedModulePullback`. The already landed definition
  node `def-sfb-affine-locally-constructible-proetale-modules` is added to stmt_deps.
* `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`:
  `Scheme.IsCoefficientConstructibleEtaleModule`,
  `Scheme.CoefficientConstructibleEtaleModuleCategory`,
  `Scheme.IsCoefficientBoundedConstructibleEtale`,
  `Scheme.CoefficientBoundedConstructibleEtaleCategory`,
  `coefficientModelFixedScalars`, `IsCoefficientModelLocallyConstantFinite`.
* `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`:
  `AffinePresentation`, `sectionDiagram`, `sectionCocone`, `continuityMap`,
  `IsClassical`, `moduleSectionPresheaf`, `moduleContinuityMap`, `IsClassicalModule`.
  The first four have fully general coefficient-category universes, which let us
  state exactly the same continuity property with independent coefficient size.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`; its existing transported inclusion and topology
  are reexported through `ProEtaleSmallModelComparison` as
  `smallModelComparisonInclusion`, `smallModelComparisonEtaleTopology`,
  `coefficientProEtaleModelTopology`. The new coefficient map is the canonical
  constant-section map for that same inclusion.
* Mathlib: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `IsNoetherianRing`,
  `CompactSpace`, `QuasiSeparated` / `QuasiSeparatedSpace`,
  `Topology.IsConstructible`, `Module.Finite`, `Module.FinitePresentation`,
  `SheafOfModules.forget`, `PresheafOfModules.pullback`,
  `PresheafOfModules.sheafification`, and `ObjectProperty.FullSubcategory`. The abbreviation for comparison pullback
  uses `SheafOfModules.pullback`; its existing `pullbackIso` identifies it with
  forget-to-presheaves, module Kan extension and module sheafification.
* Compatible recorded proof-dependency modules with a Lean declaration are imported
  privately, including `proEtaleClassicalSheavesModules`, `constructible_isClassicalModule`,
  `locallyConstructible_isClassicalModule`, `finiteLocalSystemsTwist`,
  `boundedBelowComparison`, `directImageComparison`, and
  `Scheme.exists_global_stratification_factoring_local`. The latter's current
  source was read with `scompile.py --source`; the original source checkout lacks
  that module, while the published library supplies it. Mathlib proof leaves
  (finite presentation, affine basis, constructible subsets) come through the
  imported modules. The proof docstring follows all four DAG steps explicitly.

Edge cases checked before writing:

* Empty X: the pointwise locality clause is vacuous, and zero-stratum partitions
  are permitted by the existing stratification structure. No Nonempty X appears.
* Zero sheaf and zero coefficient ring: zero modules are finite and finitely
  presented, and every constant local model can be zero. No nontriviality binder.
* Empty strata and variable local module values are allowed. The finite models
  need not have finite underlying sets (e.g. A itself for A = Z).
* A single nonempty stratum gives the usual finite-type local systems. Schemes
  may be nonreduced; no reducedness condition is imposed on stratum schemes.
* Arbitrary integer cohomological bounds, including shifted degree-zero objects
  and the zero complex, are allowed. For the zero complex take a = b = 0.
* The cofiltered presentation index is nonempty by IsCofiltered, as in the recorded
  definition, and its opposite supplies the filtered module colimit. No arbitrary
  smaller index universe or extra assumption of a chosen presentation is used.
* The coefficient universe is max v (u+1), so enlarging coefficient values does
  not force any equality between site object, site arrow and ring universes.

Searches for an existing declaration:

* `msearch.py ... leanfinder` with
  `constructible pro-etale sheaves comparison equivalence etale bounded constructible derived categories`:
  eight hits, including `Scheme.Etale.forgetFullyFaithful`, the etale topology,
  site-equivalence sheaf functors, and `Condensed.lanSheafProfinite`; none states
  the constructible module comparison.
* `msearch.py ... loogle 'IsConstructible, comparisonUpperStar'`: zero hits;
  unknown `IsConstructible` in the Mathlib search environment.
* `msearch.py ... grep 'constructible.*comparison|comparison.*constructible'`:
  zero Mathlib hits, using the correct root without a doubled Mathlib directory.
* `rg` in the source WeilConjectures tree and `lean/Sheaf` for
  `constructible.*[Cc]omparison|[Cc]omparison.*[Cc]onstructible`:
  existing generic comparison exactness and finite-coefficient comparison material,
  but no full discrete Noetherian constructible equivalence. `grep -rn` for this
  blueprint id in upstream WeilConjectures found no matching declaration.
* `rg` for the comparison helper names and the bounded specialization name in
  `dag/lean_names_upstream.json`, source WeilConjectures and `lean/Sheaf`: no hit.
* Focused searches for bounded-constructible definitions found the existing etale
  coefficient-sized category and the finite-coefficient/general internal-module
  versions. None defines this predicate on coefficient-sized intrinsic pro-etale
  constant-ring modules. The dependency module specifies this bounded condition in the encoding used by
  the already recorded discrete constructibility interface, while publicly retaining
  the entire existing general ring-object interface.

Import compatibility finding: the private proof import
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence` imports the retired
`WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`. The recorded
`BoundedBelowProEtaleComparison` uses the preferred finite-coefficient framework,
which declares the same `derivedComparisonAdjunctionPlus`. Importing both fails
with “environment already contains”. I omitted the retired proof-only import;
its theorem remains named in the proof docstring, and all its source signatures
were read. The finite-coefficient comparison is supplied by the bounded-below
proof dependency. This does not change any statement object or hypothesis.

No statement correction, new independent notion, or disputed statement is needed.
The bounded dependency receives a lean-only interface repair, described below. The only added statement dependency is an already landed
specialization that the theorem uses directly.

## Second reading by Q36

Author self-check, not an independent review; the maintainer supplies the independent
reading required by this dispatch. I reopened the node, the source unit, the recorded
constructibility interfaces, and this file. The first conjunct has no qcqs restriction;
qcqs is required only in the second conjunct. The bounded specialization takes
these same qcqs instances, where local and finite-global stratifications agree. The local condition includes actual
stratum schemes and their composite immersions, constructibility of the subsets, and
finite MODULE generation. The first predicate uses finitely presented models, so the
Noetherian binder is essential to its equivalence with the displayed finite-type
condition. Classicality uses the actual dependency continuity map and all presentations,
not a freely chosen map. Both equivalences retain ambient morphisms; both forward
functors are normalized to nu*. The derived normalization uses every cochain complex,
so it fixes the localization-induced functor, including its action on morphisms. The
derived categories are bounded by cohomology, with no completeness or finite Tor
condition. The three comparison helpers and bounded dependency have constructed data and source/blueprint docstrings.
All universes and variables are explicitly bound. No independent review is claimed.

Validation: `scompile.py Q36 sk-thm-pe-constructible-comparison` compiled BOTH
delivered modules separately in dependency order, in sandbox and library mode,
with exit 0 and no warnings or errors. The module comparison has one expected
named theorem with sorry; the bounded dependency has no sorry. Delivery preflight
is run below.

## Dependency modules

`sk-def-sfb-bounded-constructible`: the existing recorded declarations apply to
internal module objects on the original site, while this comparison uses intrinsic
constant-ring module sheaves on the recorded coefficient-sized equivalent sites.
The former cannot take these objects as arguments. The new module
`Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly imports
the entire old general interface and adds
`AlgebraicGeometry.ProEtale.coefficientBoundedConstructibleProEtale`, its exact
discrete constant-ring presentation using the existing affine-local constructibility
predicate and `coefficientModelCohomology`. Each integer cohomology sheaf must be
constructible; it vanishes outside an ordered finite interval. Its FullSubcategory
has all ambient morphisms by the existing ObjectProperty construction. There is
no completeness condition. Nothing of this dependency node changes except lean.
The original general definition, membership characterization, full subcategory and
weak Serre triangulatedness remain public. The upstream definitions and the new
specialization are listed in lean.declarations; the side-project weak Serre theorem
is reexported by its existing module. This is
an interface specialization of the same notion, not a replacement of the general
statement by a discrete-only statement. The dependency module has constructed data
and contains no theorem or sorry. Its own source and blueprint id are in its
module and declaration docstrings.

Elaboration self-check: the constant-ring map supplies the source constant
presheaf and the target comparison pushforward explicitly to sheafification's
Hom equivalence. Full-subcategory inclusions use `ObjectProperty.ι` explicitly.
`constructibleComparisonComplexPullback` is Mathlib's termwise functor, with
zero-map preservation supplied directly by the existing module pullback
adjunction and `Functor.preservesZeroMorphisms_of_isLeftAdjoint`. This avoids
adding a hypothesis, a new axiom, or a postponed structural proof.

Preflight repair: the first dry run compiled both modules cleanly, then refused
listing the imported side-only `isTriangulated_boundedConstructible_of_weakSerre`
in the dependency's lean.declarations (the gate resolves imported declarations
only in Mathlib/upstream source). Removed that metadata entry while retaining
the public import that supplies the theorem. No Lean code or statement changed.

Final dry run: `deliver2.py Q36 sk-thm-pe-constructible-comparison --no-push`
returned exit 0: “OK (dry run): commit 5404b444a0 passes the preflight and compiles;
nothing pushed”. Both modules passed the required separate compilation again.

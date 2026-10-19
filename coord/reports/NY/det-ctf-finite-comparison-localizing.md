## Worker report

The published declaration `AlgebraicGeometry.ProEtale.finiteComparisonLocalizing`,
module `Sheaf.Paper.FiniteComparisonLocalizing`, already matched this node when
this worker opened the item. An initial exact-existing-match dry run exposed an
import collision in its published import closure. The final delivery repairs the
owning module in place and records `existing: false` with its existing file path.
It changes exactly one import line. Every definition, theorem statement and proof
body is byte-for-byte unchanged; no second notion or duplicate declaration is added.
No node statement or dependency is changed.

Source read: current blueprint main-20261015, sec-six-functors-basics/
sk-prop-ctf-finite-comparison/sk-prop-ctf-finite-comparison-localizing.md, the complete
DAG statement and five proof steps, and the complete existing Lean module including
its helper definitions and theorem docstring. There is no repair note for this item.

Hypothesis and clause correspondence:

* The characteristic prime is `(p : ℕ) [Fact p.Prime]`; the algebraic closure of the
  finite field is `(k : Type u) [Field k] [Algebra (ZMod p) k]
  [IsAlgClosure (ZMod p) k]`. Algebraic closures of finite fields of characteristic p
  give the same standing algebraically closed base; the power q is not additional data
  used by any construction or conclusion here.
* The coefficient prime and inequality are `(ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)`.
  Section variables bind `B : Type`, `[CommRing B]`, `[Finite B]`,
  `[TopologicalSpace B]`, `[IsTopologicalRing B]`, `[DiscreteTopology B]`.
  `(hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)` expresses annihilation by an ℓ-power.
  `ULift B` implements the fixed coefficient universe without changing the ring.
* Standing finite-type schemes use `Scheme.{u}`, `X.Over (Spec (.of k))`,
  `LocallyOfFiniteType (X ↘ Spec (.of k))` and
  `QuasiCompact (X ↘ Spec (.of k))`. Y, U, P in the operation clauses have the same
  structure-map hypotheses; their named morphisms have `IsOver` instances.
* Ordinary unbounded module categories are `Etale.DerivedCategoryModule (ULift B) X`
  and `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat (ULift B)))`.
  The functor is the canonical `(comparisonUpperStar (ModuleCat (ULift B)) X)
  .mapDerivedCategory`, rather than an arbitrary comparison functor.
* The section parameter `eR` is a ring-object isomorphism supplied by
  `Profinite.finiteDiscreteCondensedRing_constant`, with `[IsMonHom eR.hom]`.
  `finiteComparisonRealization B X eR` is the actual ordinary-action sheafification
  followed by `Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv`.
  It is not an assumed equivalence or an arbitrary chosen map. The scheme ring
  isomorphism has the explicit equality API specifying the pullback of eR.
* Etale Dctf is `finiteComparisonEtaleGenerators`: recorded
  `Etale.DerivedCategory.isBoundedConstructible` intersected with
  `DerivedCategory.finiteTorAmplitude`. Pro-etale Dctf is
  `finiteComparisonProEtaleGenerators`: the recorded
  `constantModelBoundedConstructible` and finite Tor amplitude, evaluated on the
  transported object. `finiteTorAmplitude` quantifies over an interval a,b and
  `torAmplitudeIn` tests every module sheaf through `singleFunctor _ 0`, exactly
  the uniform degree-zero tensor test in the node.
* Both closures, `finiteComparisonEtaleClosure` and `finiteComparisonProEtaleClosure`,
  use `CategoryTheory.localizingClosure`. This is the intersection of all replete,
  triangulated, ambient-coproduct-closed object properties containing the generators;
  it imposes no completeness condition.
* `∃ hpres` states that comparison takes the etale closure into the pro-etale one.
  The `.lift` of the etale inclusion composed with comparison is required to have
  `.IsEquivalence`. Thus this is the restricted canonical comparison on full categories.
* The next conjunct tests every ambient distinguished triangle with its three
  objects in the closure and requires its comparison image to be distinguished.
  This renders exactness with the inherited ambient triangles.
* The cofan conjunct ranges over `I : Type (u + 2)` (the ambient derived object's
  indexing universe), every family in the closure, and every ambient colimiting cofan.
  It states that its vertex stays in the closure and its image remains colimiting.
  These are the ambient small sums of the node.
* For every g, `[LocallyOfFiniteType g] [QuasiCompact g]` expresses finite type.
  The two conjuncts assert `IsIso` of the canonical
  `unboundedDirectImagePullbackIso` component on closure inputs on Y, and of
  `unboundedDirectImageComparisonMap` on closure inputs on X, respectively.
  Both conclusions are in the ambient categories, with no stability assertion.
* The open clause has `[IsOpenImmersion j]` and `IsIso` of the component of
  `finiteComparisonOpenIso`, obtained by applying `mapDerivedCategoryNatIso` to
  the canonical sheaf open-extension comparison and composing the canonical
  composition isomorphisms. It is the stated nu-star/j-shriek comparison.
* The final clause quantifies over every standing open/proper factorization
  `j : X ⟶ P`, `r : P ⟶ Y`, `[IsOpenImmersion j] [IsProper r]`.
  `finiteComparisonCompactSupportMap` is literally the direct-image mate on j_! K
  followed by Rp_* of the open comparison. Its invertibility on closure inputs
  is the desired comparison for the stipulated composite definition Rf_!.

Dependency declarations inspected and reused (directly or through the existing module):

* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, and the ordinary `DerivedCategory` framework.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientDerivedComparison`;
  this node explicitly uses ordinary constant modules and the stated coefficient
  identifications, not a private second definition of the ringed-site module category.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`.
* `Sheaf.Paper.LocalizingAdmissibleCoefficients` publicly imports
  `Sheaf.Paper.LocalizingClosure`; the latter supplies the exact reused
  `CategoryTheory.IsLocalizingSubcategory` and `CategoryTheory.localizingClosure`.
  The additional admissibility predicate is unnecessary for the explicitly finite B case.
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
* Mathlib `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsProper` in their recorded modules. Properness implies
  quasi-compactness through universal closedness.
* `Sheaf.Paper.FiniteDiscreteCondensedRing`:
  `Profinite.finiteDiscreteCondensedRing_constant`.
* `Sheaf.Paper.FiniteDiscreteSchemeRing`: `finiteDiscreteSchemeRing_constant`,
  `finiteDiscreteSchemeRingIso`, `finiteDiscreteSchemeRingIso_eq`.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence` and `ordinaryAction`.
* `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison`:
  `unboundedDirectImagePullbackIso`, `unboundedDirectImageComparisonMap`;
  `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`.

The three source files for finite-discrete coefficients/internal modules and the
recorded derived-category module absent from the older local checkout were read using
`scompile.py --source <Module.Name>`, as prescribed. No source was modified.

Edge cases: the zero ring is allowed; exponent n=0 then forces that case.
Empty schemes, the zero complex, the empty indexing family and identity morphisms/open
immersions are included. There is no nonempty or nonzero assumption, no extra
separatedness hypothesis, no boundedness of closure inputs, and no direct-image
closure-stability assertion. The coefficient isomorphism is supplied by the recorded
finite-discrete theorem, including the zero ring and empty profinite sets.

Searches performed with `msearch.py NY det-ctf-finite-comparison-localizing`:

* LeanFinder: `etale proetale finite coefficient comparison equivalence localizing
  closures constructible finite Tor amplitude`: eight ring-etaleness/localization
  hits; none is the geometric comparison statement.
* Loogle: `CategoryTheory.localizingClosure,
  AlgebraicGeometry.ProEtale.finiteComparisonLocalizing`: no hits, unknown identifier
  `CategoryTheory.localizingClosure` in Mathlib.
* Mathlib grep: `finiteComparisonLocalizing|localizingClosure|proetale.*localizing`
  under CategoryTheory: zero hits.
* LeanSearch: `etale proetale localizing closures finite coefficient equivalence`:
  eight ring-etaleness results, no matching geometric comparison.
* Direct `rg` of the source repository, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `det-ctf-finite-comparison-localizing`,
  `finiteComparisonLocalizing`, `localizingClosure`: the exact existing theorem is
  `Sheaf.Paper.FiniteComparisonLocalizing:255`; closure definitions occur in
  `Sheaf.Paper.LocalizingClosure`. No duplicate upstream theorem was found.

No missing definition, dependency repair, statement correction or disputed statement
was found. The published module's import closure did require repair:

1. The initial `deliver2.py ... --no-push` compiled the published module itself,
   then failed when importing it in the generated existing-match probe: importing
   `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`
   encountered `AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin`, already
   declared in `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`.
2. Traced the finite-coefficient derived import to the broad
   `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` import. The only
   declaration this owning module needs from it is the upstream canonical sheaf
   comparison `openImmersionLowerShriekComparisonUpperStarIso`.
3. Replaced that one import by
   `public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison`.
   Its signature and adjunction-mate definition were read in the upstream source;
   it supplies exactly the same canonical comparison. The broad side proof module
   is omitted because its exports cause the duplicate, not to alter the proof route.
   The node's open-extension comparison proof remains in the theorem docstring.
4. `scompile.py NY det-ctf-finite-comparison-localizing <sandbox module>` passed both
   the sandbox and final library-file compilations, each in 6.6 seconds, with no
   errors or warnings. No tool, live source, or compiled artifact was edited.


## Second reading by NY

The dispatcher prohibits starting other agents. This is a second pass by the same
worker, not an independent review; the maintainer supplies independent delivery review.
With the DAG statement and the entire existing module open, checked each item above
against the actual signature and definitions, especially the coefficient transport,
finite-Tor degree-zero tests, full-subcategory lift, all five operation clauses and
ambient cofan universe. The existing declaration matches the node. Re-read the repaired
module against the original: the only difference is the public import naming the
upstream canonical open-extension comparison module instead of the broader side module.
Its exact canonical adjunction-mate definition is used unchanged. No new declaration,
statement correction or additional hypothesis has been introduced. The final node
signature is verbatim from the unchanged theorem in the delivered module.

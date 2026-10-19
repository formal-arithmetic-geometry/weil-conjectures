## Worker report

The module `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` states
`AlgebraicGeometry.Etale.sf_finite_etale_projection_formula`, with proof `sorry`.
It asserts that the actual canonical small-etale compact-support projection component
is invertible, and that both its endpoints lie in the strictly full bounded-below
subcategory. Together these say exactly that the specified projection is an
isomorphism in D+(Y_et, Lambda). The source is the current main-20261015 blueprint,
sec-six-functors-basics, sk-thm-sf-pf-finite, order 1706; I read both its unit statement
and proof and the chapter introduction. The original statement is unchanged.

Hypothesis and clause correspondence:

- The prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension E/Q_ell is
  `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The positive finite level is
  `(n : ℕ) (_hn : 1 ≤ n)`. Lambda is everywhere the recorded actual quotient
  `Padic.coefficientExtensionRing l E n`; it is not an arbitrary finite ring.
- The schemes are `{X Y : Scheme.{u}}` and the named morphism is `(f : X ⟶ Y)`.
  Separated finite type means `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`. There is no finite-field datum, characteristic restriction,
  separatedness of the schemes over a field, or extra condition on the base.
- `(c : Compactification f)` explicitly supplies the chosen factorization that
  defines Rf! and PF in the source's first proof step. The result holds for every
  such choice, not just a special compactification. This is the operation's datum,
  as in the recorded exchanges, rather than a new geometric condition on f.
  No global compactification existence theorem over an arbitrary non-qcqs base is
  asserted here; we state the property of the given canonical compactification map.
- `K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X` and the
  corresponding `L` over Y are complexes on the small etale sites, with module
  sheaves valued in `ModuleCat.{u + 1}`. They are not pro-etale complexes.
- `_hKc` and `_hLc` quantify over every integer i and apply exactly
  `Scheme.IsConstructibleEtaleSheafOfSets` to the underlying set sheaf of H^i.
  This is the constructible-stratification and finite-locally-constant predicate
  recorded by def-weil-pbc-etale-sheaves, not the upstream finitely-generated-stalk
  predicate with a different definition.
- `_hKb` and `_hLb` each give integers `a ≤ b` outside which the relevant homology
  sheaves are `IsZero`. These express boundedness, so together with the preceding
  conditions they express K in Db_c and L bounded constructible.
- `_hLt : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn ... Y a b L` is finite
  Tor amplitude using the exact bounded-interval predicate of def-kun-tor-amplitude.
  It tests tensor with every module sheaf in degree zero. No Tor-amplitude hypothesis
  is imposed on K. Empty intervals are permitted, allowing the zero object.
- The first conclusion uses `DerivedCategory.TStructure.t.plus` on
  `derivedTensorRightDerivedLowerShriek ... c K L`, namely Rf!K tensor L.
  The second uses the same predicate on
  `rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar ... c K L`, namely
  Rf!(K tensor Lf*L). These assert exactly the D+ typing in the node.
- The last conclusion is `IsIso (((sfEtaleProjection ... c).app K).app L)`.
  `sfEtaleProjection` is definitionally the upstream natural transformation
  `projectionMapOfCompactification`, the proper counit projection followed by the
  inverse canonical open tensor comparison and pullback composition. Both
  naturalities are part of its type as a natural transformation of bifunctors.
  Invertibility is asserted of this map, not of an unrelated map between its endpoints.
  Since D+ is full, the ambient inverse is its inverse in D+ as well.

Dependency declarations read and used:

- sk-def-sf-exchanges: original `Sheaf.Paper.SfExchanges` was read in full;
  its finite maps are pro-etale. The delivered dependency interface
  `Sheaf.AlgebraicGeometry.SfEtaleExchanges` adds
  `AlgebraicGeometry.Etale.sfEtaleProjection`, a specialization of
  `AlgebraicGeometry.Etale.projectionMapOfCompactification` in upstream
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`.
  The upstream declaration's full signature and composite were read. Its source
  and target bifunctors are the two endpoint declarations used in the conclusion.
- def-weil-l-adic-coefficient-extension:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, re-exporting the actual
  `Padic.coefficientExtensionRing` construction from `CoefficientExtension`.
  I read both modules, including the integer ring, uniformizer ideal and quotient.
- def-weil-finite-type-morphism: Mathlib morphism modules `FiniteType` and
  `QuasiCompact`, declarations `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`; their signatures and docstrings were read.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; also `IsSeparated` in its morphism module.
  Properness is used in the compactification construction, not added as a condition on f.
- def-weil-pbc-derived-categories:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read with
  `scompile.py --source`, since absent from the older local checkout), together with
  `Etale.DerivedCategoryModule` in upstream `Derived.Coefficients`, and Mathlib
  `DerivedCategory.homologyFunctor`, `DerivedCategory.TStructure.t.plus`.
- def-weil-pbc-etale-sheaves:
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, read in full using
  `scompile.py --source`, especially `Scheme.IsConstructibleEtaleSheafOfSets`.
- def-kun-tor-amplitude: the mixed record in
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` explicitly records bounded intervals
  using the existing `Etale.DerivedCategory.hasTorAmplitudeIn` from upstream
  `Derived.Coefficients`. I use precisely that existing bounded predicate;
  the lower-bounded variant is not needed by this statement.
- def-kun-derived-tensor:
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, `Etale.derivedTensor`,
  as used by the two canonical projection bifunctors and the Tor predicate.

The module imports the recorded modules of all stated proof dependencies, including
site-derived tensor descent, geometric perfect stalks, the proper base-change and
projection compatibility statements, and the projection mate exactness interface.
Mathlib proof leaves are imported from their recorded point, short exact sequence,
triangulated-category and degreewise-split triangle modules. The proof docstring
follows all six current DAG steps. No new proof route or stronger finite-field
projection theorem is used as an input.

Edge cases checked before writing: empty schemes, K=0, L=0, the zero finite-free
stalk complex, shifts and complexes with gaps, and the empty Tor interval. Boundedness
allows zero complexes and arbitrary integer shifts. Positive levels n=1 and n>1 are
included; n=0 is excluded by the coefficient convention, not by an added condition.
No finite global dimension of A_(E,n) is assumed. The proof only represents the
perfect stalk of L by finite free modules, never an arbitrary A_(E,n)-complex.
No characteristic restriction or finite Tor condition on K has been inserted.
Universes follow the recorded six-functor convention: schemes in u, coefficient
modules and E in u+1, with all binders and the universe explicitly declared.

Searches (full raw service summaries are in the sandbox searches.jsonl):

- `msearch.py ... leanfinder`, query "For a separated finite type morphism of
  schemes the compact support projection formula is an isomorphism for bounded
  constructible etale complexes and finite Tor amplitude coefficients": eight
  unrelated algebraic-geometry hits, no exact theorem.
- `msearch.py ... leanfinder`, query "compact support projection formula etale
  bounded constructible finite Tor amplitude": eight unrelated compactness and
  quasi-separatedness hits, no match.
- `msearch.py ... loogle`, query
  `AlgebraicGeometry.Etale.projectionMap, AlgebraicGeometry.Etale.HasProjectionFormula`:
  zero hits; projectionMap unknown to the Mathlib search service.
- `msearch.py ... grep`, pattern `projectionMap|HasProjectionFormula|LowerShriek`,
  Mathlib subdirectory `AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`, query "projection formula compact support small
  etale site bounded constructible finite Tor amplitude": eight unrelated hits.
- `rg` on the project's Lean and upstream SixFunctors, and
  `grep -rn sk-thm-sf-pf-finite` on upstream WeilConjectures, located
  upstream `Etale.hasProjectionFormula_of_boundedConstructible` in `Derived.Exchange`.
  Its full signature adds `HasInvertibleExponent Lambda Y`; it therefore is not an
  exact existing match for this node. The unrestricted upstream finite projection
  theorem also adds this invertibility condition. Neither is rebound to this node.
- The project modules `FiniteCompactProjectionFormula` and
  `FiniteCoefficientEtaleProjectionFormula` were read in full: both require a fixed
  finite-field datum, ell different from its characteristic, and schemes of finite
  type over that datum; the latter also requires separatedness over that field.
  They are not exact existing matches for this more general unit statement.
- `rg` for both new declaration names in upstream WeilConjectures, project
  `lean/Sheaf` and `dag/lean_names_upstream.json` found no declaration collision.

No STATEMENT-DISPUTED finding and no correction to the item statement. The released
repair note for this item was read: it is a resolved stage-1 proof-splitting note,
not an invalidated stage-2 interface. This delivery leaves its proof plan unchanged.

## Dependency modules

`sk-def-sf-exchanges`: its recorded finite projection is in intrinsic pro-etale
module categories, whereas this consumer explicitly says small etale. Under §1(B),
`Sheaf.AlgebraicGeometry.SfEtaleExchanges` publicly re-exports the old module,
keeping all its exchange, completed exchange and supplied-stage interfaces available,
and adds only `Etale.sfEtaleProjection`. The new definition specializes the already
published small-etale `projectionMapOfCompactification` to constant module
coefficients. No duplicate tensor, pullback, direct image, extension by zero or
arbitrary projection map is constructed. The dependency node changes only in `lean`,
whose note explains this interface repair. Its old definition statements remain
available under exactly their original names through the public import.

## Second reading by NH

No second worker reading is claimed: the dispatcher explicitly directs this worker
to deliver itself without starting other agents. The maintainer's independent
review reads this delivery. I checked the hypothesis and conclusion correspondence
above against the current unit and both delivered files; the main distinction found
was the pro-etale finite projection in the dependency, addressed by the dependency
module rather than silently changing the site of this statement.

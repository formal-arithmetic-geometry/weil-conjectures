## Worker report

The new module `Sheaf.Paper.ModelCompactComparisonUnit` states
`AlgebraicGeometry.ProEtale.CondensedRing.modelCompactComparison_eq_properUnit`.
Its only postponed theorem has proof `by sorry`. Four explicit definitions name the
proper-unit transformation, its specialization to a model iterate, the specified
comparison with the identity pullback removed, and the actual global operator for an
arbitrary Weil object for that iterate. These helpers belong to this node's own recipe
and are listed in `lean.declarations`; none chooses a comparison or supplies data by sorry.
No node statement or dependency list is changed. No disputed statement was found.

Hypotheses and clauses:

- The finite-field datum is unpacked, without changing its scope: `k₀ : Type u`,
  `[Field k₀] [Finite k₀]`, `k : Type u`, `[Field k] [Algebra k₀ k]`
  and `[algClosure : IsAlgClosure k₀ k]`. The source interface calls its characteristic
  `ringChar k`, and its cardinality `Nat.card k₀`; these are the datum's p and q.
  Every finite field has prime characteristic and cardinality a positive power of that
  prime, so omitting the unused integer a and using this unbundled presentation
  neither adds fields nor removes a finite-field datum. The recorded `FiniteFieldDatum`
  module is imported as the datum convention. No second finite-field notion is defined.
- `ℓ : ℕ`, `[Fact ℓ.Prime]`, `[Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ ℓ)]` express the prime coefficient and distinct prime characteristic.
- `f₀ : X₀ ⟶ Spec (.of k₀)`, `[LocallyOfFiniteType f₀]`,
  `[qcModel : QuasiCompact f₀]`, `[sepModel : IsSeparated f₀]` express separated finite type.
  The latter two assumptions and `algClosure` are explicitly retained by `include`.
- `X : Over (Spec (.of k))`, with the same three geometric property instances on `X.hom`,
  is the geometric scheme. `π : X.left ⟶ X₀` and
  `hΦ : IsModelFrobenius Φ f₀ π` specify its cartesian geometric-fibre square and the
  exact base-changed q-power Frobenius. This is the source's arbitrary representative of
  the fibre product, not an arbitrary endomorphism. `point k` is s and `toPoint X` is f.
- `r : ℕ`, `hr : 1 ≤ r` and `frobeniusIterate Φ r` express the positive iterate h.
  The helpers install `hΦ.isFinite r` and `hΦ.isUniversalHomeomorphism r` from the
  source; neither property is imposed as a new hypothesis. Finite implies proper by
  Mathlib's recorded finite/proper instance.
- `Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧` is the actual bounded constructible
  category of internal modules, with ordinary derived morphisms. There is no adic,
  discrete-coefficient, derived-completeness or finite-Tor replacement.
- P is exactly `boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
  (toPoint X)`, the chosen-compactification construction.
- `compactSupportProperUnit` uses, in order, the restricted adjunction's unit whiskered
  by P; the inverse of `boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl` whiskered
  by P; the inverse of `boundedConstructibleLowerShriekComp_padicAlgCl`; and
  `eqToIso (congrArg ... (comp_toPoint h))`. Functor unitors and associator only type the
  composition. At M these are exactly the four arrows defining d in the node.
- `modelCompactComparisonWithoutIdentity` precomposes the actual
  `compactCohomologyFrobeniusComparison` with the inverse of
  `Functor.isoWhiskerLeft P (boundedConstructibleUpperStarId ... (point k))` composed
  with `Functor.rightUnitor P`. This is precisely the specified identity removal,
  including the unitor. The first conjunct identifies this natural transformation with d,
  hence gives the displayed equality at every M.
- The second conjunct quantifies over every `M N` and `v : M ⟶ N` in that category
  and asserts `P.map v ≫ d.app N = d.app M ≫ P.map (Lh*.map v)`, the asserted naturality.
- The third conjunct quantifies over **every** `K : WeilBoundedConstructibleOfEnd ℓ h`,
  so it covers arbitrary w, not just structures obtained by iterating a Weil structure
  for Φ. `K.str` is w. `modelCompactGlobalOperator` is the published `K.globalOperator 1`,
  with its finiteness instances transported along `frobeniusIterate_one`; its data are
  not a surrogate operator. The equality says precisely `globalOperator = d ≫ P.map w.hom`.
  The source's first-iterate normalization uses its pullback right-unit coherence;
  this step is documented in the theorem's natural-language proof.
- No trace identity, adic realization, Galois operator, or duality conclusion is present.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, the datum convention.
- `def-weil-scheme-morphism-properties` is a convention record, explicitly declaring no
  new notion. Its referenced Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  are the classes in the signature.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`. The dependency's
  `lean_audit.slopmaster2.state = closed` records these even though `lean` is absent.
  I read their definitions: sections are finite-subextension-valued continuous maps,
  restricted by precomposition, not all continuous maps into the algebraic closure.
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`: imports the recorded
  `ProEtale.boundedConstructible` and `ProEtale.BoundedConstructible` definitions from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`. The weak-Serre
  triangulatedness theorem is not needed here; no extra Serre assumption is added.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `boundedConstructibleUpperStar`, `boundedConstructibleLowerStar`,
  `boundedConstructibleUpperStarLowerStarAdjunction`,
  `boundedConstructibleLowerShriekOfCompactification`, and
  `boundedConstructibleLowerShriek`. I read the full current published source via
  `scompile.py --source`; these are precisely the restricted/assembled functors of the
  dependency records. Their source uses scheme universe u and abelian coefficients u+1.
- `Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial`:
  `WeilConjectures.FiniteFieldDatum.relativeFrobenius_isFinite_isRadicial`, imported as the
  recorded geometric proof dependency. The published model interface proves the same
  finite-iterate geometry as `IsModelFrobenius.isFinite`; the theorem docstring retains
  the DAG's finiteness induction and finite-implies-proper route.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Proper`:
  `AlgebraicGeometry.IsFinite.instCompScheme` and `IsProper.instOfIsFinite`.
- `WeilConjectures.TraceFormula.Statement`: the named implementation from
  `nt-assume-trace-formula`, including `IsModelFrobenius`,
  `compactCohomologyFrobeniusComparison`, `weilCompactCohomology`, and
  `WeilBoundedConstructibleOfEnd.globalOperator`. I read its current full source using
  `scompile.py --source`; the assumption theorem itself is not invoked.
- I also read the published full signatures/docstrings in `TraceFormula.Basic`,
  `Derived.BoundedConstructiblePullback`, `Derived.ShriekComposition`, and
  `BaseChangeTheorems.ProperLowerShriek`. Proper coincidence is constructed through the
  trivial compactification and its independence comparison; composition uses the
  chosen compactifications and the specified exchange map. The helpers use those
  exact declarations without replacing them by arbitrary isomorphisms.

Edge cases checked: r=1 and r=2; empty X; zero M and zero Weil object; X=Spec k;
non-reduced X₀; nonproper X such as the affine line. No reducedness or properness of
X is requested. Positivity excludes r=0 in the theorem although the naming helpers
also have meaningful zero-iterate data. All universes and variables are declared;
`autoImplicit` is disabled. A temporary `#check @...` verified the entire elaborated
signature, including algebraic closure and both model property instances; it was removed.

Searches made:

- `msearch.py ... leanfinder`: “The compact support model Frobenius comparison is the
  adjunction unit followed by proper direct image coincidence and lower shriek composition,
  natural in the coefficient complex”. Eight hits: condensed locally constant adjunctions,
  ordinary module pushforwards and related functors; none states this comparison.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.unit, CategoryTheory.NatTrans`.
  One hit, `TopCat.adj₂_unit`, unrelated.
- `msearch.py ... grep`:
  `compactCohomologyFrobeniusComparison|weilCompactCohomology|properUnitCondensed`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: “Compact support Frobenius comparison equals the unit of
  derived pullback and pushforward followed by proper comparison and composition”.
  Eight hits, including generic pullback comparison, derived functor units and ordinary
  sheaf-module adjunction lemmas; none gives the project-specific statement.
- `rg` on the upstream source checkout and `lean/Sheaf` for the implementation names,
  the node id, and `modelCompact|properUnit.*[Cc]ondensed` found no existing statement or
  name collision. The upstream local checkout lacks the newer interface; the authorized
  published-source reads supply it. The concrete comparison itself exists as a definition,
  but there is no theorem including its identity-removal normalization, naturality and
  actual-globalOperator formula. No independent missing notion or dependency repair is needed.

Validation: `scompile.py Q26 lem-zl-model-compact-comparison-unit ...` passed for both
its sandbox and its actual module path. All four definitions have real data, and the
single theorem's proof is only `sorry`. The final delivery dry run repeats compilation
and the server preflight.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

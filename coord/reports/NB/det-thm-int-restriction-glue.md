## Worker report

The module `Sheaf.SixFunctors.IntegralRestrictionGlue` states both clauses of
`det-thm-int-restriction-glue`. Its only postponed theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction.integralRestrictionGlue`.
The assertion predicate packages the clauses without adding mathematical assumptions.
The three helper definitions construct actual full inclusions and restricted functors;
none chooses a right adjoint or contains postponed data. The theorem docstring gives
all eight DAG proof steps and their dependencies.

Hypotheses and clauses, matched to Lean:

- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite extension inside the fixed
  algebraic closure is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. Its condensed
  valuation ring is exactly `Profinite.padicIntegersRingObj ℓ E.val`, with its induced
  adic topology. This coefficient specializes the generic assertion predicate.
- The base is `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`: prime ring characteristic expresses characteristic p > 0.
- Each scheme in each clause has `[X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact (X ↘ Spec (.of k))]`,
  and `[IsSeparated (X ↘ Spec (.of k))]`. The same binders for Y appear in clause 2.
  These spell out the standing setting, rather than imposing a dimension bound.
- Clause 1's ambient M is `M : Ambient Λ X`, the existing unbounded derived category
  of module objects over the pulled-back condensed ring.
- Its finite family is `(I : Type w) [Finite I] (U : I → X.Opens)`; the open-cover
  hypothesis is `iSup U = ⊤`. The index universe w is independent; no nonempty
  hypothesis excludes the empty cover.
- The local hypothesis is `∀ i, generators Λ (U i).toScheme
  ((pull Λ (U i).ι).obj M)`. The existing `pull` is the actual total derived inverse
  image, hence the open restriction; `generators` is exactly the recorded
  `constantModelBoundedConstructible` predicate, not upstream's broader predicate.
- The first conclusion is `generators Λ X M`.
- Clause 2's morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
- The compactification c, preservation proof h, functor G and adjunction adj are
  universally quantified representatives of the adjunction already supplied by
  `det-prop-int-brown-adjoint`. They are not an assumption of preservation under G:
  the latter is a conclusion. The left functor is the recorded
  `lowerShriek Λ c.obj.obj h`, literally the restriction of Rp_* D(j_!).
  Universal quantification states the conclusion for every representative of the
  unique Brown adjoint, so it applies in particular to the previously supplied one.
- Preservation of Dbc under f^! is the existentially asserted proof
  `hG : ∀ K : (localizing Λ Y).FullSubcategory,
  generators Λ Y K.obj → generators Λ X (G.obj K).obj`.
  This includes every constructible input through `constructibleInclusion`.
- Preservation under Rf_!, needed to type its restriction, is the asserted hF;
  it is already part of `det-prop-int-brown-construction`, and is not assumed here.
- Restriction of the adjunction is `∃ adj' : restrictedLowerShriek Λ c.obj.obj hF ⊣
  restrictedUpperShriek Λ G hG`, followed by the equation of Hom equivalences for
  every A, B and m. After forgetting full-subcategory membership, `adj'.homEquiv`
  equals `adj.homEquiv` on exactly the same ambient morphism. This specifies the
  inherited adjunction (and hence unit/counit), not just an unrelated adjunction
  between abstract equivalent categories. Naturality is part of `Adjunction`.

Dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, the recorded
  standing Nagata convention, is available through IntegralBrownAdjoint's imports.
  The theorem quantifies over its boundary-compactification representatives because
  the recorded Brown adjunction does so; no second compactification is chosen.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and
  `ConstantModelBoundedConstructible`, using `IsConstantModelConstructible`, are
  the Dbc notion reused via `generators`. Its finite scalar models, finite
  constructible stratifications and ordinary boundedness were read in full.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients` (and its imported LocalizingClosure):
  `CategoryTheory.localizingClosure` and `IsLocalizingSubcategory` provide the
  ordinary closure used by the recorded `localizing`. No derived completeness is
  introduced. The literal inclusion uses the defining intersection's generator map.
- `Sheaf.SixFunctors.IntegralLocalizingCompactSupport`:
  `IntegralCompactSupport.Ambient`, `pull`, `image`, `generators`, `localizing` and
  `integralLocalizingCompactSupport`. The actual functor definitions and theorem
  signature were read; the restricted left functor uses precisely `image`.
- `Sheaf.SixFunctors.IntegralBrownAdjoint`:
  `IntegralCompactSupport.lowerShriek`, `brownAdjointAssertions`, and
  `exists_integralBrownAdjoint`. The full signature, uniqueness and normalization
  clauses were read. There is no exported chosen exceptional inverse image, so the
  theorem uses the supplied G and adjunction as arguments, just as RestrictionLocal
  already does for the general Brown adjunction.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`:
  `ObjectProperty.ιOfLE`, `lift`, and `homMk` construct the full restrictions.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicIntegersRingObj`, whose full declaration and topology docstring
  were read in the read-only side framework.

All recorded proof-dependency modules are imported, including the exact restriction,
integral coefficient limit, weakly-etale localization, local charts and integral
inverse-image statements. Mathlib proof leaves import Noetherian and Constructible;
the Proetale site is already in the public dependency closure. Three proof nodes
currently have no recorded module: `det-sf-mate-open-restriction`,
`det-thm-int-restriction-line`, `det-thm-int-restriction-closed`. There is consequently
no proof-only import for those nodes yet. They are not needed to elaborate this
statement, and their named proof steps remain in its docstring.

Edge cases checked before writing: an empty index type forces X empty by the cover
condition, and gives the zero category as intended; a singleton cover permits X
itself; repeated or empty opens are allowed; the zero complex is included; local
cohomological intervals need not have a preassigned common bound. All finite
extension coefficients are included, and the only characteristic restriction is
exactly p > 0, p ≠ ℓ. Neither a Noetherian hypothesis in addition to the setting,
derived completeness, finite Tor amplitude nor a Krull-dimension bound is imposed.
The localizing category and both full subcategories use the same ambient category,
so the two Hom expressions refer to the identical objects and arrows.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Bounded constructibility of integral sheaf complexes is
  local for finite open covers and exceptional inverse image preserves bounded
  constructible complexes"`: eight hits, all constructible-subset/topological or
  morphism-locality lemmas, including `Topology.IsLocallyConstructible.of_isOpenCover`;
  none states either integral module-object conclusion.
- `msearch.py ... loogle 'CategoryTheory.Adjunction.restrictFullyFaithful'`: six hits
  in Mathlib.CategoryTheory.Adjunction.Restrict. Read the full general construction;
  it supplies the elementary last proof step, not the integral preservation theorem.
- `msearch.py ... grep 'boundedConstructible|exceptionalPullback|upperShriek'
  CategoryTheory`: zero Mathlib hits in that directory.
- `rg` over upstream WeilConjectures and project lean/Sheaf for the node id and
  constructible/open-cover patterns: upstream Etale/Derived/Stability/UpperShriek
  has `constructibleTorAmplitudeIn_of_openCover`, read its signature. It uses the
  small etale site with discrete scalar modules and prescribed Tor intervals, not
  this condensed integral module-object pro-etale category.
- Read side-framework ModuleObject/Derived/UpperShriek: its boundedConstructible
  adjunction is constructed directly in the broader upstream Dbc and does not assert
  restriction of this Brown adjunction or finite-open locality for finite constant
  models. It is not an exact existing match.
- `rg` for `integralRestrictionGlue|IntegralRestriction` in Mathlib, upstream and
  lean/Sheaf: only unrelated integral scalar restriction names in the project;
  no declaration collision. The node-id search upstream returned no match.

Validation: scompile.py compiled both the sandbox module and its real library-path
form cleanly (only the permitted postponed theorem), after compiling the current
IntegralBrownAdjoint and RestrictionLocal overlays.

No statement correction, dependency repair or new DAG node was necessary.
No STATEMENT-DISPUTED finding.

## Second reading by NB

I reopened the node and the emitted module and checked the expanded assertion
predicate, rather than checking only the short theorem signature. This is a worker
self-check; under the dispatcher's instruction I did not start another agent. The
maintainer supplies the independent review of this delivery.

The first conjunct binds an arbitrary ambient object and finite open family, assumes
only coverage and local Dbc membership, and concludes global Dbc membership. The
second binds exactly the standing morphism and the preexisting Brown adjunction;
hG is concluded rather than hypothesized. hF and hG make the two restricted functors
well-typed, and the final Hom equality makes their adjunction the inherited one.
I checked that each restricted object is the same ambient derived object and each
map is the original map wrapped by homMk. I checked all scheme-over-k binders and
both characteristic facts. The use of finite constant models, independent finite
index universe and empty cover was confirmed. No mismatch or node change was found.

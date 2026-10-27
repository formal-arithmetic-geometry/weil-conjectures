## Worker report

The module `Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification` states
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientDerivedExchangeIdentification`.
Its only postponed proof is that theorem. All helper definitions have real bodies;
`DerivedEdgeComparison` is a structure of the comparisons and their normalization equations,
not a new module category or a chosen arbitrary equivalence.

The inherited BLOCKED report concerned the stage-1 delivery. The current node has a
reviewed stage-1 split and no Lean record. The 2026-10-22 stage-handoff paragraph of
`coord/brief-stage2.md` explicitly authorizes this stage-2 statement delivery. The accepted
statement and five-step proof are preserved. There is no statement correction or disputed
mathematical assertion.

Hypotheses and objects, clause by clause:

- The finite discrete commutative ring is `A : Type u`, `[CommRing A]`, `[Finite A]`,
  `[TopologicalSpace A]`, `[IsTopologicalRing A]`, `[DiscreteTopology A]`. The topology
  structures express the discrete condensed realization, with no additional algebraic
  restriction. In particular `Nontrivial A`, a prime, or characteristic invertibility
  is never assumed.
- `X' X C Y : Scheme.{u}` and the four arrows `a`, `f'`, `f`, `c` have exactly the
  displayed domains. The two topological classes `CompactSpace` and
  `QuasiSeparatedSpace` are required at all four corners, rendering qcqs schemes.
  Mathlib's `quasiSeparatedSpace_iff_quasiSeparated` identifies the latter with the
  structure-morphism definition in the dependency.
- `sq : ChosenCartesianSquare a f' f c` retains the chosen pullback identification,
  projection equations, and the precise commutativity equality used in both square maps.
- `coefficient A` is the existing continuous-function condensed coefficient ring.
  `Internal A T` is the existing internal module category over its scheme pullback.
  The size convention is explicit: schemes and the finite ring live in `u`; the small
  pro-etale site's object universe is `u+1` and its morphism universe is `u`; abelian
  groups and fixed scalar modules live in `u+1`. `ULift.{u+1} A` is the existing
  coefficient encoding, so there is no forced equality of site object and hom universes.
- `E : ∀ T, Encoding A T` is the recorded normalized coefficient equivalence. It is
  not an arbitrary derived equivalence: `ordinary_functor`, `fixed_functor`, and
  `normalization` fix its section-action and constant-scalar functors.
  `Encoding.derivedFunctor` is definitionally `e.fixedDerived.functor`, the actual
  termwise extension. This is the fixed-scalar presentation of the ordinary
  pro-etale derived category used in the displayed statement.
- `internalPull` and `internalPush` name the recorded total derived functors of the
  whole internal composites. `ordinaryPull` and `ordinaryPush` are the already defined
  generic total derived functors of ordinary module-sheaf inverse/direct image.
  The direct public import of ordinary `Derived.UpperLowerStar` supplies the published
  exactness, composition, resolution and adjunction interfaces. Exact inverse image is
  canonically its termwise extension via the existing
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- The theorem supplies six `DerivedEdgeComparison` records for the four edges and the
  two composite paths. `heartDirect` and `heart_normalization` specify identity on the
  actual underlying abelian sheaf; `Encoding.underlyingIso` is derived from the two
  encoding functor equalities, with body `Iso.refl` after rewriting them.
- `direct` is the derived direct-image comparison, and `direct_normalization` is its
  universal right-derived comparison-unit equation on every complex. `internalRightUnit`
  and `ordinaryRightUnit` are the existing `derivedCochainRightUnit` applied to the
  actual generic `rightDerivedFunctorUnit`. `Encoding.factors` is exactly the canonical
  termwise-localization factorization. Thus the direct comparison is normalized, not
  just an endpoint isomorphism.
- `inverse` compares the actual derived pullbacks. `unit` and `counit` explicitly use
  `internalAdj` and `ordinaryAdj`, which are definitions of the published derived
  adjunctions without a change of adjunction data. Together with the normalized direct
  comparison these determine the canonical pullback mate and identify both adjunctions.
- The two `compositionCompatible` clauses identify the two actual pullback compositors
  on arbitrary derived inputs. They use the internal and ordinary
  `leftDerivedUpperStarComp`, with the same two paths `a ≫ f` and `f' ≫ c` from `sq`.
  The composite-edge comparisons are normalized by the same equations, so these are
  comparisons of the specified canonical maps, not choices of unrelated isomorphisms.
- `exchangeSourceIso` is the prescribed source vertical map: `a_c` followed by
  `c^*(b_f)`. `exchangeTargetIso` is `b_f'` followed by `Rf'_*(a_a)`. Their definitions
  compose the edge isomorphisms with only the canonical functor associators.
- The displayed equality maps `CondensedRing.condensedAmbientExchange` through the
  termwise equivalence and compares it to `ProEtale.derivedBaseChangeMap` for
  `sq.toCommSq`. Both definitions are the actual unit--canonical-square--counit mates.
  No comparison arrow has been substituted for either horizontal map.
- Each edge and vertical comparison is a natural isomorphism, and the final equality
  quantifies over every unbounded internal `L`; this gives the requested naturality
  in `L`, including all constructible inputs.
- The last conjunct quantifies over exactly
  `ConstantModelConstructibleFiniteTor (coefficient A) X`. It supplies a bounded-below
  proof `h` for its ordinary realization and a retained
  `W : Scheme.FixedEtaleOriginWitness ... ⟨E_X L,h⟩`. The existing witness has fields
  `complex` and `iso`; its `iso` is the exact specified
  `comparisonUpperStar.mapDerivedCategory` comparison with `E_X L`.
  `Etale.DerivedCategory.isBoundedConstructible ... W.complex.obj` requires this same
  retained etale antecedent to be bounded constructible. Thus it gives both M and its
  isomorphism, rather than only a bounded-below or arbitrary antecedent.
- No `IsProper` or `IsIso` hypothesis is present for either exchange map. The rectangle
  is stated on all unbounded objects; constructibility and finite Tor amplitude enter
  only in the etale-origin conjunct, as in the source.

Dependency declarations read and used:

- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`, and the
  reexported `derivedUpperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` and its inherited `CommSq`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` and its public encoding module:
  `FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence`, `Encoding`,
  `Encoding.fixedDerived`, `coefficient`, `Internal`. The theorem already supplies
  normalized encodings; this item is uniformly stated for such encodings.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible` and `ConstantModelConstructibleFiniteTor`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`; its left adjoint is the existing
  `ProEtale.comparisonUpperStar` used by `FixedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness` with its full antecedent and isomorphism fields.
- `Sheaf.Paper.CondensedAmbientExchange`:
  `CondensedRing.condensedAmbientExchange` and its canonical square construction.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  `ProEtale.derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarComp`, and
  `derivedBaseChangeMap`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, added as the existing dependency
  `def-weil-pbc-constructible-complexes`.
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`:
  `CategoryTheory.derivedCochainRightUnit`, added as the existing dependency
  `def-derived-cochain-right-unit`; `exactEquivalenceDerivedSquares` is a proof input.
- The metatheoretic size convention has no Lean declaration, as its record says.
  `Mathlib.Topology.Defs.Filter.CompactSpace` and the scheme quasi-separated-space
  equivalence in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` are reused.

The five-step natural-language proof is in the theorem docstring. Its plain proof imports
retain the recorded exact-equivalence square, normalized adjoint square, constant-scalar
geometric adjunctions, internal-operation transport, coefficient-sections normalization,
arbitrary-finite-ring constructible origin and pullback-composition modules. The remaining
composition and exact-factorization dependencies are already public upstream/Mathlib
imports: `CondensedRing.lowerStarComp`, `CondensedRing.upperStarComp`,
`Adjunction.leftAdjointCompIso`, `unit_conjugateEquiv_symm`, and
`Functor.mapDerivedCategoryFactors`. No proof has been supplied in stage 2.

Edge cases checked before and during formulation:

- The zero coefficient ring is allowed; no step or witness needs nonzero scalars.
- Empty schemes and empty finite stratifications are allowed. The equivalence and
  witness use the actual sheaf categories, including their zero objects.
- Identity arrows and identity Cartesian squares use the specified adjunctions and
  canonical compositors. Normalization prevents arbitrary automorphisms of endpoints.
- Arbitrary finite commutative rings are allowed, including nonfields and rings with
  nilpotents; no characteristic restriction has been added.
- The comparison holds for genuinely unbounded complexes. Only the origin clause
  requires the bounded constructible finite-Tor predicate; no truncation is inserted
  into either exchange map.
- Nonproper arrows are admitted, and horizontal exchange maps need not be invertible.
- The coefficient lift keeps the full small-site universes; it does not collapse them.

Sources opened: the exact blueprint refinement proof (2), Stacks `proetale.tex`
lemma-compare-constructible-derived (09AL), and `sites-modules.tex`
lemma-adjoint-pullback-pushforward-modules (03D7) and
lemma-push-pull-composition-modules (03D8). The current node's reviewed proof explains
why finite coefficients give finite constant stalk models before applying 09AL.

Searches for an existing statement:

- `msearch.py leanfinder`: “Finite coefficient equivalence transports internal module
  derived adjunctions and base change exchange to ordinary proetale sheaves”. Eight
  hits about formally etale algebras/Kaehler base change; none states this theorem.
- `msearch.py loogle`: `CategoryTheory.Adjunction, DerivedCategory`: zero hits.
- `msearch.py grep`, Mathlib `CategoryTheory`:
  `exchange.*[Ee]quiv|[Ee]quiv.*exchange`: zero hits.
- `msearch.py leansearch`: “exact equivalence of sheaf categories preserves base change
  adjunction mate”: eight hits, including `CategoryTheory.mateEquiv` and sheaf category
  equivalences. These supply the generic mate operation, not finite coefficient
  realization, normalized unbounded operations, or the etale-origin witness.
- `rg` over both project roots for finite/exchange identification, plus the exact node
  id: no declaration for this item. Many finite base-change theorems occur, but none
  states the internal-to-ordinary normalized exchange with the retained origin pair.
  The exact prospective names also had no existing declaration.

No new nodes and no dependency modules are introduced. Two existing landed definition
nodes are added to `stmt_deps` to record the bounded-constructible predicate and the
cochain-localized comparison unit actually used by the statement. All other node fields
are preserved. The owning module's helper declarations are listed in `lean.declarations`.

Validation uses only `scompile.py` and the prescribed delivery wrapper. During diagnosis,
a missing direct ordinary-derived import caused recursive site-smallification instance
search; importing the published ordinary `Derived.UpperLowerStar` fixed that issue.
All delivered statements use `autoImplicit false` and explicit universes. Final compile
and preflight results are recorded by the delivery tools.

The final module also names `internalCompIso`, `ordinaryCompIso`, `internalExchange`
and `ordinaryExchange` with fully explicit endpoints. Their bodies are exactly the
published canonical compositors and exchange mates named above. This shares structural
arguments during elaboration; it adds no map, choice, hypothesis or independent notion.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

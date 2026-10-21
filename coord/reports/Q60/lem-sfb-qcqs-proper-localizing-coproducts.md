## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts` states
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_localizing_preservesCoproduct`.
Its sole theorem has proof `sorry`. No definition, dependency record, statement,
or proof plan is changed; no new node is needed.

The source is the current blueprint, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first
paragraph. The node's explicit qcqs-base and coefficient scope is retained. The
proof docstring reproduces all six steps of the DAG, including the uniform tail
input rather than silently using a result that assumes a field base.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The commutative condensed coefficient is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. Its allowed coefficient alternatives, finite extension in a
  fixed algebraic closure, valuation ring, and specified topologies are expressed
  by `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`, the recorded declaration of
  sk-def-localizing-closure. There is no separate E binder because E appears only
  in the list of admissible coefficients: its finite-subextension datum is bound
  in this predicate. This reuses the dependency's whole coefficient convention,
  including its retained continuous-algebraic-closure compatibility clause.
- `condensedRingObj Λ X` is precisely the pulled-back coefficient Λ_X, with the
  analogous coefficient at Y in the codomain of the recorded derived functor.
- `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X))` is the ordinary unbounded module-object derived category.
  There is no derived-complete or constructible-derived-category replacement.
- The schemes are `{S X Y : Scheme.{u}}`. The base is qcqs via `[CompactSpace S]`
  and `[QuasiSeparatedSpace S]`. `CompactSpace` has no Hausdorff requirement.
- The proper maps are `(q : Y ⟶ S) [IsProper q]` and
  `(f : X ⟶ Y) [IsProper f]`. q is retained even though only f occurs in the
  resulting functor. Finite type, quasi-compactness and quasi-separatedness of f
  are consequences of properness, rather than extra hypotheses.
- `(I : Type (u + 1))` is the fixed small indexing universe. There is no
  `Nonempty`, `Finite`, or countability assumption. Scheme.ProEt has its existing
  object/hom universe convention, and coefficients are in Ab.{u+1}; no site
  universe is forced equal to its morphism universe.
- `L : I → DerivedCategory ...` is the family in the ambient category.
- `hL` places every `L t` in
  `localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X ⊓
  fun K ↦ DerivedCategory.finiteTorAmplitude _ K)`. The first generator predicate
  includes boundedness and exactly the finite constant scalar-model notion of
  sk-def-sfb-constructible; the second is finite Tor amplitude. The localizing
  closure is the dependency's intersection of full replete triangulated
  subcategories closed under the ambient sums in precisely this index universe.
- The conclusion is
  `PreservesColimit (Discrete.functor L) (moduleObjectDerivedPushforward Λ f)`.
  This is exactly the canonical comparison assertion, without having to name a
  chosen coproduct instance in the statement. Mathlib's definition in
  CategoryTheory/Limits/Preserves/Basic.lean sends every colimit cocone to a colimit
  cocone. For a discrete family it sends the ambient coprojections to their
  derived-pushforward images. In Preserves/Shapes/Products.lean,
  `PreservesCoproduct.of_iso_comparison` proves the implication from invertibility
  of `sigmaComparison`; conversely the instance following
  `PreservesCoproduct.inv_hom` proves invertibility from this `PreservesColimit`.
  Thus this is not an arbitrary isomorphism or an assertion about sums computed
  in the localizing subcategory. Both coproducts exist: internal modules are
  Grothendieck abelian, and the imported derived coproduct theorem provides the
  ambient sums in universe u+1.
- There is no common bound on L, no completeness condition on its sum, and no
  field, characteristic, Noetherian, or finite-dimensional-base hypothesis.

Dependency declarations read and used:

- sk-def-localizing-closure:
  `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` and
  `CategoryTheory.localizingClosureOfSize` (with
  `CategoryTheory.IsLocalizingSubcategoryOfSize`).
- sk-def-sfb-module-derived-pushpull:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
  Its body is exactly `(lowerStar Λ f).rightDerivedFunctor`, the total right
  derived functor of the full underived composite; no factorwise derivation.
- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`, built from
  `IsConstantModelConstructible`, `IsFiniteConstantStratified`, and
  `HasFiniteConstantLocalModel`; its `ConstantModelConstructibleFiniteTor`
  abbreviation uses the same generator predicate as hL.
- def-weil-size-convention has a metatheoretic convention record, not a module
  declaration; implemented here by the explicit universe u and u+1 indexing.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  `AlgebraicGeometry.IsProper`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`,
  available through the proper-morphism import and required by the proof plan.
- def-weil-quasi-separated-morphism:
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated,
  `AlgebraicGeometry.QuasiSeparated`; its scheme convention is
  `QuasiSeparatedSpace` (the terminal-map equivalence is in this module).
- def-weil-pbc-quasi-compact-scheme: Mathlib.Topology.Defs.Filter,
  `CompactSpace`, as recorded.

All already-stated proof-dependency modules are imported. For mathlib_match-only
nodes these are the modules named in their matches, including the standard
t-structure, separated-implies-quasi-separated, long exact homology sequence, and
homology detection of isomorphisms. `lem-sfb-qcqs-proper-hull-tail-bound` has no
recorded declaration yet, so it has no import. Its full role and use in degrees
n and n+1 are preserved in the proof docstring; this stage states the item rather
than proving the tail estimate.

Edge cases checked before writing and against the final signature:

- Empty I is permitted. Discrete-colimit preservation then means preservation
  of the initial object, the required empty coproduct; exact derived pushforward
  sends zero to zero.
- Zero objects, the zero coefficient ring, and empty schemes are not excluded.
  A zero ring is allowed by the finite admissible coefficient case.
- The identity proper map gives the usual identity coproduct comparison.
- Families with no common lower or upper cohomological bound are admitted:
  only hull membership occurs in hL, with no quantified common integer.
- Primes equal to residue characteristics and bases of unbounded Krull dimension
  are not excluded. Properness and qcqs are exactly the geometrical hypotheses.
- The sum need not be derived complete; only the ordinary ambient coproduct
  universal property is used. Index types occupy the same u+1 universe used in
  the localizing-closure predicate.

Searches (2026-10-21):

- msearch.py leanfinder, query: "Proper derived pushforward preserves small ambient
  coproducts on the localizing closure of constructible finite Tor complexes over
  a qcqs base". Eight hits, concerning condensed AB4/AB5, localizations,
  scheme extensivity and quasi-compact base change. No matching proper
  derived-pushforward theorem.
- msearch.py loogle, query:
  "AlgebraicGeometry.IsProper, CategoryTheory.Limits.PreservesColimitsOfShape".
  Zero hits.
- msearch.py grep, query:
  "proper.*(coproduct|direct.sum)|preserves.*coproduct". Twenty-five hits,
  concerning other coproduct constructions and preservation statements.
- rg on lean/WeilConjectures and lean/Sheaf for localizingClosureOfSize,
  localizing/coproduct and boundedBelow/coproduct terms; also searched the exact
  item ID in WeilConjectures, with no match. The nearest existing theorem is
  `ellAdic_localizingLowerStar_preservesCoproducts` in
  Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts. Its full signature
  assumes finite-type separated schemes over a field with prime characteristic
  distinct from ℓ, and a different coefficient certificate, so it is not this
  node's statement. The upstream
  `preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar` in
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
  requires two extra heart hypotheses and uses another generator predicate;
  it likewise does not already state the item.

No STATEMENT-DISPUTED flag and no node fault. The example module requested in the
brief has been withdrawn; its node now points at the identical upstream
WeilConjectures.CategoryTheory.CompactObject. The module follows the current
project header, public-section, explicit-universe and docstring conventions.

Validation: scompile.py passed both the sandbox and actual library module
compilation cleanly (20.7 s and 21.9 s), with no warnings or errors. Delivery
preflight is run with deliver2.py --no-push before the actual delivery.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

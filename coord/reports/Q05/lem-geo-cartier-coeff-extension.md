## Worker report

This repairs the H3 return at immutable head `6797fe139f26`. The retained packet's
initial dry run passed (commit `0b5ae626ef`), but its existential `gAB`, `gBC`,
and `gAC` were not constrained to the coefficient-unit direct-image maps.
The repaired file constructs those maps and states the result about their actual
adjuncts. No arbitrary maps or isomorphisms are existentially chosen in the theorem.
The natural-language node is unchanged; comparison with the current shared node
found no difference outside the `lean` field.

The module is `Sheaf.SixFunctors.GeoCartierCoeffExtension`, in namespace
`AlgebraicGeometry.Etale`. Its real constructions are:

- `supportedConstantModule`: ordinary `lowerStar` of the constant regular module
  `ModuleCat.of A A` on `D`.
- `coefficientUnitModule φ i`: first construct the constant coefficient unit on
  `D` via `constantSheafAdj`. Its adjoint global-section map is
  `LinearMap.toSpanSingleton A _ x`, where `x` is the constant section `1 : B`
  obtained from the B constant-sheaf adjunction unit. The section's A-action is
  restricted along the specified `φ`. Thus a constant `a` goes to `φ a`.
  Apply `(lowerStar (ModuleCat A) i).map` and the inverse of the existing
  `lowerStarRestrictScalarsIso φ i`. This is exactly the direct image of the
  coefficient unit, with its canonical target identification.
- `supportedConstantDerived`: the degree-zero `DerivedCategory.singleFunctor`
  image of the ordinary supported constant sheaf.
- `coefficientUnitDerived φ i`: apply that single functor to
  `coefficientUnitModule φ i`, then the inverse component of the canonical
  `Functor.mapDerivedCategorySingleFunctor` for exact scalar restriction.
- `supportedCoefficientComparison φ i`: by its defining equation, the inverse
  adjunction hom-equivalence image of `coefficientUnitDerived φ i`, for
  `Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars ... φ)`.

These are helpers of this node's own specified morphism; all are listed in
`lean.declarations`, with source and blueprint docstrings. None uses `sorry`
or selects data from an existence theorem. Only the node's theorem has proof
`sorry`, with the complete five-step natural-language proof in its docstring.

Each hypothesis and clause is rendered as follows:

- Schemes: `{D Z : Scheme.{u}}`; closed immersion: `i : D ⟶ Z` and
  `[IsClosedImmersion i]`.
- Finite commutative rings: `{A B C : Type (u + 1)}` with each `CommRing` and
  `Finite` instance explicit. Their maps are `φ : A →+* B`, `ψ : B →+* C`.
- Small étale sites: `D.smallEtaleTopology`, `Z.smallEtaleTopology`.
  Constant sheaves and ordinary direct image are precisely the recorded
  `constantSheaf` and `lowerStar` constructions in `supportedConstantModule`.
- Unbounded module derived categories are `DerivedCategory (Sheaf
  Z.smallEtaleTopology (ModuleCat.{u + 1} A))` and the B/C analogues.
- Derived scalar extension is the existing `pbcFixedScalarExtension`, also
  recorded as `scalarExtension` by the updated derived-change-of-rings interface;
  its right adjoint is actual termwise `Sheaf.derivedRestrictScalars`.
- The specified comparison is `supportedCoefficientComparison`, whose defining
  equation fixes it as the adjunct of the constructed direct-image unit.
  The first three conjuncts assert `IsIso` for φ, ψ, and ψ.comp φ.
- Coefficient naturality: the fourth conjunct says the actual unit for ψ.comp φ
  equals the actual φ unit followed by restriction of the ψ unit and
  `Sheaf.derivedRestrictScalarsCompIso ... rfl`. Together with the final
  adjunct-transitivity equation this is the naturality square for
  `A → B → C` (the coefficient target map `B → C` is arbitrary).
- Identity coefficients: `supportedCoefficientComparison (RingHom.id A) i`
  equals the component of the existing canonical
  `ProEtale.normalizedOriginScalarUnit ... (RingHom.id A) rfl`. This is the
  adjunction mate of the sectionwise identity restriction map, so the clause
  fixes the identity normalization rather than choosing an arbitrary isomorphism.
- Successive extensions: the final equality is extension of the actual φ
  comparison followed by the actual ψ comparison, equal to the component of
  `pbcFixedScalarExtensionComp ... φ ψ (ψ.comp φ) rfl` followed by the actual
  composite comparison. That associator is defined by `Adjunction.leftAdjointCompIso`
  from the canonical restriction composition isomorphism.
- Neither φ nor ψ is required flat; no boundedness, nonempty-scheme, nonzero-ring,
  Noetherian, or Cartier hypothesis has been introduced.

Dependency declarations used (all sources read):

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`, `constantSheafAdj`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`.
- The recorded `WeilConjectures.AlgebraicGeometry.DerivedCategories` interface
  uses the same `DerivedCategory`/ModuleCat-valued sheaf encoding;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` supplies the single functor.
- `Sheaf.Paper.EtaleDerivedScalarTensor`: updated record of
  `lem-pur-derived-change-of-rings`, with `scalarExtension` the existing
  `pbcFixedScalarExtension` and the canonical normalized `scalarTensorIso`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; its fixed-ring adjunction
  is exposed by `Sheaf.Paper.WitnessCompatibility` via
  `pbcRestriction_isRightAdjoint` and `pbcFixedScalarExtension`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`;
  the fixed-ring canonical comparison used here is
  `ProEtale.pbcFixedScalarExtensionComp` from `WitnessCompatibility`.
- `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`:
  `lowerStarRestrictScalarsIso`, a sectionwise identity.
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses`:
  `ProEtale.normalizedOriginScalarUnit`; it uses the canonical
  `normalizedOriginRestrictionUnit` and `Adjunction.leftAdjointIdIso`.
- The recorded proof dependency modules for geometric stalks, their monoidal
  pullback interpretation, constant stalks, finite direct-image stalks, exactness,
  and conservativity are imported for the five-step proof plan.

Edge cases reread: `D` empty, `D = Z` and `i = 𝟙 Z`, both coefficient maps
identities, `B` or `C` the zero ring, and nonflat maps such as
`ZMod 4 → ZMod 2 → ZMod 2`. The unit construction uses constant section `1`,
which becomes the unique zero section on the empty site or for the zero ring;
no existence of a geometric point is assumed. The identity clause concerns the
same defined adjunct as the other clauses. All universes and variables are
explicit, and there are no `let` binders in the theorem's signature.

Searches retained from the delivered packet: `msearch.py` LeanFinder query
"derived scalar extension of a closed immersion pushforward of a constant finite
coefficient sheaf" returned generic unit/direct-image declarations, with no exact
comparison. Loogle `lowerStar, constantSheaf, derivedRestrictScalars` returned
zero hits (unknown `lowerStar`); Mathlib grep
`lowerStar.*constantSheaf|constantSheaf.*lowerStar` returned no hits. The retained
DAG searches also found no exact theorem. The source/project rg and item-ID grep
found no existing comparison declaration.

Additional repair searches: LeanFinder "canonical coefficient unit from a
constant module sheaf to restriction of scalars of another constant sheaf
followed by closed immersion direct image" returned generic
`SheafOfModules.unitToPushforwardObjUnit`, `unitHomEquiv`, and related declarations,
not the required ModuleCat-valued fixed-coefficient construction. Loogle
`constantSheafAdj, LinearMap.toSpanSingleton` gave zero hits with unknown
`constantSheafAdj`; Mathlib grep for
`coefficientUnitModule|coefficientUnitDerived|supportedCoefficientComparison`
gave zero hits. Direct rg over `WeilConjectures` and project `lean/Sheaf` likewise
found none of those names. Source inspection found and reused the existing
`constantSheafAdj`, `LinearMap.toSpanSingleton`, `lowerStarRestrictScalarsIso`,
`Functor.mapDerivedCategorySingleFunctor`, `pbcFixedScalarExtensionComp`, and
`normalizedOriginScalarUnit`; none was redefined.

No natural-language statement correction, new node, or dependency-node repair
was needed. No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q05

Repair self-check, performed in this worker because the dispatcher prohibits
starting other agents: I reread the node, source paragraph, current dependency
records, and repaired module clause by clause. The returned version's H3 defect
was real: labeling arbitrary existential maps as units in a report did not
identify them in Lean. They have been removed. I traced the actual map from the
B constant section `1`, through the A-linear span-singleton map and the inverse
constant-sheaf hom equivalence, then through ordinary direct image, degree-zero
embedding, exact restriction compatibility, and finally the derived adjunct.
Every map in the theorem now is that concrete construction.

The second reading also found that the former identity clause existentially
selected both its map and its natural isomorphism without linking them to the
specified adjunct. It now compares the same defined identity-coefficient
adjunct with the existing canonical scalar-unit isomorphism. The signature's
former `let` binders were removed by naming the concrete comparison construction.
I checked the directions of the ordinary restriction/direct-image comparison,
the derived-single-functor comparison, and the scalar associator. The full
natural-language proof and all proof-dependency imports are now supplied.
The source finite-ring and closed-immersion hypotheses, supported source objects,
coefficient naturality, identity, and composition clauses remain exactly those
of the unchanged node, including zero rings, empty schemes, and nonflat maps.

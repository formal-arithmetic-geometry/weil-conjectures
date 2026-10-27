## Worker report

The module `Sheaf.Paper.BoundaryFiniteTorDomains` states
`WeilConjectures.boundary_finite_tor_domains`. Its proof is `sorry`.
Three definitions of propositions package this one node's clauses, with real formula
bodies; they introduce no new geometric or coefficient notion. No definition contains
postponed data. The source is the first paragraph of the proof of
`cor-weil-boundary-duality-discharge`, read in the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`.
The current blueprint moved this result from the older path in the DAG's source record;
the existing node text and source record are preserved.

Hypotheses and conventions:

- The fixed finite-field datum is `D : FiniteFieldDatum.{u}`. Reading its structure
  shows `p`, positive `a`, `q = p^a`, the field with q elements, its algebraic closure,
  and its embedding. No field is replaced by an arbitrary algebraically closed field.
- The prime is `l : ℕ` with `[Fact l.Prime]`; `_hl : l ≠ D.p` is retained.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. The positive level is `n` with `hn : 1 ≤ n`.
  Each proposition uses the actual `Padic.coefficientExtensionRing l E n`, with
  `Padic.finite_coefficientExtensionRing l E n hn` supplying finiteness. The
  canonical `ULift.{u+1,u}` puts this ring in the required sheaf coefficient universe;
  it adds no coefficient assumption and changes neither multiplication nor modules.
- `Y : Scheme.{u}`, `aY : Y ⟶ Spec (.of D.k)` specify the k-scheme, and
  `[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]` are exactly separated
  finite type. Properness of Y is not assumed.
- Ordinary etale derived objects are `Etale.DerivedCategoryModule A W` (ordinary
  sheaves valued in `ModuleCat.{u+1} A`). Their bounded constructible finite-Tor
  predicate is the recorded `finiteTorConstructibleEtale l E n hn W` throughout.
  Its definition is bounded constructibility intersected with existence of integers
  a ≤ b bounding all degree-zero tensor tests. No perfectness or finite global
  dimension is substituted for finite Tor amplitude.
- Pro-etale objects in the last clause are ordinary fixed-A module-sheaf derived
  categories on `Scheme.ProEt.topology`. The recorded finite-coefficient realization
  and intrinsic-module presentations are imported, without redefining them.
  The coefficient universe u+1 and the existing derived-category instances implement
  `def-weil-size-convention`; no extra universe equality is imposed.

Conclusions, clause by clause:

- `BoundaryFiniteTorDomains` quantifies over every `W` and every `w : W ⟶ Y`
  with `[IsImmersion w]`. This is the recorded locally closed subscheme convention.
  It concludes `∃ hs ht hq` with `IsSeparated (w ≫ aY)`,
  `LocallyOfFiniteType (w ≫ aY)`, and `QuasiCompact (w ≫ aY)`.
  These are conclusions, not additional assumptions on the piece. They are passed
  explicitly to `BoundaryPieceFiniteTorDomains` only to type its canonical functors.
- `BoundaryPieceFiniteTorDomains` first asserts `IsNoetherian W`, whose Mathlib
  class includes locally Noetherian and quasi-compact. It asserts the actual ambient
  adjunction as `Nonempty (rightDerivedLowerShriek ... aW ⊣
  rightDerivedUpperShriek ... aW)` and separately that the right adjoint carries
  `DerivedCategory.TStructure.t.plus` into itself.
- The dualizing object is the existing `Etale.dualizingComplex ... aW`, definitionally
  the exceptional right adjoint applied to the coefficient unit. `Etale.verdierDual`
  is the existing derived internal Hom into this object, on the ordinary module-sheaf
  category. For every K in the recorded finite-Tor subcategory the next conjunction
  asserts preservation and `IsIso ((verdierDualDoubleDual ... aW).app K)`.
  Reading `Dualizing.lean` verifies that this is the evaluation transpose using the
  derived Koszul symmetry, not an arbitrary biduality map.
- Every closed `i : Z ⟶ W` is quantified by `[IsClosedImmersion i]` and invokes
  `BoundaryClosedFiniteTorDomains`. The composite `i ≫ w` is again an immersion
  into Y, so this includes exactly the closed pairs of pieces; no independent
  structure map or noncommuting k-structure is introduced. Taking W=T gives aT,
  and the structure map on Z is definitionally `i ≫ aT`.
- In the closed-pair proposition, `G` is precisely
  `Etale.rightDerivedUpperShriek (ModuleCat A) i`; `s` is the exact ordinary inverse
  image `(Etale.upperStar (ModuleCat A) i).mapDerivedCategory`. For a proper closed
  immersion the compact-support left adjoint is the usual derived direct image.
  The first conjunction explicitly asserts preservation of the same finite-Tor
  predicate by both s and G for every input L in that predicate.
- `DT` and `DZ` are the specified Verdier functors for aT and i ≫ aT.
  `∃ α : DT ⋙ G ≅ s.op ⋙ DZ` expresses the natural costalk isomorphism.
  Its component at `op (DT.obj (op L))` has source G(DT(DT L)) and target
  DZ(s(DT L)), exactly the displayed alpha in the node. The accompanying clause
  identifies P as `s.obj (DT.obj (op L))`, asserts its finite-Tor constructibility,
  and states invertibility of the actual composite
  `G.map ((verdierDualDoubleDual ... aT).app L) ≫ α.hom.app (op (DT.obj (op L)))`.
  Thus its source is U=GL and target is DZ P. No equation normalizing alpha against
  evaluation is imposed. Naturality is represented by a functor isomorphism, not
  unrelated componentwise choices.
- The last two `Nonempty` clauses explicitly state both dualizing isomorphisms,
  G omega_T,e ≅ omega_Z,e and Ri_p! omega_T,p ≅ omega_Z,p. The following
  `Etale.BoundaryCompositionCompatibility A i aT` supplies the specified
  pasted-counit normalization and naturality on bounded-below etale-origin inputs.
  Reading its definition shows that it uses the actual canonical
  `boundaryCompositionIso`, rather than an arbitrary comparison. Its values at
  `boundaryCoefficientPlus` are `boundaryDualizingEtaleIso` and
  `boundaryDualizingProIso` (equivalently `boundaryClosedDualizingIsos`). The latter
  is explicitly the comparison-unit transport through `boundaryOriginIso`.
  The pro-etale functor's definition is Rnu_* followed by G followed by nu^*,
  i.e. the specified C_Z G Rnu_T,*, and no ambient pro-etale adjunction is assumed.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Padic.coefficientExtensionRing` and fixed uniformizer quotient construction.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, with Mathlib's `DerivedCategory`,
  `DerivedCategory.Plus`, cohomology and standard t-structure.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, fixed-coefficient realization and comparison.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`; this records the intrinsic presentation,
  while this node's operations use the stipulated ordinary fixed-coefficient one.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale` and its imported
  `Etale.DerivedCategory.hasTorAmplitudeIn`.
- Mathlib `Morphisms.FiniteType`, `Proper`, `ClosedImmersion`, `Immersion`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsClosedImmersion`, `IsImmersion`.
  Read `IsImmersion.isImmersion_iff_exists` for the exact locally closed convention.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, and its canonical compactification
  presentation `rightDerivedLowerShriek`; `UpperShriek` gives its actual adjoint.
- `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`:
  `CategoryTheory.derivedInternalHomMixedUniverses`, retained as the general ringed
  interface; the ordinary fixed-A presentation uses the existing `Etale.derivedHom`
  of `Derived.Dualizing` and `Etale.verdierDual`, rather than a second internal Hom.
- `Sheaf.Paper.DualityPairing`: `Etale.AmbientDualityPairing` and
  `Etale.ambient_duality_pairing`; its canonical evaluation transpose is
  `Etale.verdierDualDoubleDual` in the upstream `Derived.Dualizing` module.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: recorded
  `ConstructibleExceptionalCoefficients.System`; its imported finite exceptional
  definition is `ProEtale.sfFiniteExceptionalFixed`. `BoundaryDualizingComposition`
  explicitly identifies this with the used upstream `ProEtale.rightDerivedUpperShriek`.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `ProEtale.siteComparisonDerivedPullbackPlus`; the ambient functor is its existing
  termwise counterpart `(ProEtale.comparisonUpperStar ...).mapDerivedCategory`.
- Proof interfaces are imported without public: `BoundaryEtaleAdjunctionRestriction`,
  `EtaleGeometricBiduality`, `EtaleTorFlatPullbackModel`, `ClosedCostalkDuality`, and
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`. The composition
  module is public because its predicate is also in this statement. The Mathlib
  Noetherian, finite-presentation, separated, quasi-compact and immersion modules
  supply the recorded geometric proof-dependency declarations. The upstream
  `Derived.BoundaryDuality` contains the fixed-module costalk specializations.

Edge cases checked before writing:

- Empty Y, W or Z are included: no Nonempty or positive-dimension assumption.
- Zero complexes are included: the recorded boundedness and Tor intervals may be
  chosen around zero even when all cohomology vanishes.
- n=1 is included; n=0 is excluded exactly by hn, as in the node.
- No smoothness, regularity, properness, or field-valued coefficients are assumed.
  Ramified extensions and nonreduced coefficient quotients retain finite Tor tests
  against every degree-zero module sheaf.
- Identity closed immersions and the empty closed subscheme are retained.
- There is no quasi-compact-immersion hypothesis on w: this is a conclusion of
  Noetherianity of Y in the proof plan. Universe u is shared by schemes and the
  coefficient extension, with only the recorded canonical lift to u+1 for sheaves.

Searches made:

- `msearch.py ... leanfinder` with query "Finite Tor constructible etale sheaves
  preserved by closed restriction and exceptional restriction with natural costalk
  duality and dualizing composition": eight hits, including
  `Scheme.smallEtaleTopology`, `Scheme.etaleTopology`, and unrelated scheme limit,
  compactness and condensed sheaf constructions; none states this node.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Etale.HasBoundaryDuality, AlgebraicGeometry.Etale.verdierDual`:
  zero hits; service reported unknown identifier HasBoundaryDuality.
- `msearch.py ... grep 'costalk|dualizingComplex|constructibleFiniteTor'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-weil-boundary-finite-tor-domains|HasBoundaryDuality|boundaryFiniteTorDomains`:
  only the upstream `Derived.BoundaryDuality` related declaration.
  Read that whole interface: HasBoundaryDuality omits the domains, canonical Gδ
  composite, and counit-compatible two-site composition, so it is not this statement.
  Its partial results are imported for reuse. The item id has no existing declaration.
- The dependency sources were opened by their recorded module and declaration,
  including the current comparison, constructibility, Tor, pairing and composition
  signatures. No dependency module repair is needed. The returned-delivery repair below adds an
  existing-declaration definition node for the canonical composition constructions.

No statement correction or STATEMENT-DISPUTED issue was found. The original node is
changed only in `lean` and by adding the new definition node to `stmt_deps`. The sole postponed theorem's docstring contains all seven
DAG proof steps and names their dependencies. Validation uses scompile.py only.

## Second reading by Q54

This is the worker's own second pass, not an independent agent review; the dispatcher
brief reserves independent review to the maintainer and forbids starting other agents.
With the node and file open, I checked the global finite-field, prime, extension and
positive-level binders; checked that geometric finiteness of each immersed piece is
concluded through existential proof witnesses; expanded both domain predicates and
traced P=s DT L and U=GL through the composite's endpoints; and opened the canonical
composition predicate and both dualizing-specialization definitions. This pass added
explicit existence clauses for both dualizing isomorphisms in addition to the canonical
composition normalization. It retained the ambient natural alpha without an evaluation
normalization, used the evaluation-defined delta rather than a chosen isomorphism,
and kept the specified comparison-transported pro-etale functor. A syntax issue in
the added coefficient units was fixed by opening `CategoryTheory.MonoidalCategory`.
No mathematical statement change or dependency replacement was made. The returned-delivery
repair below adds the missing definition attachment to the statement dependency graph.


## Repair of returned delivery e1e279c9a230

H2 is repaired by adding `def-weil-boundary-composition-mate`, a definition node with
`existing: true`, and adding its id to this item's `stmt_deps`. Its Lean record re-exports
all ten existing declarations requested by the maintainer from
`Sheaf.Paper.BoundaryDualizingComposition`. The theorem node
`lem-weil-boundary-dualizing-composition` stays in `proof_deps`; it is not added to
`stmt_deps`. No construction is inlined, copied, or restated in a new Lean module.

I compared the retained sandbox node with current main before editing: only `lean`
differed. Its Lean file is the returned delivery retained by the dispatcher. The repair
rebases the item node on current main, preserves its mathematical statement, proof,
proof dependencies and existing statement dependencies, and adds the definition id.
The delivery wrapper will build the repaired commit on the then-current main branch.

The advisory is addressed by naming `Etale.boundaryDualizingEtaleIso` and
`Etale.boundaryDualizingProIso` explicitly in the closed-pair predicate's docstring
and recording their defining constructions in the new definition node. The previously
reviewed two existence projections and the full canonical compatibility clause remain
in the predicate. Thus the canonical maps and their normalization stay specified by
`BoundaryCompositionCompatibility`, and the review's accepted mathematical statement
is preserved. The added dependency makes these constructions statement dependencies
instead of relying on a theorem's proof-dependency attachment.

Second pass on the repair: opened every attached declaration's full signature and body.
`boundaryCompositionIso` is the `conjugateIsoEquiv` of the actual restricted adjunctions;
`boundaryOriginIso` is the image of the comparison unit; the pro-etale composite is
exactly its prescribed four-step paste. `boundaryCoefficientPlus` is the real
constant complex, and the two kappa maps and lambda are their actual unit
specializations. The compatibility predicate is only defined by the pasted-counit
and naturality equations here; its truth remains the separate theorem. Checked that
the new node's own `stmt_deps` are exactly the ids cited by its definition text,
that it has no proof or theorem attachment, and that the main item cites it.

## New nodes

`def-weil-boundary-composition-mate` records the canonical bounded-below composition
mate, its restricted ambient adjunctions, comparison-origin transport, degree-zero
coefficient object, etale and pro-etale dualizing specializations, and the predicate
expressing the pasted-counit normalization and comparison-origin naturality. Its
source is the current blueprint's boundary-duality-discharge proof, with the existing
construction in `BoundaryDualizingComposition` specifying the canonical maps.
The definition's scope is exactly the signatures already present: finite commutative
coefficients, compactifiable f, g and their composite, quasi-compact composite and
quasi-compact middle and target schemes. Its `lean.existing` record attaches:

- `AlgebraicGeometry.Etale.boundaryUpperShriekPlus`;
- `AlgebraicGeometry.Etale.boundaryAdjunctionPlus`;
- `AlgebraicGeometry.Etale.boundaryCompositionIso`;
- `AlgebraicGeometry.Etale.boundaryOriginIso`;
- `AlgebraicGeometry.Etale.boundaryProCompositionIsoApp`;
- `AlgebraicGeometry.Etale.boundaryCoefficientPlus`;
- `AlgebraicGeometry.Etale.boundaryDualizingEtaleIso`;
- `AlgebraicGeometry.Etale.boundaryDualizingProIso`;
- `AlgebraicGeometry.Etale.boundaryDualizingComparisonIso`;
- `AlgebraicGeometry.Etale.BoundaryCompositionCompatibility`.

The primary signature is copied verbatim from `noncomputable def boundaryCompositionIso`
up to its `:=`; all ten declarations are checked by the delivery wrapper. There is no
new Lean module and no additional postponed theorem.

Searches for this definition node, also recorded in its `mathlib_searches`:

- LeanSearch: "Canonical composition mate for exceptional inverse image and dualizing
  complexes on etale and proetale sites" returned eight generic pullback-composition
  and mate-calculus hits, including `SheafOfModules.pullbackComp`,
  `CategoryTheory.mateEquiv_square` and `CategoryTheory.mateEquiv_vcomp`.
  None defines these boundary comparisons and dualizing specializations.
- Loogle: `conjugateIsoEquiv` returned zero hits and reported an unknown identifier.
- Mathlib grep: `boundaryCompositionIso|boundaryDualizingEtaleIso|boundaryDualizingProIso|
  BoundaryCompositionCompatibility` returned zero hits. Project searches in the upstream
  and Sheaf sources locate the existing declarations in `BoundaryDualizingComposition`.
- DAG grep for these canonical names found only
  `lem-weil-boundary-dualizing-composition`, a theorem node, before this addition.
  `tools/blueprint_refs.py search "boundary composition"` returned zero matches.
  Thus this is an existing-declaration definition attachment, not a duplicate of a
  definition node or a new construction. `blueprint.from` is the reported ancestor
  `cor-weil-boundary-duality-discharge`, with `via` starting with this item.

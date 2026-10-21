## Worker report

The module `Sheaf.Paper.ConstructibleNormedGeometricFibres` states all clauses of
`lem-sfb-constructible-normed-geometric-fibres`. All theorem proofs are `sorry`.
The definitions have actual data. No mathematical statement was changed.
NH's previous merged delivery was its stage-1 split, with no Lean binding; this
is its stage-2 statement, not a repeat of that split.

Hypothesis and conclusion correspondence:

- A normed field with totally disconnected metric topology is `F : Type u`,
  `[NormedField F]`, `[TotallyDisconnectedSpace F]`. The metric topology is the
  one supplied by `NormedField`. There is no completeness assumption.
- The all-continuous condensed ring is `(normContinuousRing F).X`, using the
  already recorded `Profinite.continuousMapRingObjOfUniverse`, with its recorded
  multiplication. Coefficients on Z are `condensedRingObj ... Z`, precisely p_Z^*.
- Modules are Mathlib `CategoryTheory.Mod` over these internal rings, not
  ordinary constant-ring sheaves. The ambient categories are `DerivedCategory`.
- A geometric point is the explicit `κ : Type u`, `[Field κ]`, `[IsAlgClosed κ]`,
  `x : Spec (.of κ) ⟶ Z`, following the recorded inline geometric-point encoding.
- `normedModuleInverseImage` uses the actual abelian inverse image and restriction
  along the inverse canonical coefficient isomorphism. Its real natural isomorphism
  `normedModuleInverseImageIso` identifies it with the recorded
  `CondensedRing.upperStar`, via `Mod.extendScalarsIsoComapInv`.
- `normedPointSections` is evaluation of the underlying sheaf at the terminal
  pro-etale object. `normedPointScalar` sends a to the constant function with
  value a, then applies the inverse of the canonical coefficient realization.
  Its named ring-map theorem supplies the structure proof separately.
  `normedGeometricFibre` composes the preceding constructions, internal-to-ordinary
  module conversion, and restriction along ULift's canonical ring isomorphism.
  Thus it is exactly Gamma(Spec κ, x^* M) with its constant-section F-action.
- `normedGeometricFibre_exact` asserts additivity and preservation of finite limits
  and finite colimits on ALL modules. The three component theorems expose these
  assertions as instances for the subsequent functor constructions.
- `normedGeometricFibre_symmetricMonoidal` states a braided strong monoidal
  structure after the canonical equivalence of F-vector spaces with vector spaces
  over ULift F, and identifies the fibre of the regular coefficient module with
  ULift F as an F-module. Mathlib's standard module tensor requires the ring and
  module universes to match; this ring-isomorphism transport expresses the same
  symmetric monoidality without restricting the universe of sheaf sections.
- `normedDerivedGeometricFibre` is `mapDerivedCategory` of the exact fibre: termwise
  application followed by localization, for unbounded complexes.
  `normedDerivedGeometricFibre_tExact` states t-exactness for both standard
  t-structures. The ambient vector-space derived-category instance is explicit
  (`HasDerivedCategory.{u+2} (ModuleCat.{u+1} F)`); the standard localization exists
  in this universe. This parameter selects the ambient model of D, not a new
  finiteness or size restriction on the mathematical objects.
- Noetherian Z is `[CompactSpace Z] [IsLocallyNoetherian Z]`.
  `normedGeometricFibre_finiteDimensional` uses the recorded
  `Scheme.FiniteLocallyClosedStratification`, requires constructible strata,
  and places `HasFiniteConstantLocalModel` on every stratum restriction.
  Its conclusion is `FiniteDimensional F` of the actual fibre.
- `normedGeometricFibre_reflectsIso` states sheaf-level detection, and
  `normedDerivedGeometricFibre_reflectsIso` states the requested joint detection
  on morphisms with `constantModelBoundedConstructible` source and target.
  On Noetherian schemes the latter recorded predicate uses a global finite
  constructible stratification (Noetherian schemes are qcqs). No assertion of
  unrestricted conservativity or constructibility of the cone is made.
- A continuous field inclusion is `i : F →+* F'` with `hi : Continuous i`.
  A unital homomorphism of fields is automatically injective; no independent
  algebra structure, completeness, condensed flatness, or finite-extension
  hypothesis is added. `normContinuousCoefficientMap` is postcomposition by i,
  pulled back along p_Z.
- Restriction is the actual exact `Mod.comap` of that coefficient map.
  `normedFibreRestrictionUnderlying_eq` identifies the underlying abelian groups.
  `normedFibreRestriction_existsUnique` fixes the natural isomorphism by requiring
  its underlying map to be the identity transported through that equality.
  This specification determines the isomorphism uniquely. Its chosen value is
  `normedFibreRestrictionIso`; `normedDerivedFibreRestriction` gives the termwise
  unbounded derived comparison.
- `normedFibreScalarComparison` is the adjunct, for the ordinary vector-space
  scalar adjunction, of fibre applied to the internal extension/restriction
  unit followed by the specified restriction isomorphism. Consequently it is
  precisely the balanced map a tensor m maps to a tensor m. Its naturality is
  named, and `normedFibreScalarTransformation` contains those actual components.
  `normedFibreScalarComparison_unit` explicitly states the insertion-of-one
  equation. The named vector scalar-extension assertions expose exactness
  of abstract field tensor in the ambient module universe.
- `normedFibreScalarDerivedSource` applies the exact composite of fibre and
  abstract vector scalar extension termwise, so computes F' tensor^L_F Phi(K).
  `normedFibreScalarDerivedTarget` is the fibre after the total LEFT derived
  functor of internal extension of scalars. It does not assume that internal
  extension is exact. `NormedFibreScalarDerivedNormalized` requires the square
  with its left-derived counit on every K-flat representative to equal the
  homotopy-category image of the specified ordinary balanced transformation.
  `normedFibreScalarDerived_existsUnique` states the normalized natural DERIVED
  isomorphism; `normedFibreScalarDerivedIso` selects this uniquely specified
  isomorphism. These are isomorphisms in the ordinary unbounded derived category,
  not merely per-degree vector-space isomorphisms. The representative equation
  retains the insertion-of-one normalization through the ordinary unit equation.

Dependency declarations used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: all-continuous ring construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module actions.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the public
  derived framework: ordinary `DerivedCategory` conventions.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: recorded total derived module
  pushpull conventions; the underived `CondensedRing.upperStar` remains the
  comparison for the concrete inverse-image formula.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `finiteConstantLocalModel_iff_exists_cover`, importing the existing
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, and
  `constantModelBoundedConstructible` from `CondensedConstantConstructibility`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`;
  Mathlib `CompactSpace`; recorded inline `IsAlgClosed` geometric points.
- `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing`,
  `normContinuousCoefficientMap`, `normContinuousExtension`.
- `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`:
  `condensedFieldContinuousMapIso`, its unique canonical continuous realization.
- `Sheaf.Paper.CondensedQbarCoefficientConstruction`:
  `CondensedQbarGeometricEvaluation.ordinary`, the public GENERIC internal-module
  conversion (not its Qbar-specific fibre).
- Mathlib `ModuleCat.extendRestrictScalarsAdj`, `restrictScalars`, `extendScalars`;
  upstream `Mod.extendRestrictAdjunction`, `Mod.extendScalarsIsoComapInv`,
  `Functor.leftDerivedFunctor`, its counit, and exact `mapDerivedCategory`.
  All already stated proof-dependency modules are also imported with plain imports.

Edge cases checked: empty Z (vacuous points, sheaf and derived detection on the
zero category); zero modules and rank-zero local models; strata with empty
realizations; arbitrary characteristic of both residue and coefficient fields;
noncomplete totally disconnected normed fields; identity inclusions and arbitrary
continuous field inclusions; unbounded complexes in the scalar comparison; bounded
constructible source and target without a constructible-cone assumption. The
standard ring-isomorphism lift and explicit ambient D parameters do not force
small-site object and morphism universes equal.

Searches:

- msearch leanfinder: exact geometric fibres for all-continuous totally disconnected
  normed fields, finite-dimensional constructible fibres, scalar extension;
  eight hits (condensed solid modules, exact colimits, etale forgetful functor),
  none giving this statement.
- msearch loogle: `ModuleCat.restrictScalars, Functor.mapDerivedCategory, Mod.comap`;
  no packaged match; the latter derived name was unknown to its index.
- msearch grep: `geometric.*(Fibre|Fiber)|normed.*(Fibre|Fiber)`; ordinary etale
  geometric fibres and unrelated vector-bundle hits, no normed pro-etale interface.
- rg in live Sheaf and WeilConjectures: the item id has no declaration. Broader
  normed/geometric-fibre searches find the Qbar- and adic-specific fibres; these
  impose coefficient restrictions and do not state this node. The generic existing
  point evaluation in CondensedFieldEvaluationFunctors is private. The delivery
  therefore uses public sections and public generic module conversion, with the
  scalar action explicitly fixed by the already canonical coefficient realization.
- Read the coefficient and stratification definitions and the full signatures and
  docstrings of the recorded dependencies; read HRS Section 3, Example 3.1 and
  Lemma 4.1 from the supplied local PDF. No new independent notion/node is needed.

No STATEMENT-DISPUTED flag. No dependency replacement or statement correction.
Added stmt_deps only for the three already landed interfaces used for the normed
ring/scalar map, canonical realization, and public ordinary-module conversion.

Validation: the complete delivered module compiled cleanly through scompile.py in
sandbox mode (20.3 s) and library mode (18.9 s), below the prescribed 60 s limit.
No warnings or errors remained. The inverse-image formula was factored through a
generic canonical helper to avoid expensive concrete kernel conversions; no
limits were raised. Explicit additivity arguments in the representative square
keep the section/coefficient universes unchanged.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

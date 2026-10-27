## Worker report

The module `Sheaf.Paper.FiniteRingRelativeScalarComparison` states
`AlgebraicGeometry.ProEtale.finiteRingRelativeScalarComparison`, with its whole proof
postponed as `sorry`. Its only helper, `finiteRingScalarDirectImageMate`, is the actual
`mateEquiv` of the published pro-etale scalar/pullback comparison and geometric derived
adjunctions. Its data is a concrete expression, with no postponed data or arbitrary map.

Hypotheses and clauses, in the order of the node:

- The field is `(k : Type u) [Field k]`; positive characteristic is `[CharP k p]`
  together with `_hp : p.Prime`. The prime away from the characteristic is
  `_hl : l.Prime` and `_hlp : l ≠ p`. For a field, a positive characteristic is prime,
  so writing this as primality imposes no further restriction.
- `X Y : Over (Spec (.of k))` and `f : X ⟶ Y` express k-schemes and a k-morphism.
  Each structure arrow has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`,
  exactly separated finite type. No hypothesis on f beyond being over k is added.
- `A B : Type (u + 1)`, `CommRing`, `Finite`, and `a : A →+* B` express the finite
  commutative coefficient rings and their unital homomorphism. `_hA` and `_hB`
  assert that a positive power of l kills 1, equivalently the entire ring.
  These constant coefficient sheaves use the discrete topology; no topological
  ring structure or continuity assumption is necessary for this presentation.
- `K : DerivedCategory.Bounded (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat A))`
  expresses boundedness in the ordinary uncompleted category of constant-ring modules.
  `_hK` applies `Scheme.IsConstructibleProEtaleFixedModuleSheaf X.left A`
  to every cohomology sheaf. This is the published intrinsic fixed-module predicate:
  a positive finite constructible locally closed stratification, local constancy on
  each stratum, and finite geometric module stalks. It imposes no etale origin and
  no common stratification for different cohomology degrees. For finite rings on
  the standing Noetherian schemes this expresses the finite constant-model notion
  in the node; finite modules over finite rings are finitely presented.
  `_hTor` uses `DerivedCategory.finiteTorAmplitude` on this very sheaf category:
  derived tensor with every degree-zero module sheaf is tested, with no perfectness
  or projective-dimension substitute.
- The existential `J : DerivedCategory.Bounded ...` and its cohomology-constructibility
  and `finiteTorAmplitude` conjuncts give `J ∈ D^b_ctf(X_et,A)`. The next conjunct is
  `Nonempty (comparisonUpperStar.mapDerivedCategory.obj J.obj ≅ K.obj)`, the claimed
  comparison pullback isomorphism.
- The next two existential integer bounds are `J_B.IsGE n` and `Q.IsGE n`, with
  `J_B = (pbcFixedScalarExtension X.left.smallEtaleTopology a).obj J.obj` and
  `Q = (pbcFixedScalarExtension Y.left.smallEtaleTopology a).obj (R ... J.obj)`.
  They are conclusions, never assumed. Scalar extension everywhere is the existing
  adjoint fixed by restriction of scalars, not an arbitrary tensor functor.
- The two `IsIso` conjuncts are precisely the B-linear etale scalar mate at J and
  pro-etale scalar mate at K. The etale mate is written as `mateEquiv` of the two etale geometric adjunctions
  over `scalarPullbackEtaleIso`, owned by the cited scalar-mate transport node.
  This is definitionally equal to the previously written `Etale.scalarMate`. The pro-etale helper uses the very same mate expression as that node.
- The first equality is the restriction/projection normalization, written with the
  published `derivedRestrictScalars`, `scalarRestrictionDirectImageMap`, `scalarTensorIso`,
  `rightDerivedLowerStarProjectionMap`, and `scalarCoefficientPullbackIso`. Both endpoints
  are compared using those specified identifications, including the target tensor
  identification after direct image. It is an equality of morphisms, not an existential
  isomorphism of objects.
- The last equality is the displayed transport identity, in Lean's left-to-right
  composition order. Delta is `pbcComparisonReduction`, beta is
  `directImageComparisonAmbient`, and the inverse beta_A is `eA.inv`.
  `eA.hom = (directImageComparisonAmbient A f.left).app J.obj` fixes eA uniquely to the
  canonical beta_A and asserts its invertibility. Packaging this inverse as a uniquely
  specified existential isomorphism avoids imposing qcqs typeclasses just to elaborate
  a chosen inverse. These conditions are already guaranteed by the setting and the
  cited comparison theorem. There is no arbitrary comparison choice or extra input.
- No flatness, finite projective dimension, or absolute etale cohomological dimension
  condition occurs anywhere in the binders.

Dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` documents the existing Over/finite-type
  setting; the binders render its standing assumptions directly.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; only its finite
  discrete constant-ring specialization is needed here.
- `sk-def-sfb-constructible` retains its current sheaf-dag record unchanged, including
  every landed general condensed-coefficient declaration. Its current recorded module
  `Sheaf.Paper.FiniteConstantRingedLocalModel` is publicly imported; it reexports
  `Sheaf.Paper.CondensedConstantConstructibility` and its general finite constant-model,
  bounded constructible, and finite-Tor definitions. The item uses their finite-ring
  specialization via the separately owned fixed-module predicate below.
- `def-weil-proetale-constructible-sheaf`, module
  `Sheaf.Paper.ProEtaleFixedModuleConstructible`, owns
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`. Its complete
  signature and docstring, as well as the local-constancy definition it uses, were read.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` reexports the generic
  ringed-site derived scalar construction. `pbcFixedScalarExtension` of
  `Sheaf.Paper.WitnessCompatibility`, used by the recorded scalar-mate node, is its
  already published constant-ring presentation. `Etale.scalarExtension` is an abbreviation.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`;
  its left adjoint is `comparisonUpperStar` and its exact derived functor is
  `comparisonUpperStar.mapDerivedCategory`.
- `Sheaf.Paper.EtaleProEtaleScalarMate`: `scalarPullbackProEtaleIso`,
  `scalarPullbackEtaleIso`, `directImageComparisonAmbient`, and
  `etaleProEtale_scalar_mate`. These provide exactly the maps in the last clause.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `DerivedCategoryModule`,
  `DerivedCategory`, `DerivedCategory.Bounded`, and `DerivedCategory.homologyFunctor`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` documents the general
  module category. The constant-ring presentation is the existing `Sheaf ... (ModuleCat A)`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` supplies the general
  canonical comparison; its fixed-ring specializations are the scalar pullback isos above.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` supplies the constant-ring
  operations; the fixed-ring geometric adjunctions are the already published
  `ProEtale.derivedUpperStarLowerStarAdjunction` and their etale counterpart.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`.
- `Sheaf.Paper.PurEtaleScalarMateProjection` is a plain proof import for
  `scalarMate_restrict_eq_projection`. The signature uses the definitionally equal
  explicit etale mate of the cited `scalarPullbackEtaleIso`.
- `def-kun-scalar-restriction-comparison-maps`, module
  `Sheaf.Paper.EtaleUnboundedRestrictionComparison`, owns
  `Etale.scalarRestrictionDirectImageMap` (and `scalarRestrictionPullbackIso`).
- `def-pur-scalar-pullback-representative-data`, module
  `Sheaf.Paper.ScalarPullbackRepresentativeData`, owns
  `Etale.scalarCoefficientPullbackIso`.
- `def-weil-pbc-etale-constructible-sheaf`, module
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, owns
  `Scheme.IsConstructibleEtaleModuleSheaf` in the J conclusion.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.finiteTorAmplitude` and `torAmplitudeIn`, both with all module tests.

Every recorded statement-dependency module is publicly imported. Stated proof-dependency
modules are imported with plain imports unless already public. The complete nine-step
proof from the node is in the theorem docstring, with its dependency identifiers.

Edge cases checked: A and B may be the zero ring (no Nontrivial binder); zero complexes
and the empty scheme are allowed; the intrinsic predicate requires a positive number
of strata, but strata may be empty, so a one-stratum partition still admits the empty scheme;
nonflat finite quotient maps are allowed; there is no projective-dimension binder;
unbounded outputs of scalar extension are not silently assumed bounded below; no
finite absolute cohomological dimension of k is used. The coefficient/module universe
is u+1 for Scheme.{u}, the existing fixed-coefficient convention on both actual small
sites, with no equation forcing site object and morphism universes equal.

Searches performed:

- msearch leanfinder: `Derived extension of scalars for finite torsion rings commutes
  with direct image of constructible finite Tor amplitude etale sheaves`. Eight hits
  about algebraic etaleness and base change, no derived sheaf statement.
- msearch loogle: `AlgebraicGeometry.Etale.scalarMate,
  AlgebraicGeometry.ProEtale.etaleProEtale_scalar_mate`. Zero hits, unknown project name.
- msearch grep: `scalarMate|finiteRingRelativeScalar`, CategoryTheory. Zero hits.
- msearch leansearch: `Derived scalar extension commutes with direct image of finite
  Tor amplitude constructible sheaves for finite rings`. Eight module scalar-extension
  hits, no derived direct-image statement.
- rg of WeilConjectures and Sheaf for finite scalar/relative scalar comparisons found
  finite compact-support and other coefficient comparisons, and the two scalar-mate
  modules used here, but no theorem carrying this node's full clauses.
- rg of WeilConjectures for the item identifier found no attachment.
- A focused search for scalar-mate definitions in ProEtale and Sheaf/Paper found no
  fixed-ring pro-etale natural transformation already naming the mate expression.
  The helper merely names the existing mate expression used verbatim by the dependency.

The returns identified missing statement-dependency ownership and then an invalid
replacement of a general coefficient record by a special case. The repair below cites
the existing owner of the fixed-module predicate and withdraws that replacement.
No new node or dependency record is delivered.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review. The clause-by-clause audit above
is the author's audit, not an independent reading.

## Returned delivery repaired

The latest immutable returned head was `f98826f90c22`, following `87c6ab5ddaf6`.
The item and dependency records were compared with current sheaf-dag. The H2 changes
already accepted by the maintainer are retained: the etale mate is explicit `mateEquiv`
over `scalarPullbackEtaleIso`, and all three normalization/etale-constructibility owners
are cited in the TeX and stmt_deps and publicly imported.

H13: The replacement attachment of `sk-def-sfb-constructible` is withdrawn: its node
file is absent from this delivery, so its complete current sheaf-dag record remains
byte-identical, with every general declaration preserved. The Lean `_hK` binder now
uses exactly `Scheme.IsConstructibleProEtaleFixedModuleSheaf X.left A`. The module
`Sheaf.Paper.ProEtaleFixedModuleConstructible` is publicly imported and its existing
owner `def-weil-proetale-constructible-sheaf` is added to stmt_deps and cited at pro-etale
constructibility in the TeX. The old general dependency remains in stmt_deps; its current
recorded module is publicly imported. No shared dependency's statement, stmt_deps, or
lean record is changed. The helper, every other binder, all conclusions, the proof,
and proof_deps are unchanged.

## Statement corrected

This is the requested section 1(C) citation-only correction. The current sheaf-dag
statement is stored verbatim in `statement_change.old_statement`, and its statement
dependencies are stored in `old_stmt_deps`. The mathematical content remains the
same finite-ring scalar/direct-image comparison. The TeX explicitly cites:

- `def-weil-proetale-constructible-sheaf` for intrinsic pro-etale constructibility;
- `def-weil-pbc-etale-constructible-sheaf` for etale constructibility;
- `def-kun-scalar-restriction-comparison-maps` for the scalar-restriction/direct-image map;
- `def-pur-scalar-pullback-representative-data` for coefficient pullback.

The latest blueprint finite-rings paragraph and preceding canonical-mate and
restriction-of-scalars paragraph were reread. No field, coefficient, boundedness,
canonical-map, or normalization clause changes. The proof and proof_deps are unchanged.

The reverse-dependency audit was repeated by searching all dag/nodes for the item id
and parsing every stmt_deps and proof_deps. It again found exactly one citer, whose
statement and use were reread:

- `det-prop-scalar-six-direct-image`: holds true. Its finite-ring case uses the same
  B-linear counit-mate isomorphism on bounded constructible finite-Tor complexes,
  including nonflat maps and arbitrary standing fields. Intrinsic fixed-module
  constructibility is the same finite-coefficient notion in this setting; adding
  its owner and the normalization-map owners changes none of that use. The citer
  is not edited.

The fixed-module definition includes zero rings and the empty scheme, uses the
existing canonical module inverse image on each stratum, and has coefficients in
u+1 over Scheme.{u}. The positive stratum count permits empty strata. All earlier
edge cases (including f=id and nonflat quotient coefficients) and the exact
canonical-mate transport equality are retained. No new theorem is asserted.

## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality` as
`AlgebraicGeometry.Etale.ordinaryEtaleCup_functoriality`. Its proof is `sorry`.
The original natural-language statement is unchanged. Its statement dependencies gain
`def-wf-ordinary-etale-cup`, which supplies the previously missing canonical operation
and its integral coefficient presentation, rather than assuming an arbitrary pairing
on cohomology.

Hypothesis and conclusion correspondence:

- The arbitrary scheme morphism is `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  There is no finiteness, properness, flatness, connectedness or field hypothesis.
- `F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}` and the three primed
  sheaves on `Y` are precisely the six abelian sheaves of the node. The common
  coefficient size is the size already used by the recorded pullback declaration.
- `ordinaryEtaleTensor X F G` is the ordinary sheaf tensor over the integers:
  equip each abelian sheaf with its unique integral action, use the existing
  ModuleCat-valued sheaf tensor (sheafification of sectionwise tensor), and forget.
  Thus `e` and `e'` are precisely the two coefficient pairings in the statement.
- `a`, `b`, `c` have sources `(upperStar AddCommGrpCat f).obj F`, and similarly
  for `G,H`. This is the dependency's actual inverse-image functor, not an
  unspecified exact functor or the pullback of scheme O-modules.
- `he` is `upperStar.map e ≫ c = ordinaryEtaleTensorPullback f F G ≫
  ordinaryEtaleTensorMap Y a b ≫ e'`. The first comparison is the canonical
  inverse-image tensorator. It is built from the existing module inverse-image
  tensorator and the canonical Kan-extension/sheafification scalar comparisons;
  its direction is from inverse image of tensor to tensor of inverse images.
- `p q : ℕ` includes exactly all nonnegative degrees. `x : Sheaf.H F p` and
  `y : Sheaf.H G q` are ordinary small-etale classes, using the Ext presentation
  of the recorded `Sheaf.H`/`Etale.cohomologyMap` API.
- Each `T_a` is written out as `Sheaf.H.map a p (cohomologyMap f F p x)`.
  The same expression with `b` renders `T_b`. The left side is `H.map c (p+q)`
  of `cohomologyMap f H (p+q)` applied to the cup; thus it is exactly `T_c`.
- Each cup is `ordinaryEtaleCup` with the specified ordinary coefficient pairing.
  It tensors the two lifted derived unit classes, applies the canonical derived
  tensor-to-ordinary tensor augmentation, then the coefficient pairing, and
  returns through the canonical coefficient-forgetting cohomology comparison.
  By the derived constant-sheaf/global-sections adjunction this is the relative
  derived-global-sections cup of Stacks 0B6C and 0FPJ. In particular it does not
  replace derived tensor by ordinary tensor before taking derived classes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`; the small site is
  `Scheme.smallEtaleTopology` from `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` reexports the
  recorded site tensor and supplies the independent-site-universe interface.
  The constant-integer presentation uses the existing ModuleCat-valued sheaf
  monoidal tensor, not a new sheafification or a scheme O-module tensor.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.cohomology`, `Etale.rightDerivedGlobalSections`. The sheaf cohomology
  realization is Mathlib's `Sheaf.H`, as already required by the pullback node.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`; its definition is Ext transport through the exact
  inverse image followed by the canonical constant-integer comparison.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`,
  defined as `curriedTensor` for the existing derived monoidal structure.
- `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`:
  `RawModuleScalarComparison.forget`, its exactness instances and `pullbackIso`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`:
  `ordinaryFiniteConstant`, `ordinaryFiniteIntegralGenerator`, `ordinaryFiniteClass`.
  These constructions accept every commutative coefficient ring, including
  lifted integers; no finite-ring restriction or `N` hypothesis is used.
- `Sheaf.Paper.ModuleCupCanonicalHZeroIdentification`:
  `DerivedCategory.moduleCup_singleTensorIso`, the existing generic single/tensor
  comparison, reused rather than copied.
- `DerivedCategory.singleFunctorObjUnitIso` (upstream FlatModel), and the existing
  localization lax tensorator, supply the unit diagonal and tensor augmentation.
  The single-functor/localization natural isomorphisms are retained explicitly.

All recorded proof-dependency modules are imported non-publicly. The full eleven-step
DAG proof is included in the item's theorem docstring, retaining the normalized
adjunctions, the inverse Leray comparison, both transposes, augmentation naturality
and the degree-zero identification. The live source of
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` was read through
`scompile.py --source`, since it is absent from the older local source checkout.

Edge cases checked before drafting:

- Identity morphism and arbitrary coefficient maps: `he` becomes precisely the
  coefficient-pairing square under canonical unit/counit identifications. No
  assumption forces those maps to be identities or isomorphisms.
- Degree `(0,0)`: derived classes are maps out of the integral generator; the
  diagonal sends 1 to 1 tensor 1 and the augmentation gives ordinary tensor.
  The formula is the ordinary pairing of sections and its given coefficient square.
- Empty schemes and zero coefficients: all relevant ordinary cohomology groups
  vanish. The construction uses no chosen point and assumes no nonempty site.
- Disconnected schemes: the integral generator is the constant sheaf, not
  `Gamma(X,Z_X)` as coefficient ring; all comparisons work componentwise.
- Non-flat coefficients, for instance integral torsion: the derived tensor remains
  unbounded if necessary and its augmentation is the lax localization comparison.
  No assertion that this augmentation is invertible is made.
- The sign convention is the unsigned cocycle convention in Step 10 of the node.
  `ordinaryCupShiftIso` moves the right shift first, then the left. On degree-zero
  maps into the shifted factors this sends the two cycles to their tensor without
  the extra (-1)^(pq) introduced by moving the left shift first. This agrees with
  the normalization recorded in `def-wf-finite-coefficient-cup`.

Searches for an existing statement/notion:

- `msearch.py leanfinder`: “Pullback of ordinary etale cohomology commutes with cup
  products and compatible coefficient pairings”. Eight hits, mostly scheme
  pullback cocycles and group cohomology functoriality; no matching statement.
- `msearch.py loogle`: `cupProduct`. No hits; unknown identifier.
- `msearch.py grep`: `cupProduct|cup_product`. Zero Mathlib hits.
- `msearch.py leansearch`: “Cup products of abelian sheaf cohomology using integral
  module sheaves and derived tensor”. Eight hits, including `Sheaf.H`, ordinary
  sheaf definitions, and Cartesian tensor; none is this integral cup operation.
- `msearch.py grep`: `ordinaryEtaleCup|ordinaryEtaleTensor|integralClassLift` in
  `CategoryTheory/Sites`: zero hits.
- Direct `rg` over the upstream project and `lean/Sheaf` found upstream
  `Etale.cupProduct` for the derived tensor unit only. It does not permit arbitrary
  coefficient sheaves or coefficient pairings. Its generic tensor infrastructure
  is reused. The two finite-coefficient cup definitions are specializations and
  do not give this general integral pairing. Scheme O-module and supported
  pro-etale cup definitions have different sites/coefficient categories.
- Direct search for the item ID in the upstream project returned no hit.
- DAG text searches and `blueprint_refs.py search 'ordinary cup'` found the
  finite-field Poincare trace-cup node; its datum and coefficients differ. No
  existing node defines the general integral cup introduced here.

No statement dispute or source-based correction is needed.

## New nodes

`def-wf-ordinary-etale-cup` defines the canonical ordinary integral cup for arbitrary
abelian sheaves, and the canonical tensor and inverse-image comparisons it uses.
Its source is Stacks 0FPJ/0B6C, with the coefficient comparison of 03FD. Searches
are recorded in its `mathlib_searches` from the search-tool results, plus the
project/DAG search described above. Its module reuses the existing scalar-forgetting
functor, integral generator, ordinary class realization, derived tensor,
tensor/single comparison and localization structure. Every definition contains
real data. The only new postponed theorems are
`integralForget_isEquivalence` and `integralClass_bijective`; their statements
are included in the definition node and their docstrings give full proofs.
They determine the inverse functor up to the canonical counit isomorphism and
the inverse class comparison uniquely. No arbitrary morphism or mere Nonempty
witness replaces a canonical construction.

Validation: `scompile.py N5 lem-wf-etale-cup-functoriality` with both delivered
modules passed, compiling each separately in dependency order, including private
overlay, sandbox and actual-library module checks. There were no errors or warnings.

## Returned-delivery validation

On 2026-10-18 the required first dry run of the retained packet passed:
`OK (dry run): commit cf4ee79ee9 passes the preflight and compiles; nothing pushed`.
The private-overlay check initially reproduced the reported 60-second timeout;
the wrapper's confirmation against current server sources accepted that dry run.
The subsequent delivery attempt also timed out in server confirmation, with nothing
pushed, so the packet required a performance repair after all.

Profiling a scratch copy isolated repeated kernel checks in `integralClassLift`:
the generated equivalence proof and the definition each took about 15 seconds,
in addition to about 15 seconds for `ordinaryEtaleCup`. The lift now applies
`Function.surjInv` directly to the surjectivity component of the existing
`integralClass_bijective` theorem, instead of constructing an entire `Equiv` and
then applying its inverse. Injectivity in that same theorem uniquely determines
the chosen preimage, so this is the same canonical inverse class. No theorem or
definition signature, coefficient object, comparison or cup convention changed.
The scratch profiling options were removed and are absent from the delivery.

The self-check confirmed that both recorded signatures occur verbatim, both files
disable auto-bound implicits, and all lines are within 100 characters. The
hypothesis, conclusion and edge-case correspondence above continues to apply.

After this repair, `scompile.py` with both delivered modules passed the private
overlay, preliminary, sandbox and library checks, with no warnings or errors.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

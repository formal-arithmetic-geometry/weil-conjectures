## Worker report

This delivery defines the finite-coefficient trace–diagonal datum and all the
canonical constructions specified by def-pur-td-datum. The accepted stage-1 split
is unchanged. Its earlier unchanged-stage-1 refusal does not apply: standing
brief §0 explicitly makes a reviewed split without Lean the input to stage 2.

Module: `Sheaf.Paper.FiniteTraceDiagonalDatum`.
Main declaration: `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.Datum`.
The named `tensorFor`, `pullFor`, and `compactSupportFor` wrappers contain exactly
the existing native functor data, with transparent abbreviation reduction.
Comparison component endpoints are explicit, and the constructions retain their
ordinary transparency so Lean can check their canonical endpoint identifications.
All auxiliary declarations are listed in lean.declarations, carry the owning
blueprint identifier, and belong to the formulas of this same notion.

Hypotheses and clauses, one by one:

- The purity setting is `P : WeilConjectures.PurityFiniteSetting.{u}`. Its
  `P.Coefficient` is the recorded finite quotient A_(E,n), including the positive
  level, finite extension, and characteristic/ell conditions. `coefficientFinite`
  uses finiteness of that quotient; no higher coefficient stage is asserted.
- `X Y : Scheme.{u}` have `Over (Spec (.of P.field.k))`; the locally-of-finite-type
  and quasi-compact structure morphisms say exactly finite-type k-schemes.
  `f.IsOver` says f is a k-morphism. `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f` say separated finite type. `compactification` applies Nagata in
  this setting, using the noetherian and compact target consequences. All these
  hypotheses are explicit binders on Datum, so Lean cannot omit unused section
  assumptions from the public datum signature.
- `pullback f f`, `pullback.fst f f`, `pullback.snd f f`, and
  `pullback.diagonal f` are the existing fibre product, projections, and diagonal.
  In the Lean formulas the map is the existing
  `Etale.TraceDiagonalDatum.diagonal`, with section equations `diagonal_fst` and
  `diagonal_snd` from its upstream Basic module. This is exactly pullback.diagonal
  with the codomain explicitly written pullback f f; the upstream docstring warns
  that the diagonalObj synonym makes derived-functor kernel comparisons very slow.
  normalizedDiagonalProper reuses the existing properness instance for this map.
- `D P T` is the derived category of module-valued sheaves on the ACTUAL small
  pro-etale site `Scheme.ProEt.topology T`, with `ModuleCat.{u+1} P.Coefficient`.
  It is not a coefficient-small replacement of the site. `Ctf P T` abbreviates
  the existing `ProEtale.DerivedCategoryFiniteTor`, whose full-subcategory objects
  are bounded constructible complexes with a global finite Tor interval.
- `tensor` is exactly `ProEtale.derivedTensor`. `pull` is the existing derived
  `upperStar`. `shriek` is the existing compactification-based derived exceptional
  direct image; `push` is its published chosen-compactification abbreviation.
  `shriek₂` uses the base-changed compactification needed by self-square exchange.
- `L : Ctf P X` is the specified finite-Tor constructible object. `Invertible P L`
  says `exists M : D P X, Nonempty (L tensor M ≅ one P X)`, exactly the meaning
  explicitly given in the node. The inverse is not required to be chosen as
  additional datum or assigned an extra Tor condition. `Datum f L hL` keeps the
  tensor-invertibility hypothesis while having precisely two fields.
- `Datum.trace` is `Rf! L → one P Y`. `Datum.diagonalClass` is
  `RDelta! (one P X) → pull p2 L`. Both are actual ambient derived morphisms.
- `twisted f L` is `pull P f ⋙ (tensor P X).flip.obj L.obj`, so its map is precisely
  `Lf*(a) tensor 1_L`. `functor f L` restricts this existing functor to Ctf via
  `ObjectProperty.lift`. `twisted_preserves` names the typing clause explicitly
  proved in the node's natural-language proof by pullback and tensor closure.
  `compactFunctor f` similarly restricts `shriek`; `shriek_preserves` names the
  other typing clause explicitly stated in that proof. Neither is extra data.
- `signedSymmetry` uses the published `DerivedCategory.braidedCategory'`
  wrapper for `DerivedMonoidal.braidedCategory'`, and
  `BraidedCategory.curriedBraidingNatIso`, descending the Koszul braiding through
  the canonical derived localization. There is no arbitrary Nonempty iso here.
  `one` is the native tensor unit; `unitLeft` and `unitRight` are its localized
  multiplication constraints. They are the same monoidal structure as tensor.
- `projection` inverts the EXISTING `projectionMapOfCompactification`, using
  `hasProjectionFormulaOfCompactification_of_constructibleFiniteTor` at the
  specified finite-Tor arguments. `Datum.counitMap` composes signed symmetry,
  inverse projection, signed symmetry, `1_K tensor trace`, and multiplication.
  This is exactly the displayed epsilon, including its canonical comparison.
- `originChange` descends the published compactification comparison uniquely by
  full faithfulness of the canonical etale-origin equivalence. `compactSection`
  composes those comparisons, `originCompositionAmbient`, equality transport of
  the section equation, and `originCompactSupportId`. The latter is normalized
  by the trivial compactification. These are actual constructions, not choices
  from an existence theorem or a separately supplied comparison map.
- `projectionCore` and `selfExchangeCore` invert the published canonical maps
  at the finite-Tor inputs, separately from their composites, keeping instance
  proof checking small. `diagonalPullbackCore`, `contractionCore`, and
  `exchangeCore` construct the
  same canonical maps over an abstract finite ring, to keep elaboration from
  unfolding the concrete Padic quotient. Their hypotheses are discharged by the
  existing typing clauses when specialized to P.Coefficient; no hypotheses or
  maps are supplied by the datum. These helpers use the published native
  functors and category directly.
- `diagonalPullback` uses inverse `leftDerivedUpperStarComp`, the p1 section
  equality, and `leftDerivedUpperStarId`. `diagonalContraction` first applies
  signed symmetry and the projection map for Delta, then unit multiplication,
  that pullback comparison, and `compactSection` for Delta,p2. Its inverse is
  the FIRST isomorphism in eta. `diagonal_inputs` names precisely the unit and
  p1-pullback finite-Tor conditions used in that displayed formula; its docstring
  explains the finite constant unit and pullback preservation proofs.
- `diagonalExchange` composes inverse projection for p2 and inverse of the
  EXISTING `rightDerivedLowerShriekOfCompactificationBaseChangeMap` for
  `IsPullback.of_hasPullback f f`, tensored with `1_L`. Invertibility uses the
  native etale-origin compact-support base-change theorem at A.property.
  This is the LAST isomorphism in eta, with the direction in the node.
- `Datum.unitMap` is `(diagonalContraction f A).inv`, followed by `shriek₂.map`
  of `1_(p1*A) tensor diagonalClass`, followed by `diagonalExchange.hom`.
- `Datum.counit_naturality` and `unit_naturality` state the naturality clauses
  explicitly asserted in the node; the complete proof explanations compose
  naturality squares of the named canonical transformations. `Datum.counit`
  and `unit` package those component maps in the full Ctf subcategories.
- `Datum.leftTriangle` is the natural transformation Rf! eta then epsilon Rf!;
  `rightTriangle` is eta G then G epsilon. The associators/unitors merely identify
  parenthesizations. No triangular identity, adjunction, or relation between
  the datum's arrows is imposed. In particular zero arrows remain valid data.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  its coefficient ring, finite quotient construction and fixed-setting fields.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `snd`, `diagonal`, `diagonal_fst`, `diagonal_snd`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: recorded common-stage internal-Hom
  interface; its finite-coefficient inputs use the native `ProEtale.upperStar`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `ProEtale.derivedTensor` (the native curried monoidal derived tensor).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- Scheme morphism properties: Mathlib `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`; no private variants are introduced.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`; actual fixed-module realization uses
  `ProEtale.rightDerivedLowerShriekOfCompactification` from the published framework.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`; concrete
  canonical native maps are `projectionMapOfCompactification` and
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`:
  `Etale.isIso_finiteCompactProjection`; its native fixed-module realization is
  `ProEtale.hasProjectionFormulaOfCompactification_of_constructibleFiniteTor`.
- `Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin`:
  `ProEtale.constructible_localTor_iff_etaleOrigin`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal`:
  `Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`.
  Native Ctf objects supply their canonical `property.plusEtaleOrigin`.
- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`:
  `SheafOfModules.DerivedTensorConstraints.existsUnique_derived_tensor_constraints`;
  the actual fixed-module symmetry is the localized signed braiding described above.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`:
  `Scheme.proEtaleCoefficientInverseImageMap_comp`;
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity`:
  `Scheme.proEtaleDerivedPullback_identity`. The exact module-valued realizations
  are `ProEtale.leftDerivedUpperStarComp`, `Congr`, and `Id`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `ProEtale.originCompositionAmbient`, `originCompactSupportCongr`, and
  `originCompactSupportId`; all retain the canonical etale-origin normalization.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`:
  `ProEtale.isIso_csAuxiliaryExchange`; its native compactification realization is
  `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`.
- Proof dependencies: `Sheaf.Paper.PullbackTorAmplitude`,
  `WeilConjectures.sf_pullback_finiteTorConstructible`;
  `Sheaf.Paper.FiniteCoefficientTensorCtf`, `Scheme.finiteCoefficient_tensor_ctf`;
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution`,
  `ProEtale.derivedTensor_map_app_comp_map`;
  `...Derived.CompactifFiniteTor`,
  `ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`.

Edge cases checked before writing: f=id uses the canonical identity normalization,
not an arbitrary iso of its values; empty X gives the same pair of morphism types;
L=Lambda_X has the tensor unit as inverse; either or both arrows can be zero,
so triangle identities would incorrectly strengthen the datum; level=1 is allowed;
P excludes level=0 itself. No nonempty scheme hypothesis, selected inverse object,
or extra field characteristic condition is added. The full finite-Tor subcategory
keeps all ambient morphisms, so origin-model choices do not restrict naturality.

Searches made:

- msearch.py leanfinder, query `Trace diagonal datum compact support proetale twisted
  pullback unit counit finite Tor constructible`: eight irrelevant affine-transition
  limit matches; no exact definition.
- msearch.py loogle, query `TraceDiagonalDatum, constructibleFiniteTor`:
  TraceDiagonalDatum unknown; no match.
- msearch.py grep, query `TraceDiagonal|traceDiagonal|diagonalIso`:
  two unrelated Mathlib diagonal-isomorphism declarations.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, including blueprint identifier and
  trace/diagonal names: the upstream `AlgebraicGeometry.Etale.TraceDiagonalDatum`
  in `WeilConjectures/EtaleCohomology/Purity/Smooth/TraceDiagonal.lean` is an
  AMBIENT etale definition, not the finite-Tor pro-etale definition here. Its
  `derivedTensorFlipIso` is a chosen Nonempty iso and cannot supply this node's
  explicitly canonical signed comparison. Its pure scheme-theoretic diagonal
  helper in TraceDiagonal.Basic is reused with the explicit pullback codomain.
  No exact existing match was found.
- rg for declarations named Invertible in Mathlib/CategoryTheory/Monoidal found
  only the unrelated monoid-object `GrpObj.ofInvertible`, not a tensor-object
  predicate matching the node.
- rg for `constructibleFiniteTor`, pullback, projection, exchange, composition,
  tensor constraints and compactification independence found the native fixed-module
  constructions used above. Their full signatures and docstrings were read.

No statement correction, independent new notion, or dependency-record repair is
needed. No mathematical statement is disputed. Every definition contains actual
data; the named postponed theorems are the typing/naturality clauses already in
the owning node, with source references and complete natural-language proofs.

Validation: prescribed server scompile.py passed for the complete delivered file
in both modes: sandbox 16.7 s, library module 15.8 s. No errors or warnings were
reported. The final file contains no diagnostic options or commands. The prescribed
deliver2.py --no-push dry run passed preflight and per-file compilation (OK).
The initial metadata-only signature mismatch was corrected by omitting the
terminating `where` keyword, as required by the preflight signature extractor.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

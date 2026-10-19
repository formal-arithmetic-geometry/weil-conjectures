## Worker report

This repairs the returned immutable head `17ef11a3b244`. The saved packet was
inspected first and `deliver2.py ... --no-push` was run before editing; it passed
mechanical preflight as `3f6558cf77`. The independent review correctly identified a
semantic defect that compilation did not detect. The retained theorem allowed
unrelated scalar functors, geometric functors, adjunctions, lambda maps and theta
maps. Even with every functor identity, its arbitrary `lambda_h` could be zero
while the other comparisons were identity. The required equality then fails on a
nonzero object. No cube compatibility constrained those arguments. The repaired
packet changes that signature and the definitions used in it; it is not an
unchanged rebase or re-push.

The module `Sheaf.SecSmoothPurity.DirectImageScalarExchange` now states
`AlgebraicGeometry.ProEtale.directImageScalarExchange` with just the rings, their
map, the four schemes and morphisms, the chosen cartesian square, and M. It has
one `sorry`, the whole proof of that named theorem. Every helper has real data
assembled from published constructions. No hypothesis supplies a functor, an
adjunction or a comparison. The module and every declaration have source and
blueprint docstrings; the theorem docstring contains the node's four proof steps,
including the two mate-pasting instantiations and the top/bottom whiskering rule.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite commutative rings A and B | `{A B : Type u}`, `[CommRing A]`, `[CommRing B]`, `[Finite A]`, `[Finite B]` |
| The ring homomorphism A → B | `(φ : A →+* B)`; `proEtaleConstantRingMap φ` applies the constant-sheaf functor to `RingHom.ulift φ` |
| Four schemes, all four arrows | `{X' X Y' Y : Scheme.{u}}`, followed by `h`, `f'`, `f`, `g` with exactly the displayed domains and codomains |
| Chosen cartesian square | `sq : ChosenCartesianSquare h f' f g`; `sq.w` supplies the actual commutativity used in the ambient exchange |
| Ordinary unbounded constant-ring module derived categories | `Scheme.proEtaleDerivedCategory T A`, the standard localization of modules over the sheafified constant ring, with the published ULift size convention |
| Canonical inverse images | `Scheme.proEtaleConstantRingDerivedPullback A f`, exact termwise descent of the published module pullback using the canonical constant-section coefficient comparison |
| Canonical direct images and adjunctions | `directImageConstantPush A f` specializes `proEtaleRingDerivedDirectImage`; `directImageScalarComparison` uses `proEtaleRingDerivedAdjunction` with those same coefficients and comparisons |
| S_T = derived extension along A_T → B_T | `directImageScalarExtension φ T` is an abbreviation for the published `proEtaleRingDerivedExtension (proEtaleConstantRingMap φ)`, with its universal derived counit and K-flat computation |
| Canonical lambda_u | `directImageScalarPullbackIso φ f` specializes `proEtaleReductionPullbackIso`; the coefficient square is proved by `proEtaleConstantInverseImageMap_naturality`, rather than supplied as a hypothesis |
| Normalization on K-flat representatives | The existing reduction/pullback construction is the inverse scalar-adjunction mate of exact restriction/pullback. Its ordinary restriction comparison is the geometric-adjunction mate of identity on sections. The ordinary scalar adjunction is fixed by insertion of `1 tensor m`, and its derived adjunction by the universal K-flat counit. Hence its comparison is the tensor balancing comparison specified by the node, not an arbitrary natural isomorphism |
| chi_u is the geometric adjunction mate of lambda_u | `directImageScalarComparison φ f` is `mateEquiv` of the canonical derived adjunctions applied to `(directImageScalarPullbackIso φ f).hom` |
| Ex^R is the ambient ringed exchange | `directImageConstantExchange R sq` calls the existing `proEtaleAmbientRingedExchange`, with the four canonical constant-ring identifications. Compatibility follows from `proEtaleConstantRingCompositeCoefficients_eq` on each route and dependent congruence along `sq.w` |
| Every M in D(X,A) | `(M : Scheme.proEtaleDerivedCategory X A)` is arbitrary, including unbounded M |
| Left composite | `pullback_B_g.map (chi_f.app M) ≫ Ex_B.app (S_X.obj M) ≫ push_B_f'.map (lambda_h.hom.app M)` |
| Right composite | `lambda_g.hom.app (push_A_f.obj M) ≫ S_Y'.map (Ex_A.app M) ≫ chi_f'.app (pullback_A_h.obj M)` |
| Common source and target in D(Y',B) | Lean checks the equality as a composition of three morphisms on each side, with the exact source `g_B^-1(S_Y(Rf_*^A M))` and target `Rf'_*^B(S_X'(h_A^-1 M))`; no equality transports of objects are assumed |
| Natural in M | Each constituent is a specified natural transformation or functor map, so the displayed universal component equality is an equality between the two natural composites |
| No extra geometric or coefficient restrictions | There is no properness, boundedness, constructibility, Tor-amplitude or coefficient-flatness binder |

The dependency declarations and their full signatures/docstrings were read. The
current records include specializations in addition to their general interfaces:

- `def-weil-pbc-proetale-modules`: module
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, declaration
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`. Its canonical coefficient
  presentation and realization interfaces are publicly retained. The theorem uses
  the published intrinsic constant-ring category, not a privately defined category.
- `def-weil-pbc-proetale-operations`: module
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, declaration
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`, together with
  `proEtaleConstantRingComparison`, `proEtaleRingDerivedDirectImage` and
  `proEtaleRingDerivedAdjunction` from its published ring-sheaf operations.
- `def-weil-pbc-adjunction-mate`: Mathlib
  `CategoryTheory.mateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`, with
  the orientation `G ⋙ L₂ ⟶ L₁ ⋙ H` to `R₁ ⋙ G ⟶ H ⋙ R₂`.
- `def-weil-pbc-cartesian-square`: module
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, declaration
  `AlgebraicGeometry.ChosenCartesianSquare`, used by the theorem and by ambient Ex.
- `lem-pur-derived-change-of-rings`: the current primary record is the etale
  specialization `AlgebraicGeometry.Etale.scalarTensorIso_existsUnique` in
  `Sheaf.Paper.EtaleDerivedScalarTensor`; its publicly reexported full ring-sheaf
  interface is `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` in
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`. The latter
  is the correct interface for the original small pro-etale site. It underlies the
  existing universal `proEtaleRingDerivedExtension` used here. No etale category
  is substituted for the pro-etale category, and no duplicate scalar functor is built.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: current module
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, declaration
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  with its ordinary pure-tensor/unit and K-flat normalization interfaces. The
  specialized scalar/pullback comparison is the already published
  `Scheme.proEtaleReductionPullbackIso` in `Sheaf.Paper.FourCorners`, using
  `Scheme.proEtaleRingRestrictionDerivedPullback` from
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `def-weil-pbc-ambient-ringed-exchange`: its current module
  `Sheaf.Paper.PbcActualRingedExchange` publicly retains the general
  `Scheme.proEtaleAmbientRingedExchange` and
  `Scheme.proEtaleAmbientRingedPullbackComparison` in
  `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`. We specialize that
  ordinary interface to constants; we do not use the completed specialization.

The stated proof-dependency modules
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` and
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition` are imported for
stage 3. The Mathlib mate-pasting declarations are in the imported Mates module.
The source passage read was `sites-cohomology.tex`, lines 4032–4127:
`remark-base-change`, `remark-compose-base-change`, and Tag 0E47,
`remark-compose-base-change-horizontal`.

Edge cases checked: the identity square and coefficient identity use exactly the
same canonical constructions, so no arbitrary normalization remains; M = 0 gives
the zero composites; empty schemes are allowed by every binder and by the
constant sheaf/unit constructions; the zero coefficient ring is allowed;
non-flat `Z/4 → Z/2` and unbounded M need no new hypothesis, since scalar extension
is genuinely derived and inverse images are exact. The original small site keeps
object universe u+1 and morphism universe u; none of these is identified with the
other to fit a specialized API.

Searches made (retained search log plus repair searches):

- `msearch.py ... leanfinder "derived scalar extension compatibility with direct image base change exchange mate canonical coefficient comparison"`: eight hits, including `IsBaseChange.comp`, `IsBaseChange.of_comp`, `ModuleCat.homEquiv_extendScalarsComp` and `ModuleCat.extendScalarsComp_hom_app_one_tmul`; no derived geometric-exchange equality.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.Functor.whiskerLeft"`: `CategoryTheory.mateEquiv_apply`, `CategoryTheory.mateEquiv_symm_apply`; the generic mate construction, not this target.
- `msearch.py ... grep "scalar.*exchange|direct.*image" Mathlib/CategoryTheory`: zero hits.
- `rg` for the item id and `directImageScalarExchange` in the named upstream and side Lean directories: no existing target declaration.
- `rg` for scalar extension, constant-ring maps, reduction/pullback, canonical adjunctions and ambient exchange found the published constructions used above. In particular `proEtaleConstantRingMap` in `StratumScalarExtension` and `proEtaleReductionPullbackIso` in `FourCorners` eliminate any need for a new notion or dependency replacement.

No source statement is changed or disputed. The faulty old Lean rendering was
replaced; the mathematical DAG statement, proof and dependency fields stay intact.
The node copy was refreshed from the current shared DAG and only `lean` changed.
All six helper/main declaration names are recorded in `lean.declarations`, and
`lean.statement` is the exact multiline theorem signature from the file.

## New nodes

None. All added helpers are real specializations of existing constructions that
belong to the maps explicitly named in this item's statement.

## Dependency modules

None. The current published general interfaces remain usable through the exact
imports listed above; no copied or arbitrary comparison interface is introduced.

## Second reading by Q34

I checked the repaired theorem against every hypothesis and clause of the
unchanged node, and against the source's unit/square/counit construction and
horizontal pasting identity. Unlike the returned head, φ determines every scalar
extension and scalar/pullback comparison, and sq determines every geometric
exchange. There are no arbitrary-functor/comparison binders and no compatibility
hypothesis replacing the coefficient/pullback cube. Each of the three arrows on
each side has precisely the source and target of the displayed node formula.
The helper definitions select only published normalized constructions, not a
mere existence of an unconstrained map or natural isomorphism.

Both defects named in the return are repaired in the file: the maps are canonical,
and the module/proof-step documentation is complete. The single-file compile by
`scompile.py` passed in 4.3 seconds for the sandbox probe and 2.9 seconds for the
library module, with no errors or warnings. The only postponed theorem is
`AlgebraicGeometry.ProEtale.directImageScalarExchange`, as required in stage 2.

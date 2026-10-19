## Worker report

The delivery states `WeilConjectures.OrdinaryFieldRealization.exists_ordinaryFieldRealization`
in `Sheaf.Paper.FieldStageOrdinaryRealization`. Its conclusion is `Nonempty (System l Y Ω)`.
`System` packages the functors with their formulas; it is not a hypothesis asserting that
any of them already exist. All theorems have `sorry` proofs. Definitions contain actual
data, existing universal constructions, or choices from uniquely normalized theorems.
There are no axioms, added geometric hypotheses, or constructibility assumptions on targets.

Hypotheses and coefficient objects:

- The global datum is `(D : FiniteFieldDatum.{d})`; the coefficient prime is `(l : ℕ)`
  with `[Fact l.Prime]` and `(_hl : l ≠ D.p)`.
- The chosen closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`; `(Y : Scheme.{u})` is arbitrary. In particular there is
  no finite type, quasi-compactness, Noetherian, or structure-map hypothesis on Y.
- Finite subfields are `AlgebraicallyClosedCoefficients.Index l Ω`. Their rings are
  the recorded `Coefficient.{u} l Ω E = Shrink.{u} E.val`, with the existing
  `Shrink.algEquiv`. This is the dependency's precise finite-coefficient presentation.
- The valuation ring and uniformizer are `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`; the completed coefficient sheaf and the
  compatible quotient-cone lift are the recorded
  `completedIntegralCoefficientSheafUnrestricted` and
  `integralConstantToCompletionOfUniverses`.
- `integralRestriction` is literally `SheafOfModules.restrictScalars` along that lift.
  `integralRestriction_exact` states its kernel/cokernel preservation; the two instances
  expose this proof to `mapDerivedCategory`. `integralDerivedRestriction` is U_E.
- `constantRing` abbreviates the actual `constantSheaf` of the lifted commutative ring.
  `Ambient Y A` abbreviates the existing `Scheme.proEtaleDerivedCategory Y A`.
  These are discrete constant coefficient sheaves, not continuous field coefficients.
- `extend Y f` is the existing `reductionDerivedChange` of the actual constant-sheaf
  map `coefficientMap Y f`; it is ordinary uncompleted K-flat scalar tensor and retains
  the target coefficient action. `integralRealization` is the integral inclusion,
  followed by U_E, followed by extension from O_E to E.

Every asserted clause:

- `System.finite E` is J_E with domain the recorded intrinsic raw rational stage
  `GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E` and target `Ambient Y E` in
  its canonical small coefficient model. These are raw localizations, with no Karoubi
  completion. `finite_additive` and `finite_linear` assert E-linearity.
- `integral_objects` is the literal object formula J_E(C) = U_E(C) tensor^L E_Y.
  A raw localized object has its unchanged integral representative `C.obj`.
- `scalar_morphisms` uses `sfRationalHomCoordinates` in its Hom-first coordinates
  `f ⊗ₜ a` through the definition `stagePureHom`, and asserts that the image is
  `integralScalarMap`, which is literally `a • integralRealization.map f`.
  `HEq` accommodates the separately recorded object equality, without adding a cast
  or a choice of comparison. `constantLinear_existsUnique` specifies the target
  action by multiplication by the sheafification unit's constant section.
  `rationalLinear` transports the existing localized scalar action through the
  recorded field equivalence via Mathlib's category-center construction.
- `finite_bounded` supplies integers r ≤ s and `IsZero (H^i (J_E(C)))` for every
  i < r or s < i, using `DerivedCategory.homologyFunctor`.
- `comparison E L h` is the natural isomorphism
  `transition(E,L) ⋙ J_L ≅ J_E ⋙ extend(E→L)`.
  The transition is the recorded `stageTransition`; `stageIdentification` retains
  its equality with the recorded rational scalar-extension functor.
- `identity`, through `HasComparisonIdentity`, is the unit equation. `stageUnit` uses the dependency's normalized
  rational unitor, and `fieldUnit` uses ordinary scalar multiplication.
- `composition`, through `HasComparisonComposition`, writes out the two paths for
  E ≤ L ≤ M, using the exact associator
  from the dependency's `stageSystem` and the ordinary `fieldComp` comparison.
  `extendComp_existsUnique` fixes that comparison by the universal derived counits
  and the existing `reductionBalance` map, not by a bare Nonempty choice. Its formula
  is stated on every complex: the K-flat identity extends to arbitrary complexes by
  counit naturality along a K-flat resolution.
  `extendUnit_existsUnique` fixes the unit by the sectionwise formula a⊗x ↦ a*x.
- `System.closure` is J_Qbar from the recorded `Pair` common-stage category.
  `closure_objects` is its object formula as an isomorphism to J_E(C) tensor^L Ω_Y.
  `closure_additive` and `closure_linear` assert Ω-linearity.
- `common_morphisms`, through `HasCommonMorphismFormula`, specifies the image of every
  `ofHom` representative at a common
  finite L: pass to L by `toCommon`, apply J_L, extend to Ω, and conjugate back by the
  displayed object identifications. `toCommon` is made from `comparison` and the
  normalized ordinary associator `closureComp`. Hence these are the actual maps
  from the node, not arbitrary comparison maps. A functor with this property is
  independent of representatives and respects the common-stage composition law.
- `closure_bounded` is the analogous cohomology-vanishing interval for every closure
  object. No clause asserts constructibility in either ordinary target.

Universes: d, u and v are independent. `closureSmall` uses Mathlib's existing
`IsAlgClosure.equiv` with the small algebraic closure only to establish `Small.{u} Ω`.
`Closure = Shrink Ω`, `closureEquiv`, and `closureInclusion` retain the explicit
identification with the chosen Ω and the actual finite subfield inclusions. No random
closure automorphism enters the coefficients. The source pair category keeps its
original index universe v; the small pro-etale site keeps object universe u+1 and
morphism universe u. The closure action on pair Homs is uniquely specified by finite
representatives in `pairLinear_existsUnique`; it is not an arbitrary module structure.
`stageSmul` explicitly reuses the finite stage's `stageHomModule` scalar action.

Dependency declarations used (sources and full signatures/docstrings inspected):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageTransition`,
  `stageSystem`, `Pair`, `StageHom`, `ofHom`, `unitor`, `stageSystem_existsUnique`.
  `Sheaf.Paper.AlgebraicallyClosedCoefficients`: `Index`, `Coefficient`,
  `coefficientInclusion`, `coefficientInclusion_laws` and `coefficientSmall`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalHomCoordinates`, `sfRationalCoefficientEquiv` and the actual raw
  localization used by the preceding common-stage declarations.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory, carrying derived completeness, all positive constructible reductions,
  and one cohomological interval independent of reduction level.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imports:
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its compatible quotient cone.
- Mathlib `AlgebraicGeometry.Scheme.ProEt` / `ProEt.topology`,
  `CategoryTheory.constantSheaf`, `SheafOfModules.restrictScalars`, and
  `DerivedCategory.homologyFunctor` are the recorded site, constant sheaf,
  restriction, and cohomology dependencies.
- `Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`:
  `SheafOfModules.ringedSiteDerivedTensorOfUniverses` is the intrinsic ordinary
  tensor interface; `Scheme.reductionDerivedChange`, `reductionScalarComplexCounit`,
  and `reductionBalance` in `Sheaf.Paper.AdicCoefficientDatum` are its canonical
  coefficient-change form and counit-normalized balanced tensor comparison.

The imports also retain every currently stated proof dependency: integral linearity,
ordinary tensor functoriality and resolution independence, the residue cohomology bound,
finite-free completed scalar comparison, derived change of rings, constructibility of
integral scalar extension, and scalar-extension composition. The module docstring and
main theorem docstring give the five source proof steps, including the affine-local
boundedness argument for non-quasi-compact Y.

Edge cases checked mathematically: empty Y and its empty covering objects; zero objects;
integral torsion objects (rationalization maps them to zero); E=L and all repeated fields
in a tower; a proper inclusion E<L<M; negative, zero, and positive cohomology degrees;
arbitrary non-quasi-compact Y via the same uniform interval before affine localization;
and independent closure/site universes. No counterexample or statement fault was found.
The affine-local Tag 09C2 argument does not add a global quasi-compactness hypothesis.

Searches made:

- `msearch.py ... leanfinder "Scalar localization of derived complete constructible
  integral sheaves has a bounded ordinary constant field realization compatible with
  coefficient extension"`: 8 hits, about constant sections, localizations, BDeRham and
  finite projective modules; no realization theorem.
- `msearch.py ... loogle "SheafOfModules.restrictScalars, DerivedCategory"`: 0 hits.
- `msearch.py ... grep "realization|Realization|realisation" Algebra/Homology`: 0 hits.
- `rg` on upstream WeilConjectures and project lean/Sheaf for ordinaryRealization,
  field-stage realization, constructible realization and this node id: no match for
  the node. The condensed E-realization module has continuous coefficient targets and
  stronger geometric hypotheses, so is not this ordinary constant-field statement.
- The explicit upstream node-id grep has no hits. The upstream name index was also
  inspected with `tools/lean_names_upstream.py show OrdinaryFieldRealization`.
- Read Stacks proetale.tex, lemma-describe-constructible-complexes (Tag 09C2), its
  statement and proof; read Bhatt--Scholze Proposition 6.8.14 and its proof on printed
  pp. 61–62; read the current blueprint field-Tor-amplitude proof, first two sentences.

Validation: `scompile.py Q23 lem-sf-field-stage-ordinary-realization
lean/Sheaf/Paper/FieldStageOrdinaryRealization.lean` exited 0 with no errors or warnings:
overlay compilation 37.5 seconds and current-server confirmation 37.8 seconds.
The final file has no diagnostic commands, no unbound implicit variables, and all lines
fit the 100-character limit. The prescribed `deliver2.py --no-push` dry run returned OK: its commit passed
the maintainer preflight and every required per-file compilation.

## Dependency modules

`def-weil-derived-tensor`: lean-only existing-interface repair under §1(B). Its old
record names the ModuleCat-valued fixed-ring sheaf presentation. This item and its
recorded integral category, completion and u_E use intrinsic `SheafOfModules`, so that
record has different endpoints. Rebind to the already published
`SheafOfModules.ringedSiteDerivedTensorOfUniverses` in
`Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`, with the full independent-site-
universe signature and `existing: true`. It is the same ordinary K-flat total tensor;
no new module or construction, and no change to the dependency's mathematical statement,
Mathlib match, or any other field. The scalar-change notation in the item's module is
its canonical ordinary derived-change-of-rings form, retaining target scalar actions.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

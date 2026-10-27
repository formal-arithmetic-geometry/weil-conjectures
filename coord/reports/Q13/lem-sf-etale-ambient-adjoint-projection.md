## Worker report

The delivery states `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection` and defines
`AlgebraicGeometry.Etale.sfEtaleAmbientTensorMap` in
`Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`. No node statement was changed.
The only postponed proof is the named main theorem, whose docstring records all nine
steps of the node's proof. The definition contains the actual composite and adjunction
transpose; its projection-invertibility instance comes from the main theorem.

Source read: blueprint main-20261015,
`sec-six-functors-basics/sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`, paragraph 1.
I also read the node's specified arbitrary-base upstream declarations in
`LowerShriekLeftAdjoint.lean` and `ProjectionFormula.lean`, together with the full
compactification and projection-map definitions. The blueprint constructs the map by
transposition; the node explicitly extends its setting to arbitrary bases. This is a
statement delivery, not a change to the blueprint unit or its proof route.

Hypothesis and clause correspondence:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  There is no nonzero-ring or invertibility assumption.
- Arbitrary schemes and their morphism are `{X Y : Scheme.{u}} {f : X ⟶ Y}`.
  No Noetherian, finite-dimensional, separated, or finite-type hypothesis is imposed on f.
- The supplied factorization is `(c : Compactification f)`. The actual structure has
  `Z`, `i`, `g`, `comm : f = i ≫ g`, `isOpenImmersion`, and `isProper` fields.
  Its docstring and signature explicitly allow a non-quasi-compact open immersion.
- Ordinary unbounded categories are `DerivedCategoryModule A X` and
  `DerivedCategoryModule A Y`, abbreviations for the derived categories of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`. Neither D+ nor a constructible
  subcategory occurs. The one common universe follows the recorded coefficient convention.
- `F_f = Rr_* Dj_!` is exactly
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`, whose
  definition is `D((c.i)_!open[...]) ⋙ R((c.g)_*[...])`.
- Existence of G and its adjunction is the first conjunct, `F_f.IsLeftAdjoint`.
  This Mathlib property asserts existence of a right adjoint and adjunction data;
  a selection gives the `G` and `adj` arguments to the helper. Its natural counit
  is `adj.counit : G ⋙ F_f ⟶ 𝟭 _`, with `adj.counit.app` the required components.
- Every M and K is covered by the second conjunct's universal quantifiers.
  `IsIso (((projectionMapOfCompactification ... c).app M).app K)` asserts
  invertibility of the actual canonical arrow with exactly the displayed endpoints.
  The upstream component formula composes the proper counit-defined projection,
  the inverse open-extension tensor comparison, and inverse-image composition.
- Derived tensor is the recorded `derivedTensor`, used explicitly in the helper.
  Inverse image in the canonical projection is the left-derived `upperStar`;
  `leftDerivedUpperStarIsoMapDerivedCategory` canonically identifies it with
  termwise exact `upperStar`. This uses the recorded inverse-image functor, not a
  replacement pullback or an extra exactness assumption.
- The helper puts omega equal to `G.obj (constantComplex A Y)` and has source
  `derivedTensor(omega, L(upperStar f).obj K)` and target `G.obj K`.
  `constantComplex A Y` is the constant coefficient sheaf in degree zero.
- The helper's defining data are `adj.homEquiv _ _` applied to `inv PF`, followed
  by `derivedTensor.map (adj.counit.app (constantComplex A Y))` at K, then
  `(derivedTensorLeftUnitor ... K).hom`. Thus it is precisely the displayed
  inverse-PF/counit/unitor composite transposed under the selected adjunction.
  K is unrestricted, and the helper makes no assertion that theta is invertible.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `constantComplex`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, `preservesFiniteLimits_openImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`,
  `upperStarLowerStarAdjunction`; the composition comparison is `upperStarComp`,
  with its unit coherence in the sibling `UpperLowerStar.Coherence` module.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap` and its explicit counit component formula.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`:
  `projectionMapOfCompactification`, its component formula, and
  `leftDerivedUpperStarCompactificationIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`:
  `derivedTensorLeftUnitor`, `derivedTensorRightUnitor`.

All recorded proof-dependency modules are imported (non-public for proof-only imports).
The additional existing adjunction/projection results are available for stage 3. The
statement-dependency modules above are exposed transitively through the public imports;
there is no private copy of any notion. No new node or dependency-record repair was needed.

Searches performed:

- `msearch.py`, LeanFinder: “For finite ring coefficients compact support pushforward
  on unbounded etale derived categories has a right adjoint and canonical projection
  formula”. Eight hits; ordinary module-sheaf pushforward adjunctions and condensed
  module constructions, no exact match.
- `msearch.py`, Loogle: `"DerivedCategory", "IsLeftAdjoint"`. Zero hits.
- `msearch.py`, grep of Mathlib: `rightDerivedLowerShriek|dualizingComplexTensorMap`.
  Zero hits.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`,
  `projectionMapOfCompactification`, `dualizingComplexTensorMap` and the node id.
  This found the separate upstream adjoint theorem, projection constructions,
  finite projection theorem and globally chosen-compactification tensor map.
  I read their signatures, binder contexts, full definitions and docstrings.
  The adjoint theorem alone omits projection and theta; the projection theorem alone
  omits the adjoint; the existing theta uses `HasCompactification.compactification f`
  rather than the supplied c. Thus no single declaration states the complete node.
  This delivery reuses all canonical constructions, packages the two assertions,
  and gives the direct transpose for the supplied factorization and selected adjunction.
- Name/id searches in `dag/lean_names_upstream.json` and repair notes found no attachment
  or maintenance repair note for this node.

Edge cases checked: A=0 is allowed (`Finite` and `CommRing`, no `Nontrivial`);
empty schemes and the zero derived object are allowed; identity factorizations are
allowed by `Compactification.ofIsProper`; an arbitrary non-quasi-compact open is allowed
by the structure definition; the ambient categories impose no cohomological bounds.
The proof plan includes empty indexing sets and sums, and does not assume a global
cohomological-dimension bound over an infinite disjoint-union base. No extra universes
are equated. The helper can be used with any selected right adjoint of this exact F.

Validation: prescribed server `scompile.py` compiled the sandbox and named library
module cleanly, with no errors or non-sorry warnings (33.4 s and 21.4 s respectively).
The interrupted process handles expired, so the final compile output was saved in
`scratchpad/compile.log`. The delivery dry run passed preflight and compilation; the supplied statement and all
helper definitions are accepted by the prescribed mechanical checks.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

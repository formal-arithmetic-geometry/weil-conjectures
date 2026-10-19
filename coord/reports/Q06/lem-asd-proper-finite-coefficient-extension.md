## Worker report

This repair replaces the arbitrary extension functors, comparison isomorphisms, and
unconstrained map `π` in the previous packet by the canonical constructions fixed by
the project.  The module is
`lean/Sheaf/SecSmoothPurity/ProperFiniteCoefficientExtension.lean`, and the item
node now records its declaration.  The added statement dependency
`lem-pur-etale-scalar-mate-projection` supplies the canonical ambient scalar mate,
pullback comparison, and restriction/direct-image comparison used by the signature.
The item statement itself is unchanged: it is rendered directly with the canonical
objects that its prose calls for.

The theorem has finite commutative rings `R` and `A`, a unital ring map
`φ : R →+* A`, schemes `X,Y`, a proper morphism `f : X ⟶ Y`, and Noetherian
instances for both schemes.  The canonical extension functors are
`scalarExtension φ X` and `scalarExtension φ Y`; the canonical derived inverse-image
comparison is `scalarPullbackIso φ f`; and the canonical A-linear mate is
`scalarMate φ f`.

The first conjunct is
`∀ L : DerivedCategoryModule R X, IsIso ((scalarMate φ f).app L)`, which renders
that the coefficient-change comparison is an isomorphism on every unbounded object.
Its naturality is built into `scalarMate φ f : R(f)_* ⋙ scalarExtension φ Y ⟶
scalarExtension φ X ⋙ R(f)_*`.

The second conjunct is the restriction-of-scalars identification with the ordered
proper projection.  Its left side, clause by clause, is:

* `((derivedTensorSymmetry R Y).hom.app (scalarCoefficient φ Y)).app (Rf_* L)`
  changes the coefficient-first source `A_Y ⊗ᴸ_R Rf_*L` to the tensor order used by
  the projection-map API;
* `(scalarTensorIso φ Y).inv.app (Rf_* L)` identifies that tensor with the
  restriction of `scalarExtension φ Y (Rf_* L)`;
* `Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ` maps the component of the
  canonical mate;
* `(scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L)` is the
  canonical direct-image composition comparison;
* `Rf_* ((scalarTensorIso φ X).hom.app L ≫ (derivedTensorSymmetry R X).hom.app L)`
  identifies the restricted target with the coefficient-first tensor
  `A_X ⊗ᴸ_R L`.

The right side is the canonical ordered projection: the symmetry at `Y`,
`rightDerivedLowerStarProjectionMap R f` at `(L, scalarCoefficient φ Y)`, then
`Rf_*` of the tensor map induced by the canonical coefficient pullback
`scalarCoefficientPullbackIso φ f` followed by the symmetry at `X`.  Thus both tensor
symmetries required by the source statement occur explicitly.

The third conjunct is the exact counit normalization.  For every `L`, the component of
`scalarMate φ f` equals the `A`-adjunction hom-equivalent of
`(scalarPullbackIso φ f).hom.app (Rf_*L)` followed by `scalarExtension φ X` applied to
the `R`-adjunction counit.  This is the displayed counit transpose in the node
statement, with no extra boundedness, flatness, or nonzero assumptions.

### Dependency declarations used

* `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme`.
* `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
  `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
* `AlgebraicGeometry.Etale.DerivedCategoryModule` and `constantComplex` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
* `scalarExtension`, `scalarCoefficient`, `scalarTensorIso`, and the scalar/tensor
  normalization from `Sheaf.Paper.EtaleDerivedScalarTensor` (the recorded
  `lem-pur-derived-change-of-rings` interface).
* `scalarPullbackIso`, `scalarMate`, and `scalarCoefficientPullbackIso` from
  `Sheaf.Paper.PurEtaleScalarMateProjection` (the added
  `lem-pur-etale-scalar-mate-projection` dependency).
* `scalarRestrictionDirectImageMap` from
  `Sheaf.Paper.EtaleUnboundedRestrictionComparison`.
* `rightDerivedLowerStarProjectionMap` and `derivedTensorSymmetry` from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` and the derived
  tensor framework.

### Edge cases checked

The signature permits `L = 0`, empty schemes, `f = 𝟙 X`, and the identity coefficient
map.  It also permits zero finite rings when the corresponding `CommRing` and `Finite`
instances exist, and non-flat maps such as `ZMod 4 →+* ZMod 2`.  No boundedness or
finite Tor-amplitude condition appears, so negative and arbitrarily high cohomological
degrees are included.  For the identity map, the scalar mate and both scalar/tensor
comparisons reduce to the canonical identity normalizations; for `f = 𝟙`, the
projection expression reduces to the tensor unit/symmetry normalization.

### Searches made

* `msearch.py Q06 lem-asd-proper-finite-coefficient-extension leanfinder
  "canonical unbounded proper direct image comparison finite coefficient extension"`:
  no existing item theorem; only unrelated étale morphism and pushforward hits.
* `msearch.py ... loogle "scalarExtension, scalarPullbackIso, scalarMate,
  scalarTensorIso, scalarRestrictionDirectImageMap"`: the exact project declarations
  were found in `Sheaf.Paper.EtaleDerivedScalarTensor`,
  `Sheaf.Paper.PurEtaleScalarMateProjection`, and
  `Sheaf.Paper.EtaleUnboundedRestrictionComparison`.
* `msearch.py ... grep "proper.*coefficient|coefficient.*proper|projection"` in
  the project sources: the canonical projection API is
  `rightDerivedLowerStarProjectionMap`; the canonical proper isomorphism is the
  reordered projection theorem in `Sheaf.AlgebraicGeometry.ProperProjectionFormula`.
* `rg -n "properFiniteCoefficientExtension"` over the project and upstream source:
  no prior declaration.  `rg -n "scalarMate|scalarPullbackIso|scalarRestrictionDirectImageMap"`
  located the canonical definitions used here.

The repaired module compiles cleanly with `scompile.py`; the expected theorem `sorry`
warning is the only postponed proof.

## Dependency modules

The retained copy of `def-pc-sheaf-restrict-scalars` records the existing
`CategoryTheory.Sheaf.restrictScalars` declaration from
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` as its constant-ring
specialization.  Its Lean record is unchanged in meaning and is needed because the
previous packet had already repaired that dependency interface; the item uses the
project’s derived specialization `Sheaf.derivedRestrictScalars` built from it.

## Second reading by Q06

I reread the retained node and the repaired module together.  The ring hypotheses are
`[CommRing R] [CommRing A] [Finite R] [Finite A]` and the sole coefficient map is
`φ`; the geometric hypotheses are exactly `f : X ⟶ Y`, `[IsProper f]`, and the two
Noetherian instances.  No arbitrary functor, comparison, projection map, flatness
condition, or boundedness condition remains.

The first conclusion clause matches the node’s assertion that the canonical `β_L` is
an isomorphism.  The second clause starts with the coefficient-first tensor, converts
it to the projection API by the `Y` symmetry, applies the canonical scalar mate and
canonical direct-image comparison under restriction, and ends with the coefficient-first
`X` tensor using the `X` symmetry.  Its right side is exactly the canonical ordered
proper projection with the coefficient pullback comparison.  The final clause is the
node’s displayed counit transpose, using `scalarPullbackIso` and the `R` counit under
the `A` adjunction.  Since `scalarMate` is a natural transformation, the required
naturality in `L` is present.  The returned H3 defect is therefore repaired: every map
in the Lean signature is canonical and fixed by the cited project declarations.

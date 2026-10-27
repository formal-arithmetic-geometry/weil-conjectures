## Worker report

The module `Sheaf.WeilSheaf.ProperSheafFiniteness` states
`AlgebraicGeometry.WeilComplex.proper_sheaf_finiteness`, with `sorry` as its only
proof. No definition is introduced. The node is unchanged except for `lean`.

The previous attempt confused the node's stage-1 `reviewed: pass` for group NM
with stage-2 completion. The live node has no `lean` or `reviewed_lean` record.
The completed split is precisely the prerequisite for this stage-2 delivery;
this delivery does not split it again.

Hypotheses and clauses, read against the node and its source:

- A finite field is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- A prime unequal to the characteristic is `(l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]`.
- The coefficient, site, module category and invertible Frobenius structure are
  exactly those in `ProEtaleWeilSheaf k₀ l Z` and `ProEtaleWeilSheaf k₀ l T`.
  These are `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l _)` on the native
  `ProEtale.AdicSheaf` categories of the recorded framework. No coefficient
  model is replaced by a continuous-map condensed ring or a common-stage pair
  category. `PadicAlgCl.locallyFiniteFunctions` remains the coefficient data.
- The two schemes are `{Z T : Scheme.{u}}`, with the two explicit `.Over`
  instances for `Spec (CommRingCat.of k₀)`. The arrow `(p : Z ⟶ T)` is a
  k₀-morphism by `[p.IsOver (Spec (CommRingCat.of k₀))]`.
- Properness is `[IsProper p]`; no redundant assumptions of quasi-compactness,
  quasi-separatedness or local finite type on p are imposed.
- Quasi-compactness, quasi-separatedness and local finite type of T over k₀
  are the respective three classes on `T ↘ Spec (CommRingCat.of k₀)`.
  Because Spec of a field has one affine chart, the first is exactly
  quasi-compactness of the scheme. Since the base is separated, the second
  expresses the scheme's quasi-separatedness as in the recorded dependency.
- Ordinary equivariant direct image is the framework's
  `ProEtaleWeilSheaf.lowerStar k₀ l p`.
- Additivity is the first conjunct `.Additive`.
- Left exactness is the second conjunct `PreservesFiniteLimits` of that functor.
  This is the standard finite-limit formulation for additive functors of
  abelian categories, and matches the source's instance exactly.
- Every F in the constructible heart is quantified as
  `∀ (F : ProEtaleWeilSheaf k₀ l Z), WeilSheaf.objectProperty k₀ l Z F → ...`.
  The property is constructibility of the underlying AdicSheaf, defined by
  pulling back `adicConstructibleSheaf` along `IsoAlgebra.forget`.
- Placing F in degree zero is `(_root_.DerivedCategory.singleFunctor _ 0).obj F`.
- Applying the actual ambient total right derived functor is
  `(ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor.obj` of that object.
  Its source is `DerivedCategory (ProEtaleWeilSheaf k₀ l Z)`; it is not a
  fixed-pair category on `DerivedCategory (ProEtale.AdicSheaf ...)`.
- The final conclusion is `WeilComplex.objectProperty k₀ l T` of this object.
  Its definition in `WeilConjectures.WeilSheaf.Category` is the intersection of
  `DerivedCategory.TStructure.t.bounded` and
  `DerivedCategory.homologyProperty (WeilSheaf.objectProperty k₀ l T)`.
  The first means cohomology vanishes outside a finite integer interval; the
  second means the underlying sheaf of every integer cohomology is constructible.
  Thus neither clause is replaced by a condition on a chosen representative.

Dependency declarations used:

- `def-sf-native-weil-derived-framework`: the recorded entry module
  `WeilConjectures.WeilSheaf.LowerShriek` is publicly imported. It reexports
  `AlgebraicGeometry.ProEtaleWeilSheaf`, `WeilSheaf.objectProperty`,
  `WeilComplex.objectProperty`, and `ProEtaleWeilSheaf.lowerStar`, whose full
  definitions and source docstrings were read in `WeilSheaf/Category.lean` and
  `WeilSheaf/LowerStar.lean`. The recorded coefficient and constructibility
  definitions are retained without copies.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` from Mathlib's `Morphisms.FiniteType` and
  `Morphisms.QuasiCompact`. FiniteType is publicly imported.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, publicly imported. Its
  UniversallyClosed superclass implies quasi-compactness, so it is the node's
  properness, including finite type.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, publicly imported;
  its defining field is quasi-compactness of the diagonal.

The proof docstring carries all five DAG proof steps and their named inputs.
All stated proof dependencies' recorded modules are imported: Proper,
FiniteType, QuasiCompact and Separated from Mathlib;
`Sheaf.CategoryTheory.RingedSiteModules`;
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`;
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` (the existing affine
finiteness theorem);
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`; and
`Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`.
`lem-sf-adic-affine-finiteness-descent` has no recorded declaration yet, so it
has no module to import; it remains a proof dependency, not a statement
prerequisite. It is neither restated nor assumed as a hypothesis here.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "proper direct image of constructible pro-etale
  Weil sheaf has bounded constructible derived cohomology"`: eight hits on
  constructible images, scheme limits and condensed sheaves; none states the
  native equivariant result.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper,
  CategoryTheory.Functor.Additive"`: zero hits.
- `msearch.py ... grep "objectProperty_rightDerivedLowerStar|ProEtaleWeilSheaf"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures/WeilSheaf` and `lean/Sheaf` for
  `objectProperty_rightDerivedLowerStar_singleFunctor`, proper finiteness, and
  `proper_sheaf_finiteness`: the source's singleFunctor theorem is the closest
  result. It is more general in the morphism and asserts only derived finiteness;
  the source separately provides anonymous additive and finite-limit instances.
  No declaration states this node's combined proper specialization. Other
  proper-finiteness modules, including ContinuousAlgClProperHeartFiniteness,
  concern different coefficient categories and do not match.
- `rg` for the item id in `lean/WeilConjectures`: no hit. The exact new name
  was also absent from Mathlib, WeilConjectures and Sheaf.

Edge cases checked: F=0 is allowed and constructible (rank zero is allowed in
`IsAdicLisseSheaf`); Z or T can be empty (no Nonempty hypothesis); identity
proper morphisms are included; degree zero and every negative integer degree
are included by the same homology property. No target-separatedness or fixed
positive characteristic is added. The same universe u follows the recorded
native framework, with its sheaf categories in u+1 and derived categories in
the published standard size; no equality of site object and morphism universes
or independent test universe is introduced. No finite interval or uniform bound
independent of F is imposed.

No statement correction, new node, dependency repair, or disputed assertion.
The only remaining sorry is `AlgebraicGeometry.WeilComplex.proper_sheaf_finiteness`.
The initial scompile.py check passed both sandbox and library compilation,
without errors or non-sorry warnings. The delivery dry run recompiles the final
module with its explicit affine-finiteness proof import.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

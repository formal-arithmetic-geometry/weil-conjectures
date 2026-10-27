## Worker report

Recorded the existing declaration
`AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructibleAdic`
from `WeilConjectures.SixFunctors.ProEtale.Adic.Localization`, lines 69–72.
No Lean module is delivered, because this is an existing exact native statement.
The server source was also read with `scompile.py --source` and agrees with the local source.
Only the item's `lean` field changes; its natural-language statement and dependency lists stay intact.

Hypothesis and object correspondence:

- Prime ell: the enclosing explicit section variables are `{l : ℕ} [Fact l.Prime]`.
  The elaborated declaration quantifies over exactly these variables and `X : Scheme.{u}`.
- Fixed algebraic closure with extended absolute-value topology: `PadicAlgCl l` is
  Mathlib's abbreviation for `AlgebraicClosure (Padic l)`, in
  `Mathlib.NumberTheory.Padics.Complex`; its `normedField` uses the spectral extension
  of the p-adic norm, and `norm_extends` identifies its restriction. This chooses the
  fixed closure in the statement; no completed algebraic closure is substituted.
- Small pro-etale site: `Scheme.ProEt X`, with `Scheme.ProEt.topology X`, is the
  recorded small weakly-etale site. The framework uses modules in universe `u+1`
  and the usual universe lift of the coefficients. No site-universe equality is imposed.
- The sheaf B_T: `PadicAlgCl.locallyFiniteFunctions` in
  `WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf`, lines 74–80,
  has carrier `∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U))`
  inside continuous maps. `adicConstantSheaf_obj_obj` identifies the sections with
  the universe lift of these functions. `locallyFiniteFunctionsComp` gives
  restriction by precomposition; `Adic.Ring.adicFunctionsAlgPresheaf` supplies
  their pointwise ring operations. Thus the coefficient sheaf is the node's B_T.
- A(T): `AlgebraicGeometry.ProEtale.AdicSheaf l X` in `Adic.Module`, lines 49–54,
  is the category of internal modules over this ring sheaf in sheaves of coefficient
  vector spaces. Its objects are precisely module sheaves over B_T, with B_T-linear
  maps, rather than sheaves over the discrete field. This is the native realization
  of the module-sheaf notion in the dependency; no replacement category is defined.
- Constructibility: `IsAdicConstructibleSheaf` in `Adic.Constructible`, lines 142–150,
  quantifies over every point and an open immersion whose image contains it.
  `IsAdicStratifiedLisseSheaf`, lines 115–125, provides a finite type of strata,
  immersion maps, constructible images, unique membership of every point in an image,
  and lisse pullbacks. Immersions provide the locally closed subschemes.
  `IsAdicLisseSheaf`, lines 80–87, provides a pro-etale covering and an existential
  natural-number rank inside the quantifier for each member of the cover, with an
  isomorphism to the direct sum of `Fin n` copies of `AdicSheaf.unit`.
  Rank zero and ranks varying between covering members are included.
- Ordinary derived category and boundedness:
  `boundedConstructibleAdic`, `WeilConjectures.SixFunctors.ClosedImmersionStages:392`,
  is definitionally `DerivedCategory.TStructure.t.bounded ⊓
  DerivedCategory.homologyProperty (ProEtale.adicConstructibleSheaf l X)`.
  `homologyProperty` means every integer cohomology object satisfies constructibility;
  the standard bounded t-structure means vanishing below and above integer bounds,
  equivalently outside a finite interval. This is the ordinary derived category of
  the native module category, not a separate adic derived or two-colimit category.
- Locally Noetherian T: `[IsLocallyNoetherian X]` is the sole scheme hypothesis.
  There is no base-field, characteristic restriction, finite-type condition, or
  quasi-compactness assumption in this declaration. The later localization section's
  hypotheses do not occur in its signature.

Conclusion correspondence:

- Zero and every integer shift are fields of `ObjectProperty.IsTriangulated`:
  `ContainsZero` and `IsStableUnderShift ℤ`.
- Isomorphism invariance is already an instance for this precise object property,
  inherited from the intersection of the standard bounded property and
  `homologyProperty (adicConstructibleSheaf l X)`. The latter uses
  `IsAdicConstructibleSheaf.of_iso`. It is not asserted that `IsTriangulated` alone
  includes strict fullness.
- `IsTriangulatedClosed₂` is the remaining field of `IsTriangulated`. Together with
  the existing isomorphism-closure instance it gives actual middle-vertex membership,
  not just an isomorphic witness. Mathlib's `IsTriangulatedClosed₁` and
  `IsTriangulatedClosed₃` instances give the other two choices, via rotations.
- Finite direct sums follow from Mathlib's existing
  `ObjectProperty.instIsClosedUnderFiniteProductsOfIsTriangulatedOfIsClosedUnderIsomorphisms`
  in `Mathlib.CategoryTheory.Triangulated.Subcategory:674`; in this additive category
  finite products are the finite biproducts. This includes the empty sum using zero.

Dependency declarations read:

- `def-weil-algebraic-closure`: `AlgebraicClosure` and `IsAlgClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `.Basic`.
- `def-weil-l-adic-coefficient-extension`:
  `Padic.finite_coefficientExtensionRing` in
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and its imported
  `Padic.coefficientExtensionAbsoluteValue` in `.CoefficientExtension`.
  These finite-extension data agree with the spectral topology used by `PadicAlgCl`;
  their finite quotient theorem is not needed by this existing instance.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt`,
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`, transparently `SheafOfModules`.
  The existing native `AdicSheaf` implements this mathematical category as internal
  modules, with its own existing abelian instance, as explained above.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-locally-closed-subset`: `IsLocallyClosed`, `Mathlib.Topology.Defs.Basic`.
- `def-weil-constructible-subset`: `Topology.IsConstructible`,
  `Mathlib.Topology.Constructible`, used directly in the native stratification predicate.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`; the every-affine-open formulation is
  equivalent to the stated affine Noetherian covering formulation by its recorded lemmas.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` and
  `CategoryTheory.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
  and `.Triangulated`; the ambient ordinary derived category has these instances.

Edge cases checked: empty scheme (local constructibility is vacuous), zero sheaf
(rank zero), zero complex (an interval such as [0,0] works), negative as well as
positive shifts, empty and arbitrary finite sums, every position of the omitted
triangle vertex, non-quasi-compact locally Noetherian schemes, ranks not uniformly
bounded across strata or covering members, and schemes of any characteristic,
including characteristic ell. The fixed closure is not assumed complete.
There is no statement correction or disputed statement.

Searches (2026-10-22):

- msearch.py leanfinder: "Bounded constructible adic sheaves form a triangulated
  subcategory of the derived category over a locally noetherian scheme".
  Eight hits, including `DerivedCategory.TStructure.t`, `.IsGE`, `.IsLE`, and
  `DerivedCategory.instIsTriangulated`; generic derived results, no exact native hit.
- msearch.py loogle: "ObjectProperty.IsTriangulated, DerivedCategory".
  Zero hits; the service reported unknown identifier `ObjectProperty.IsTriangulated`.
- msearch.py grep: "boundedConstructibleAdic|isTriangulated_boundedConstructible".
  Zero Mathlib hits. Direct Mathlib inspection found the generic object-property
  subcategory API, which supplies the closure consequences described above.
- rg in `lean/WeilConjectures` for `boundedConstructibleAdic` found the exact
  `Localization.lean:69` instance and its underlying `ClosedImmersionStages:392`
  definition. Reading their full signatures and underlying definitions established
  the exact native match. Searching for the item id in upstream sources found no
  blueprint-id annotation; semantic agreement does not rely on such an annotation.
- rg in `lean/Sheaf` for `isTriangulated_boundedConstructibleAdic`,
  `def.*boundedConstructibleAdic`, and `native.*adic.*triangulat` found no duplicate
  declaration. The item-id search found a proof comment in AdicAffineFinitenessDescent.
- Consulted `dag/lean_names_upstream.json`; no current name hit. The current live
  source, also retrieved by `scompile.py --source`, contains the instance.

Validation: a temporary module-mode probe importing the existing upstream module
checks the full elaborated signature with autoImplicit disabled, and synthesizes
ContainsZero, IsClosedUnderIsomorphisms, IsStableUnderShift ℤ,
IsClosedUnderFiniteProducts, and IsTriangulatedClosed₁/₂/₃ for the exact native
bounded constructible property. It compiled cleanly with the prescribed scompile.py (both checks, 13.6 and
12.7 seconds, no warnings), then was removed from the sandbox; there are no new declarations to deliver or prove.

## Second reading by Q74

I reread the node against the complete upstream declaration and the coefficient,
module-category, lisse, stratified, constructible, bounded and homology definitions.
This is a second pass by the same worker; no independent subagent was started,
as explicitly required by the dispatcher. The maintainer performs independent review.
The main possible mismatch was that Mathlib's `IsTriangulated` alone only gives
middle-vertex closure up to isomorphism. I checked the existing strict-fullness
instance separately and validated all three triangle-closure instances, as well as
finite products. The coefficient sections impose exactly local finite-dimensional
span, and the lisse rank quantifier occurs separately for each covering member.
The full elaborated signature confirms that none of the later localization
hypotheses leaked into this instance. No Lean or natural-language statement changed.

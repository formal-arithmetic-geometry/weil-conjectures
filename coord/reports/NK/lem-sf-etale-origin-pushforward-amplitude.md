## Worker report

The module `Sheaf.AlgebraicGeometry.SfEtaleOriginPushforwardAmplitude` states
`AlgebraicGeometry.ProEtale.etaleOrigin_pushforward_amplitude`, with one `sorry` and no
new definitions. The node is unchanged except for its `lean` record. No dependency
repair, statement correction, or new node is needed. There is no repair note for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A morphism of schemes is `{X Y : Scheme.{u}} (f : X ⟶ Y)`; quasi-compactness and
  quasi-separatedness are `[QuasiCompact f] [QuasiSeparated f]`, on this actual morphism.
- The finite commutative discrete coefficient ring is `(B : Type u) [CommRing B]
  [Finite B]`. Constant sheaves interpret the coefficient ring discretely; no topology
  beyond the discrete constant-coefficient interpretation is involved in these operations.
  `ULift.{u+1,u} B` is the published coefficient size convention, canonically the same ring.
  Site objects remain in universe `u+1`, with morphisms in `u`.
- The integer bound is `(N : ℤ)`. `_hN` quantifies over EVERY sheaf of modules on
  `X.smallEtaleTopology` and every integer `q`, with both `0 ≤ q` and `N < q`.
  Its conclusion is `IsZero` of degree-q cohomology of ordinary etale total right derived
  direct image of `M[0]`. This is precisely `R^q f_* M` in the node. No condition on M,
  such as constructibility, flatness, or finite generation, is imposed.
- `(a b : ℤ) (_hab : a ≤ b)` supplies the specified ordered interval.
- `L : FiniteCoefficientEtaleDerivedCategory X (ULift B)` is an ordinary unbounded
  etale derived object. `_hL` explicitly gives some finite cohomological interval
  `[c,d]` for L, which is exactly its boundedness. It does not require strict boundedness
  of a selected representative complex.
- `C = ν_X^* L` is substituted verbatim as
  `(finiteCoefficientIntrinsicDerivedComparison X B).obj L`. This published functor
  is exact termwise comparison followed by the canonical constant-scalar realization;
  no arbitrary comparison map, origin witness, or coefficient identification is assumed.
- `_hC` is exactly vanishing of H^r(C) for `r < a ∨ b < r`.
- The first conjunct concludes H^r(L)=0 for `r < a ∨ b < r`.
- The second conjunct concludes H^i(Rf_proet,* C)=0 for `i < a ∨ b + N < i`.
  It uses `Scheme.proEtaleConstantDerivedDirectImage f B`, the ordinary uncompleted
  total right derived functor on all modules over the constant ring sheaf.
- The final conjunct is `N < 0 → IsZero (Rf_et,* L) ∧ IsZero (Rf_proet,* C)`.
  It includes BOTH zero-object conclusions, in the same order as the node.
  It adds no conclusion about arbitrary pro-etale heart objects.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  The property-collection dependency is a convention, with no own declaration;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.QuasiSeparated` supply
  `AlgebraicGeometry.QuasiCompact` and `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientEtaleDerivedCategory`, the published
  fixed-ring etale module encoding. Its canonical intrinsic constant-ring specialization
  is `finiteCoefficientIntrinsicDerivedComparison` in the existing owning-node module
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`.
  The latter's docstrings identify it with def-weil-pbc-proetale-modules; its source was
  read through the complete definition, including scalar map, realization, and exactness.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, using the existing
  `ProEtale.comparisonUpperStar` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`; the intrinsic derived comparison
  is built from precisely this inverse image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`.
  Its `.rightDerivedFunctor` is the ordinary total derived functor defined in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, with
  K-injective computation supplied by `.KInjective`. On bounded-below inputs this is
  the direct image recorded by def-weil-pbc-direct-image.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the intrinsic
  constant-ring operations of def-weil-pbc-proetale-operations. Its existing additional
  module `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` supplies
  `Scheme.proEtaleConstantDerivedDirectImage`: the right derived functor of the canonical
  sectionwise module direct image, on `Scheme.proEtaleDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; `.HomologySequence` supplies `DerivedCategory.homologyFunctor`.

All stated proof dependencies are imported directly, without `public` when only used by
its planned proof: `proEtaleClassicalSheavesModules` in
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`;
`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses` in
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`;
`Etale.existsUnique_constantModuleDirectImage_leftExact` in
`Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`;
the shift/triangulated instances in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`;
`Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`;
`DerivedCategory.bounded_heart_amplitude` in `Sheaf.CategoryTheory.BoundedHeartAmplitude`;
`Functor.exists_universal_rightDerived_deltaFunctor` in
`WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`; and
`ProEtale.directImageComparison` in
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
Their signatures and docstrings were inspected. The six-step natural-language proof
in the theorem docstring follows all six node proof steps and names the same inputs.

Sources read: local `literature/stacks-project/derived.tex`,
`remark-truncation-distinguished-triangle` (08J5), including the successive-cohomology
triangles, and `lemma-negative-vanishing` (05TC); local `proetale.tex`,
`lemma-fully-faithful` (099T) and `lemma-morphism-comparison` (09A6), including the
qcqs hypotheses. The node uses their bounded-input finite-devissage consequence, as
explained in its proof, rather than imposing a bound on all pro-etale sheaves.

Edge cases checked mathematically before writing: L=0; B the zero ring; empty source
or target; a=b; N=0; N<0; and b+N<a. In the negative case the hypothesis at q=0 forces
f_* to vanish on every module sheaf, so both ordinary derived images are zero.
This also makes the interval assertion valid when that interval is empty. No
nonzero-ring, nonempty-scheme, characteristic, constructibility, or Tor assumption occurs.

Searches actually run, using the prescribed msearch wrapper:

- LeanFinder: `Etale heart bounds control the cohomological range of derived pushforward
  of bounded proetale complexes of etale origin`. Eight hits: `DerivedCategory.IsGE`,
  `IsLE`, their Q/support equivalences and instances, and bounded representative
  existence. These define individual bounds and do not give the comparison/pushforward
  theorem or the N<0 clause.
- Loogle: `DerivedCategory.IsGE, DerivedCategory.IsLE`. Two hits:
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE` and
  `exists_iso_Q_obj_of_isGE_of_isLE`. Neither is this theorem.
- Mathlib grep: `proetale.*(bound|amplitude)|rightDerived.*(isLE|isGE)`.
  Seven hits in general derived localization/Kan-extension files, no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for this node id and
  `etaleOrigin.*[Aa]mplitude|[Aa]mplitude.*etaleOrigin`: no matches.
  The node id/name search in `dag/lean_names_upstream.json` also returned no match.
  Further `rg` for constant derived image and intrinsic comparison found the existing
  canonical interfaces above, which are used without replacement.

No disputed statement or node fault found. Validation: the prescribed server compile
and delivery dry run are run on the exact delivered file; their results are recorded below.

## Second reading by NK

A second pass by the same dispatcher worker (no other agents started, as instructed),
with the node, module and source passages open: the `_hN` quantifier retains q=0 and
all sheaves, `_hL` retains boundedness, and `_hC` bounds the actual intrinsic comparison
of the same L. The conclusion has the reflected input range, the shifted pro-etale
image range, and both negative-bound zero conclusions. In particular no N≥0 assumption
has crept into the theorem. The ULift is the existing coefficient convention and the
pro-etale target is the intrinsic constant-ring category used by ordinary direct image.
No definition is copied or chosen. No mathematical mismatch or statement change was found.
The minor docstring indentation was cleaned up; the signature was unchanged.

Validation results: `scompile.py NK lem-sf-etale-origin-pushforward-amplitude <file>`
passed both the sandbox and named-library compiles (13.2 s and 11.1 s), with no errors
or warnings. The final package, including the explicit direct dependency imports, passed
`deliver2.py NK lem-sf-etale-origin-pushforward-amplitude --no-push`: OK, preflight and
per-file compiles passed (dry-run commit fcdd8a20b7a). A source-only delta check confirms
that only `lean` changed in the node and its recorded signature is verbatim.

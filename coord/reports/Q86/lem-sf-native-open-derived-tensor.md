## Worker report

Q86 states `lem-sf-native-open-derived-tensor` in
`Sheaf.Paper.NativeOpenDerivedTensor`, primary declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_derived_tensor`.
The theorem has `sorry` and a complete proof plan in its docstring. All helper
definitions have real data; the assertion records package conclusions of this
one node. There is no new independent mathematical notion requiring a new DAG
node. No original node field except `lean` changes.

Sources read: Stacks `sites-cohomology.tex`, Tag 0GL1,
`lemma-j-shriek-and-tensor`; `sites-modules.tex`, Tag 0E8I,
`lemma-j-shriek-and-tensor`, and the module pullback composition construction
Tag 03D8. The current blueprint source read is
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`,
Step 1, second Hom bijection. The item is the native equivariant refinement of
these ordinary open tensor maps. The module uses the actual native framework,
not a category of fixed pairs in a derived category.

Hypothesis-by-hypothesis and clause-by-clause correspondence (native names below
are in `AlgebraicGeometry.ProEtaleWeilSheaf`):

* Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`. Prime coefficient distinct
  from the characteristic: `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  The algebraic closure and algebraic l-adic coefficient field are the existing
  choices of the dependency framework; their coefficient sheaf is unchanged.
* Both schemes over the field: `U Z : Scheme.{u}` with the existing `Over`
  instances. Finite type is `LocallyOfFiniteType` and `QuasiCompact` on each
  structure morphism; separated is `IsSeparated` on each structure morphism.
  `j : U ⟶ Z`, `[IsOpenImmersion j]`, and `[j.IsOver ...]` are the open immersion
  over the field. The geometric open used in ordinary operations is exactly
  `Scheme.Hom.geometricFiberMap j (comp_over j _)`.
* The sheaves and ambient categories are the actual `ProEtaleWeilSheaf k₀ l U`
  and `ProEtaleWeilSheaf k₀ l Z` and their Mathlib `DerivedCategory`. The bounded
  constructible full subcategories mentioned as background are not imposed on
  the input of the theorem. Neither input is restricted to degree zero, lisse,
  constructible, or bounded complexes.
* Localized coefficients and module restriction are those of `upperStar` and
  `extensionByZero`. The underlying balanced tensor restriction comparison is
  fixed, rather than chosen arbitrarily, by
  `NativeOpenTensorData.restriction_forget` against the actual
  `ProEtale.adicUpperStarTensorLeftIso`. Thus the localized coefficient
  identification is the one already used by these actual module operations.
* The natural derived isomorphism for every M,N is
  `NativeOpenDerivedTensorData.gamma`, between `nativeOpenDerivedLeft` and
  `nativeOpenDerivedRight`. Its two-variable domain is the full product of
  ambient derived categories. Its tensor is the dependency's
  `nativeDerivedTensor`, and its functors are the exact termwise native functors
  localized by `mapDerivedCategory`.
* The termwise balanced comparison is `NativeOpenTensorData.sheafGamma`.
  Its inverse is fixed by `sheaf_inverse`, the actual adjunction unit transpose
  using the canonical sheaf restriction comparison. The adjunction is fixed by
  both `unit_forget` and `counit_forget` to the ordinary open adjunction.
  `unit_iso` records the open unit isomorphism. Uniqueness of adjunction
  transposes fixes both maps of `sheafGamma`.
* Categorical K-flatness is exactly the dependency's `NativeIsKFlat`, whose
  two-sided definition tests preservation of arbitrary quasi-isomorphisms.
  `extension_kflat` and `restriction_kflat` quantify over every such complex,
  without assuming its terms are flat. These are conclusions, not hypotheses.
* The generic record `OpenTensorPresentation` retains the total comparison,
  representative comparison, and each summand. Its `TA`, `TB` are pinned by
  `NativeOpenPresentationCompatibility` to `nativeTensorTotal`, the existing
  direct-sum total with left degree first and differential
  `d_P tensor 1 + (-1)^p 1 tensor d_T`. Its insertion fields are pinned to
  `nativeOpenTensorInsertion`, the actual `HomologicalComplex.ιMapBifunctor`.
  `summands` identifies every degree-(p,q) summand with the fixed sheaf map.
  Since `totalGamma` is an isomorphism of complexes, the differential and
  inverse are respected as well, including on unbounded complexes.
* `OpenTensorPresentation.model` is
  `OpenTensorRepresentativeNormalization`: the explicit square through
  `DerivedCategory.Q`, actual exact-functor factorization isomorphisms, and
  `nativeOpenTensorModel`. It fixes `gamma` on arbitrary K-flat inputs to the
  localization of that specified total map. The presentation pins its sheaf,
  total, derived tensor, flatness, model, and insertion data to the native
  constructions with `HEq`; these equalities permit dependent transport and
  do not introduce a second tensor or category. Equality of inverse arrows
  follows from equality of isomorphisms' forward arrows.
* The derived inverse unit transpose is
  `NativeOpenDerivedTensorData.inverse_unit` with the actual
  `sheaves.adj.mapExactDerivedCategory`. Its restriction comparison is also
  fixed: `restriction_summands` fixes `totalRestriction` on each summand;
  `restriction_model` localizes it on arbitrary K-flat inputs; compatibility
  pins `sheafRestriction` and `restriction` to the native fields. Thus the
  restriction/tensor isomorphism in the transpose is canonical.
* Frobenius compatibility of both maps holds in the type: all sheaf maps are
  morphisms in the actual Weil sheaf category, and all localized comparisons
  and natural transformations live in its derived category.
* Forgetting is the exact `nativeForget` of
  `lem-sf-weil-native-closed-forgetful`; the tensor comparisons used are exactly
  `(nativeDerivedClosedComparison ...).tensorComparison`, and ordinary tensor
  is its specified `ordinaryClosed.tensor`. `nativeOpenForgetExtension` and
  `nativeOpenForgetPull` are real constructions from the actual functor
  identities and canonical derived factorization maps. The `ordinary` field
  retains a normalized ordinary comparison and the exact commuting square
  `OpenTensorForgetNormalization`. `OpenTensorForgetData.inverse_unit` gives
  precisely the ordinary unit normalization from the ordinary dependency.
  `restriction_compatibility` identifies the ordinary restriction comparison
  on forgotten inputs with the already fixed native comparison. This prevents
  a simultaneous arbitrary rescaling of the ordinary restriction and gamma.
  The forward equality in `compatibility` also fixes the inverse equality,
  since all arrows of the comparisons are isomorphisms.
* The composable-pullback clause is the actual definition `nativeOpenPullComp`.
  For any composable field morphisms j,p it is the localization of the existing
  `(upperStarCompIso k₀ l j p).symm`, composed with the canonical
  `mapDerivedCategoryCompIso`. The existing compositor is the module
  adjunction compositor: on balanced generators its map multiplies b j*(c)
  and the inverse inserts 1. Thus the declaration supplies the specified map,
  rather than positing an arbitrary isomorphism. It is defined for all field
  morphisms, hence includes the required separated finite-type p; its arrows
  are native Weil arrows, and it is a `NatIso` on the full derived input.

Dependency declarations used, after reading their signatures and docstrings:

* `WeilConjectures.WeilSheaf.LowerShriek` publicly supplies the framework's
  `AlgebraicGeometry.ProEtaleWeilSheaf`, actual coefficients, `upperStar`, and
  `extensionByZero` (the node's full declaration list includes these). Its
  constructible compact-support entry point is
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`; this node needs the
  unrestricted open operations, not that constructible restriction.
* `WeilConjectures.WeilSheaf.UpperStarComp` supplies the actual
  `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompIso` used in the real
  compositor definition.
* `Sheaf.Paper.DerivedWeilOperations` supplies
  `AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorBifunctor`,
  `nativeTensorTotal`, `NativeIsKFlat`, `nativeDerivedTensor`,
  `nativeDerivedTensor_models`, and `nativeDerivedClosedComparison`.
  `nativeOpenTensorModel` takes the isomorphism from the already recorded
  representative theorem, which determines its object and normalization.
* `Sheaf.Paper.NativeWeilClosedForgetful` supplies
  `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForget`,
  `NativeClosedComparison`, and `native_closed_forgetful`. Its recorded
  ordinary tensor and tensor comparison are used unchanged.
* `Sheaf.SixFunctors.OpenTensorNormalization` supplies
  `SheafOfModules.openTensorNormalization` and its operations/assertion
  interface. This uses sheaves of modules on sites, whereas the native
  framework uses the existing module-object interface. The exact same
  unit-transpose normalization is written on the actual module-object
  functors in `OpenTensorUnitNormalization`; no alternate ordinary theorem or
  alternate category replaces that dependency.
* Every recorded proof-dependency module is imported, including exact derived
  adjunction, ordinary localized restriction, total K-flat comparison,
  generator normalization, twisted-action realization, equivariant
  resolutions, tensor restriction, derived descent, and site localization.
  The Mathlib localization leaf is provided by the derived-category imports.
  `lem-sf-native-adic-open-restrictions` has no recorded module yet; its
  invertible-unit assertion needed here is a conclusion in this item's
  record, with the node's own proof plan retained.

Edge cases checked on the intended statement: empty U (extension is zero),
identity j (unit and tensor comparison identities), zero M or N, arbitrary
unbounded complexes, and p the identity. None is excluded by a binder. Both
K-flat tests are two-sided and allow acyclic unbounded test complexes. No
characteristic-zero assumption is added to the finite base field, and ell=2
is allowed when distinct from its characteristic. The universe `u` is the
same as the native dependency framework's scheme and base-field universe;
generic presentation universes `a b` do not change the native category sizes.

Searches for an existing full statement:

* `msearch.py ... leanfinder "Extension by zero commutes with derived tensor of
  equivariant Weil sheaves, normalized by the adjunction unit"`: eight hits,
  including representation Tor statements and
  `SheafOfModules.unitToPushforwardObjUnit`; none is the native open statement.
* `msearch.py ... loogle '"extensionByZero", "tensor"'`: zero hits.
* `msearch.py ... grep
  'extensionByZero.*[Tt]ensor|[Tt]ensor.*extensionByZero|jShriek'`: zero hits.
* Local source `rg` for native open tensor / extensionByZero tensor in
  `lean/WeilConjectures` returned only unrelated Deligne--Laumon realified
  kernel references. The item-id grep returned no existing statement.
* `rg` in `lean/Sheaf` found the ordinary open tensor results and the recorded
  native tensor/forgetful framework used here; no existing native open
  comparison. Searches for the new qualified helper names found no collision.

No statement correction or disputed mathematical assertion is claimed. The
module's only postponed proof is the named theorem for this DAG node. Every
helper is listed in `lean.declarations` and carries this item's source tag.
Compilation uses only scompile.py with its fixed server limits. The expanded
statement passed against the current live sources in 35.2 seconds; the older
local overlay timed out and the wrapper's live confirmation succeeded.

## Second reading by Q86

Author's second reading, not an independent worker review: this dispatcher
assignment explicitly prohibits starting other agents and assigns the
independent delivery review to the maintainer. I reread the statement and
source against the file. I found a potential ambiguity in the initially
unconstrained derived restriction comparison and repaired it by pinning each
restriction summand and its K-flat localization square; the ordinary
restriction square is pinned on forgotten inputs as well. I checked tensor
order (the upstream curried tensor takes its right parameter first), the
left-degree sign via the flipped total bifunctor, the direction of the open
inverse transpose, the direction of the pullback compositor, the ordinary
forgetting square, and all edge cases above. No source or DAG statement was
changed. The maintainer's independent review remains required by this delivery
workflow.

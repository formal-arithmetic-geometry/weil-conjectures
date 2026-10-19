## Worker report

Record the existing `CategoryTheory.Mod.rightDerivedComapIsoMapDerivedCategory` in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` (declaration at line 194
of the current source). No module is delivered. The declaration is precisely the name
specified by the current main-20261015 blueprint, order 1628; its source and docstring were
read locally and independently through `scompile.py --source` on the live server.
Only the item's `lean` record changes. There are no new nodes, dependency repairs,
statement changes, or postponed theorems in this delivery.

Hypothesis-by-hypothesis correspondence with the context of
`lem-sfb-extend-scalars-kflat`:

- The category is `{C : Type u} [Category.{v} C]`, with independent object and morphism
  universes. Its abelian structure is `[Abelian C]`.
- Tensor and additivity are `[MonoidalCategory C] [MonoidalPreadditive C]`.
- Closedness is `[MonoidalClosed C]`; the context's symmetry is `[SymmetricCategory C]`.
- The Grothendieck condition is `[IsGrothendieckAbelian.{v} C]`.
- Functorial flat resolutions in the context are `[Abelian.HasFunctorialFlatResolution C]`.
- Ring objects are `{R S : C} [MonObj R] [MonObj S]`, with their commutativity supplied by
  `[IsCommMonObj R] [IsCommMonObj S]` in the context.
- The given ring-object morphism is `(φ : R ⟶ S) [IsMonHom φ]`.

The existing declaration actually needs neither symmetry, flat resolutions nor commutativity;
these are available in the node's setting, and the server probe specializes it under exactly
the complete contextual hypotheses without adding any. The quasi-isomorphism `s` and K-flat
complexes of the context lemma are not hypotheses of this definition: the item uses its
ambient situation, not its preservation conclusion or a particular complex.

Clause-by-clause correspondence:

- Restriction of scalars is Mathlib's `Mod.comap φ : Mod C S ⥤ Mod C R`. Its `obj` leaves
  the underlying object unchanged and uses `scalarRestriction`; its `map` leaves the
  underlying arrow unchanged. Thus this is the action restricted through φ.
- Right derived restriction is `(Mod.comap φ).rightDerivedFunctor`, the total right derived
  functor of `mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`.
- Termwise restriction is `(Mod.comap φ).mapDerivedCategory`. It is induced from the same
  functor on all integer-indexed cochain complexes, using restriction's exactness.
- Both functors have domain `DerivedCategory (Mod C S)` and codomain
  `DerivedCategory (Mod C R)`. Thus the direction is precisely the node's direction.
- The canonical natural isomorphism is the returned `≅`; its body is
  `(Mod.comap φ).rightDerivedFunctorIsoMapDerivedCategory`, constructed by uniqueness of
  right derived functors with their units. Its hom satisfies
  `rightDerivedFunctorUnit ≫ whiskerLeft Qh comparison.hom =
  mapDerivedCategoryFactorsh.inv`. The probe checks this equality directly using the
  upstream `rightDerivedFunctorIsoMapDerivedCategory_hom_fac`.

Dependency declarations inspected and used:

- `lem-sfb-extend-scalars-kflat`: `CategoryTheory.Mod.preservesKFlatQuasiIso` in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`; its ambient binders
  give the context above. Its preservation result is unnecessary for this definition.
- `sk-def-sfb-change-of-scalars`: recorded module
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` supplies extension and
  coextension and imports Mathlib's `CategoryTheory.Mod.comap`. The latter is the exact
  restriction used by the comparison; no private action or restriction is introduced.
- `def-sfb-right-derived-functor`: the recorded
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` uses arbitrary
  quasi-isomorphism resolutions. This is a different choice of the same universal pair,
  rather than a different mathematical notion. The upstream `rightDerivedFunctor` uses
  monomorphic resolutions, already supplied here by
  `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` from
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- The compatibility probe imports the recorded `def-sfb-right-derived-exact` module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact` and constructs,
  for every resolution hypothesis `h`, the natural isomorphism from the recorded choice to
  the upstream choice by composing
  `rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory h` with the inverse of
  the comparison being recorded. Both comparisons are characterized by the same
  factorization unit. The definition of the recorded exact comparison and the upstream
  comparison were read in full. No extra resolution hypothesis is imposed on the item:
  another probe example obtains `h` by forgetting `Mono` from the available resolutions.
- `def-weil-abstract-derived-category`: Mathlib's `DerivedCategory`, `HasDerivedCategory`
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic` are the
  actual localization objects on both sides; no replacement derived category is used.

Edge cases checked: identity φ, zero ring object when present, and nonflat scalar changes
such as ℤ → ℤ/2 all remain allowed. Exactness of restriction uses no flatness of S over R.
There is no boundedness assumption: `ComplexShape.up ℤ` means all integer-indexed complexes.
The probe uses independent universes `u` and `v`, not an equality of category universes.
There is no nonempty-index or nonzero-object condition to exclude a degenerate case.

Searches performed (actual results):

- `msearch.py leanfinder`, query “The right derived functor of exact restriction of scalars
  for module objects is naturally isomorphic to the functor applying restriction termwise”:
  eight hits on Ext functoriality and degree-zero right-derived comparisons, no exact match.
- `msearch.py loogle`, query
  `CategoryTheory.Mod.comap, CategoryTheory.Functor.mapDerivedCategory`: zero hits.
- `msearch.py grep`, query `rightDerivedComap|rightDerivedFunctorIsoMapDerivedCategory`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` for `rightDerivedComapIsoMapDerivedCategory` found the
  exact declaration in `ModuleObjects/DerivedExtendScalars.lean` and its existing users.
  Searching the node id there found no hit. The analogous search over `lean/Sheaf` found
  existing uses in `CondensedCoefficientComplexDerivedTransport` and
  `CondensedQbarScalarBasisUnitOfSections`, and no separate definition.
- The name was searched in `dag/lean_names_upstream.json` with no hit; the current source
  and server source provide the declaration directly despite that older index.

Validation: `scratch/ExistingCompatibility.lean` is a non-delivered consumer probe compiled
only through `scompile.py`. It prints the full type, specializes the existing definition,
checks its unit normalization, constructs the bridge to the recorded universal pair, and
extracts arbitrary quasi-isomorphism resolutions from the ambient Grothendieck instance.
The initial probe needed a `noncomputable section`; this was fixed in the scratch file.
No node fault or disputed statement was found.

## Second reading by NW

I reopened the node, the upstream module, and the dependency records. The node has one
clause: a canonical isomorphism from right-derived restriction to termwise restriction.
The existing declaration has exactly that direction, source and target, and its ambient
binders are a generalization of every hypothesis in the node's context. The termwise
functor is `Mod.comap φ` mapped to the derived category, with the underlying action and
arrows unchanged. The comparison is canonical by the recorded unit characterization. No
mismatch, omitted hypothesis, extra clause, duplicate notion, or edge-case exclusion was
found, so no file or statement correction is needed.

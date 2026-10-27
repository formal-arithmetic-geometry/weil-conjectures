## Worker report

Delivered `Sheaf.AlgebraicGeometry.DerivedOrdinalStrictification`, declaring
`AlgebraicGeometry.derived_ordinal_strictification` with one `sorry` and no new definitions.
The node is unchanged outside `lean`. There is no statement correction or disputed claim.

Read the node and every statement dependency, including their complete recorded signatures
and docstrings. Source checked: `literature/stacks-project/cohomology.tex:11343–11455`,
Tag 0D6B, `cohomology-lemma-glueing-increasing-union`. The source recursion chooses the
K-injective representatives before constructing the chain maps. The node isolates this
recursion and does not require the final ambient cover. Read the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`;
this auxiliary lemma is not that unit's own statement. The node already records the source's
reversed comparison direction and incorrect finite-case uniqueness pointer; its accepted
proof and this module use the direction `QC → QI_alpha` and Tag 0D68 instead.

Clause-by-clause correspondence:

- The scheme is `X : Scheme.{u}`. The set-sized ordinal is `lambda : Ordinal.{v}` and
  its index set is `lambda.ToType : Type v`. No nonempty, countable, successor-final, or
  finiteness assumption is present, and the universe variables `u v w` are explicit.
- The open family is `W : lambda.ToType → X.Opens`. `hincreasing : Monotone W` says
  it is increasing. `hcontinuous` says `W alpha` is the indexed supremum of all earlier
  opens at every `Order.IsSuccPrelimit alpha`. This predicate means no immediate
  predecessor and includes a minimal index. Thus at index zero its earlier-index type
  is empty and the supremum is bottom, giving precisely `W_0 = ∅` when the ordinal
  is positive. A separate zero binder would only repeat this clause. The theorem has
  no `hcover` or other covering assumption on X.
- `K alpha` belongs to `DerivedCategory (SheafOfModules.{u}
  ((moduleRings X.toRingedSpace).over (W alpha)))`. These are the shared localized
  open-site module categories, canonically equivalent to modules on `(W alpha).toScheme`
  by Mathlib's `Scheme.Modules.overEquiv`. This is the same carrier and size convention
  as the parent increasing-union theorem and the local-Hom-gluing proof dependency.
  The `HasDerivedCategory.{w}` family supplies the derived-localization size convention,
  not a geometric or boundedness hypothesis. There is no unused ambient localization binder.
- `hnegative` quantifies over every alpha and every integer i with `i < 0`, and says
  `Subsingleton (K alpha ⟶ (K alpha)⟦i⟧)`. In the additive derived category this says
  exactly that the indicated Hom group is zero.
- `I` is the given family of unbounded integer-indexed complexes; `hI` says each
  `(I alpha).IsKInjective`. These are input complexes, not existential replacements.
  `e alpha : DerivedCategory.Q.obj (I alpha) ≅ K alpha` is the given identification.
- `r beta alpha h` has source the derived `overMap` restriction of `K alpha` and
  target `K beta`, for every strict pair. `hcocycle` precomposes the restriction of
  `r beta alpha hba` with `derivedModuleOpenMapCompIso.inv`, and postcomposes with
  `r gamma beta hgb`; its equality to `r gamma alpha` is exactly the given cocycle.
  The comparison simply identifies direct restriction with successive restriction.
- The existential family `f beta alpha h` consists of actual morphisms of complexes
  `I beta ⟶ (overMap ...).mapHomologicalComplex (.up ℤ) |>.obj (I alpha)`.
  The first conjunct asserts `QuasiIso` for every pair.
- The second conjunct composes `f gamma beta` with the termwise restriction of
  `f beta alpha`, then the identity-on-sections direct/iterated comparison
  `Functor.mapHomologicalComplexCompIso (moduleOpenMapCompIso ...) (.up ℤ)`.
  Equality to `f gamma alpha` is chain-map equality, not equality only after Q and
  not a homotopy condition. The comparison is necessary because Lean distinguishes
  the two categorical restriction expressions.
- The last conjunct is `Q.map f = e_beta.hom ≫ r.inv ≫ R.map e_alpha.inv ≫ factors.hom`.
  Since Lean writes composition left to right, this is the node's
  `(e_alpha|)^(-1) ∘ r^(-1) ∘ e_beta`; `mapDerivedCategoryFactors.hom` is exactly the
  canonical last identification `R(QI_alpha) ≅ Q(R_complex I_alpha)` stipulated
  in the node's last sentence. Every map and both inverse directions were checked.

Dependencies used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`;
  full structure and docstring read in `Mathlib/AlgebraicGeometry/Scheme.lean:36–48`.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `schemeDerivedCategory`, with the shared `SheafOfModules (moduleRings ...)` carrier.
  Full module read; local derived categories specialize the same abstract localization
  to the `R.over U` categories rather than introducing a private category.
- `def-pur-kinjective-complex`: its Mathlib match `CochainComplex.IsKInjective`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective:39–44`, read in full.
- `def-pc-quasi-iso-modules`: its Mathlib match `QuasiIso`,
  `Mathlib.Algebra.Homology.QuasiIso:135–147`, read in full.
- Shared restriction functors `SheafOfModules.overMap` and `overFunctor`, and the
  `overFunctorMap` comparison: `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
  Exactness and additivity come from the upstream `DerivedHomMayerVietoris` instances.
- Existing real-data definitions `moduleOpenMapCompIso` and
  `derivedModuleOpenMapCompIso`: `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion:45–77`.
  Both full definitions read. Only these comparison definitions are used; its
  `derived_basis_increasing_union` theorem is not used in this statement or proof plan.
  This helper import avoids duplicating an already existing definition, as in the
  landed BBD-descent sibling. It does not add a cyclic mathematical DAG dependency
  on the parent theorem. Maintainer import note: adding this module as a proof import
  to `DerivedBasisIncreasingUnion` would close a module-import cycle, so omit that
  automatic import under stages/2-statements.md §3(7). A later helper-module extraction
  can make the parent consume this theorem; no shared source was edited here.
- Proof imports include `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
  (`CategoryTheory.isKInjective_restrict_localized`),
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
  (`CochainComplex.IsKInjective.Qh_map_bijective`), and
  `Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue`
  (`AlgebraicGeometry.derived_basis_local_hom_glue`). Their source declarations and
  docstrings were read. The abstract derived-category dependency is already publicly
  imported through DerivedCategory. `lem-trf-derived-strict-open-colimit` has no
  recorded module or match in the read repository; it is only a proof dependency,
  so no placeholder or duplicate statement is introduced for it.

Edge cases checked against the signature and source argument: lambda zero (empty f),
lambda one (no strict pairs, continuity forces the only open empty), nonzero limit
without finite subcover, repeated opens, all opens empty, X empty, zero complexes,
and a family contained in a proper open of X. All representatives and all e's remain
arbitrary prescribed inputs. There is no boundedness hypothesis or cover of ambient X.

Searches actually run with the prescribed `msearch.py Q34 <item>` wrapper:

- LeanFinder: `Choose strictly composable chain maps between fixed K-injective complexes
  realizing derived isomorphisms on a continuous ordinal family of increasing opens`:
  8 hits (bounded derived fraction lemmas, `CochainComplex.cm5b`, injective resolution
  successors, and `isKInjective_of_injective_aux`); none states ordinal strictification.
- Loogle: `CochainComplex.IsKInjective, DerivedCategory.Q`: 0 hits.
- Mathlib grep: `strictif|rectif|transfinite` in `Algebra/Homology`: 0 hits.
- LeanSearch: `Strictification of ordinal derived descent data by chain maps between
  prescribed K-injective complexes`: 8 hits, individual K-injectivity, cm5b and fraction
  constructions; no compatible ordinal system on nested opens.
- `rg` for `strictif|ordinal.*derived|derived.*ordinal|ordinal_strict|strict_open` in
  both `lean/WeilConjectures` and `lean/Sheaf`: no exact statement; found other tower,
  descent, and strictification results, and then located the parent's comparison helpers.
- `rg`/node-id search for `lem-trf-derived-ordinal-strictification` in upstream Lean:
  no match. `rg` for the proposed declaration in Mathlib and `dag/lean_names_upstream.json`:
  no match. Helper names searched across the DAG, upstream Lean and Sheaf; only the
  existing increasing-union module owns the two comparison definitions.

Validation: prescribed scompile.py compiles sandbox and library module cleanly within
60 seconds, using two threads; final run 9.6 s and 10.2 s, no errors or warnings.
An early transient local ENOSPC was handled by the wrapper's server confirmation;
subsequent wrapper compiles worked normally. Only the theorem body is `sorry`.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

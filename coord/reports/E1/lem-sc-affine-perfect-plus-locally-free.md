## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree` states
`AlgebraicGeometry.Scheme.exists_perfect_lift_plus_finiteLocallyFree` with proof `sorry`.
No definitions or auxiliary theorems are introduced. The theorem docstring carries all four
steps of the node's proof, including the reviewed shift bookkeeping and image/kernel
identification only on U.

Hypothesis and conclusion correspondence:

- X is a scheme: `(X : Scheme.{u})`, using the recorded Mathlib scheme structure.
- X is affine: `[IsAffine X]`, Mathlib's isomorphism of X with the spectrum of its global
  sections; equivalent to being isomorphic to some affine spectrum.
- U is an open subscheme: `(U : X.Opens)` and its canonical open scheme `U.toScheme`.
- U is quasi-compact: `(hU : IsCompact (U : Set X))`. Mathlib's `IsCompact` requires the
  finite-subcover property and does not impose a Hausdorff hypothesis.
- F is an arbitrary object of D(O_U): `(F : schemeDerivedCategory U.toScheme)`. This is
  the recorded derived category of all module sheaves, not merely quasi-coherent objects.
- F is perfect: `(hF : IsPerfect U.toScheme F)`, using the recorded definition verbatim.
- The integer r: the existential `(r : ℤ)`, with no sign or size restriction.
- The module sheaf on U: existential
  `(M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))`.
- Finite local freeness: `M.IsFiniteLocallyFree`; its trivializing opens may have different
  finite ranks. The existing node `def-sc-finite-locally-free-sheaf` is added to stmt_deps
  to carry this already-landed notion. No dependency record is changed.
- The perfect object on X: `∃ P : schemeDerivedCategory X, IsPerfect X P ∧ ...`.
- M[-r]: M is embedded in degree zero using `DerivedCategory.singleFunctor ... 0`, then
  shifted with `⟦-r⟧`; this is the cohomological shift in the recorded derived category.
- Direct sum with the given F: binary biproduct `... ⊞ F`.
- Isomorphism on U with the restriction of P: `Nonempty (...obj P ≅ ... ⊞ F)`.
  The functor is `SheafOfModules.overFunctor ... U` followed by
  `Equivalence.functor (Modules.overEquiv U)` and `mapDerivedCategory`. This is the
  canonical restriction to the open scheme, in the same explicit category form used
  by the landed `AffinePseudoCoherentLift` and `QcOpenDerivedLift` modules.

All universes and variables are explicit; `autoImplicit false` is set. The four
`HasDerivedCategory.{w}` instance binders supply the chosen derived localizations for X,
its open sites, U, and U's open sites, as required by the recorded `IsPerfect` definition
and restriction functor. They impose no extra geometric property. The module uses
Mathlib's abelian structures; no new abelian or derived category is chosen inside it.
The local additive and composition instances make the exact restriction functor elaborate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and its category of
  morphisms), from `def-pc-scheme`; read the structure, full local-affine field and docstring.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  from `def-pc-derived-category`; read its signature and the associated QCoh declarations.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`,
  from `def-pc-perfect-complex`; read its full definition, `IsStrictlyPerfect` and docstrings.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, from `def-sc-finite-locally-free-sheaf`; read its
  signature and variable-rank local-generators definition and docstring.
- Restriction uses Mathlib's `Scheme.Modules.overEquiv` and
  `SheafOfModules.overFunctor` through the imports of `PerfectComplex`. The former is
  the equivalence of restricted-site O_X-modules with O_U-modules, not another pullback.

Edge cases checked before writing: U may be empty; X may be the empty affine scheme;
F may be zero; the summand may have rank zero; no nonempty or positive-rank binder is
present. The finite locally free predicate allows local ranks to vary, so disconnected
opens are not excluded. U need not be affine, and X need not be Noetherian. All integers
are allowed for the shift, including zero. No base field or characteristic restriction
is present. Universe u matches the recorded category of sheaves and permits every scheme
in that universe; w is the shared localization morphism universe.

Searches made:

- `msearch.py ... leanfinder "perfect complex on a quasi compact open of an affine scheme
  extends after adding a shifted finite locally free sheaf"`: eight hits on derived
  t-structure bounds and single complexes, no matching extension theorem.
- `msearch.py ... loogle "IsPerfect, IsFiniteLocallyFree"`: zero hits, unknown IsPerfect.
- `msearch.py ... grep "lift.*perfect|perfect.*locallyFree|IsFiniteLocallyFree"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "perfect complex extension from open affine scheme finite
  locally free summand"`: service unavailable (Internal Server Error), recorded without
  treating the outage as evidence of absence.
- `rg` over WeilConjectures for `IsFiniteLocallyFree`, the item id, and perfect lifting:
  the existing variable-rank predicate was found in `LocallyFree.lean:156`; no item theorem.
  The upstream `CategoryTheory/DerivedCategory/Perfect.lean` concerns categorical perfect
  objects and triangles, not this affine-open extension theorem.
- `rg` over Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `perfect.*(extension|summand)|lift-perfect-complex|exists_perfect_lift_plus_finiteLocallyFree`:
  only unrelated field-theoretic perfect-extension hits; no existing declaration of this
  theorem or collision with the proposed full declaration name.
- DAG and lean/Sheaf searches for finite locally free sheaves found the already-landed
  `def-sc-finite-locally-free-sheaf`. Its declaration gives exactly the needed notion;
  no new definition node or dependency module is needed.

Source fault: the node's source field says Tag 08ED (Lemma 36.13.7) with label
`lemma-lift-perfect-complex-plus-locally-free`. The label and statement actually belong to
[Stacks Tag 08EG, Lemma 36.13.6](https://stacks.math.columbia.edu/tag/08EG).
Tag 08ED is the general quasi-coherent lifting lemma. The actual statement agrees clause
by clause with 08EG; no statement correction is needed. The source field is outside this
worker's writable fields and is preserved; the module cites the correct source.
The proof follows the node's already-reviewed shift corrections rather than repeating
the source's displayed shift typo.

Validation: the statement compiled on the server in 4.1 seconds, with no warnings or
errors. The theorem is the only declaration with `sorry`. Required dry run is the final
mechanical check; its result is recorded below.

## Second reading by E1

- `X` is `(X : Scheme.{u})` with `[IsAffine X]`; verdict: matches the affine scheme.
- `U` is `(U : X.Opens)` with `hU : IsCompact (U : Set X)`; verdict: matches a quasi-compact open.
- `F` is `schemeDerivedCategory U.toScheme` with `hF : IsPerfect U.toScheme F`; verdict: matches every perfect object of `D(O_U)`.
- Witnesses are `r : ℤ`, `M` with `M.IsFiniteLocallyFree`, and perfect `P` on `X`; verdict: matches the node.
- The `Nonempty` isomorphism uses restriction, `singleFunctor M ⟦-r⟧`, and `⊞ F` in the same order.
- Edge cases checked: empty schemes or opens, zero `F`, rank-zero `M`, shift zero, disconnected opens, and arbitrary characteristic; no extra Noetherian, field, positivity, or nonemptiness hypothesis.
- Searches found no duplicate theorem. The existing finite locally free declaration was read and added to `stmt_deps`; it gives exactly `M.IsFiniteLocallyFree`.
- The source metadata cites Tag 08ED while the label and statement are Tag 08EG; this metadata discrepancy is outside permitted fields and was preserved. The Lean statement agrees with the node and Tag 08EG.
- No Lean mismatch found; compilation succeeded with only the permitted theorem `sorry`.

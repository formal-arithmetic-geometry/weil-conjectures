## Worker report

The module `Sheaf.RingTheory.PrincipalFreeAlgebraNorm` defines
`Algebra.principalFreeNorm` by the formula in the node and states its three algebraic
properties as `Algebra.principalFreeNorm_spec`. The companion
`AlgebraicGeometry.principalFreeNorm_affineOpen` states the final geometric clause.
Both theorem proofs are `sorry`; both definitions have complete data. No statement
correction, disputed statement, new node, or dependency repair was needed.

Hypotheses and clauses, read against the node:

- The commutative rings are `[CommRing R] [CommRing D]`. The specified unital map
  `ρ : R →+* D` is encoded by `[Algebra R D]`; its ring map is `algebraMap R D`.
  Every unital ring map supplies exactly this instance by `RingHom.toAlgebra`.
  The algebraic part permits independent universes `R : Type u`, `D : Type v`.
- The nonnegative rank and finite cover length are `{r m : ℕ}`. The elements are
  `f : Fin m → R`, and generating the unit ideal is precisely
  `hgen : Ideal.span (Set.range f) = ⊤`.
- `hfree` asserts a basis indexed by `Fin r` of each
  `LocalizedModule.Away (f i) D` over `Localization.Away (f i)`. Its existential
  `True` presentation is the existing characteristic-polynomial interface; no
  global basis or choice of local bases is assumed.
- Multiplication `μ_u` is `LinearMap.mul R D u`. The polynomial `χ_u` is the
  existing `Algebra.locallyFreeCharpoly f hgen hfree (LinearMap.mul R D u)`.
  `principalFreeNorm` is literally `(-1) ^ r * χ_u.eval 0`.
- For every `a : R`, every finite cardinal `k : ℕ`, every basis `e` indexed by
  `Fin k` of `D_a`, and every `u : D`, the first conjunct of
  `principalFreeNorm_spec` states the equality after `algebraMap R (Localization.Away a)`
  with `Matrix.det (LinearMap.toMatrix e e (localizedMul a u))`. Any finite basis
  can be reindexed by `Fin k`; there is no requirement that `k = r` at zero
  localizations. `localizedMul` is conjugation of scalar-extended multiplication
  through `(LocalizedModule.isBaseChange (Submonoid.powers a) D).equiv`, the
  canonical map sending a pure tensor to the scalar times `d/1`. It is therefore
  multiplication by `u/1`, not a chosen endomorphism or extra hypothesis.
- The second conjunct quantifies over every function `N : D → R` satisfying
  precisely that same local formula and concludes `N = principalFreeNorm f hgen hfree`.
  Together with the first conjunct this states existence and uniqueness. This
  characterization does not mention the cover, so it also gives independence
  of any other generating cover. Bases are universally quantified, and the
  construction itself only takes proofs of existence of local bases.
- The third conjunct quantifies over every commutative `S : Type (max u w)` and
  every `[Algebra R S]`, a `Fin r` basis `e` of `S ⊗[R] D`, and `u : D`.
  It identifies the image of the norm with the determinant of
  `(LinearMap.mul R D u).baseChange S` in `e`. This is the recorded base-change
  convention, with tensor factors swapped relative to the printed node.
  The universe includes the base ring's universe and can be enlarged arbitrarily;
  it does not make scalar-extension tests vacuous in a small independent universe.
- The geometric theorem uses the actual `Spec.map (CommRingCat.ofHom (algebraMap R D))`
  and the actual `Scheme.Modules.pushforward` of
  `SheafOfModules.unit (Spec (CommRingCat.of D)).ringCatSheaf`.
  `_hqc` is exactly that object's `IsQuasicoherent` predicate, with no finite-type
  or coherence hypothesis substituted for it. `V` ranges over all affine opens
  of `Spec R`. `e` is any finite basis of the direct-image sections at `V` over
  `Γ(Spec R,V)`; thus existence of such a basis is exactly the stated conditional
  freeness requirement. Schemes and their morphisms use the standard common
  universe `Scheme.{u}`; both ring types can always be placed in a common universe.
- The left side of the geometric equality is the inverse `Scheme.ΓSpecIso`
  followed by restriction from the top open to `V`, applied to the norm. The
  right side is the determinant of the matrix whose `(i,j)` entry is `e.repr`
  applied to the product of the restriction of `u` and `e j`. Restriction of `u`
  is likewise the inverse `ΓSpecIso` followed by restriction to `p ⁻¹ᵁ V`.
  These are exactly the ordinary restrictions in the node, without an arbitrary
  comparison map. The explicit `@id` only exposes the definitionally identical
  structure-sheaf carrier of a section of the structure module, so multiplication
  elaborates with its actual commutative-ring instance.

Dependency declarations read and used:

- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away`, the
  canonical ring map, and `Localization.existsUnique_algebraMap_eq_of_span_eq_top`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away` and
  `LocalizedModule.mkLinearMap`; `Mathlib.RingTheory.Localization.BaseChange`:
  `LocalizedModule.isBaseChange` and `IsLocalizedModule.isBaseChange`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`;
  `Mathlib.LinearAlgebra.Basis.Defs`: `Module.Basis`.
- `WeilConjectures.Algebra.CharpolyLocallyFree`:
  `Algebra.charpoly_locallyFree_exists_unique`. The already landed definition node
  `def-weil-pbc-charpoly-locally-free` is added to `stmt_deps`, and its existing
  module `Sheaf.Algebra.LocallyFreeCharpoly` supplies `Algebra.locallyFreeCharpoly`
  and `Algebra.locallyFreeCharpoly_spec`. No duplicate characteristic polynomial
  is defined. This is the authorized addition of an already landed notion.
- `Mathlib.LinearAlgebra.Determinant`: `LinearMap.det` and its basis-matrix
  description; `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`;
  `Mathlib.LinearAlgebra.Charpoly.BaseChange`: the free base-change formula;
  `Mathlib.LinearAlgebra.InvariantBasisNumber`: the commutative nontrivial-ring instance.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.ΓSpecIso`;
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.pushforward`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `SheafOfModules.IsQuasicoherent` predicate as recorded by `pqf-def-coherent`.
- The proof imports retain
  `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections` and its
  `Scheme.Modules.exists_tensorPullback_affine_sections`, and
  `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction` and its unit-compatible
  restriction comparison. The docstring spells out their application to the
  affine-open formula.

Edge cases checked before writing: no `Nontrivial` hypothesis occurs. If `R` is
zero, unitality forces `D` zero and all equalities lie in singleton rings. An
empty cover is permitted by `Fin 0`; its span condition forces `R` zero. Rank
zero gives polynomial `1`, norm `1`, and empty determinant `1`. Local bases may
have any finite cardinal, even where the localized ring is zero. The empty affine
open is allowed and has zero section ring. No injectivity, positive rank,
nonempty cover, global freeness, or freeness of the preimage as an affine scheme
is assumed.

Searches performed with `msearch.py` (the sandbox `searches.jsonl` retains the
returned records):

- LeanFinder: “determinant norm of a finite locally free algebra from
  characteristic polynomial with arbitrary scalar extension”: eight hits,
  including `Algebra.norm`, `Algebra.norm_apply`, `Algebra.norm_eq_matrix_det`,
  discriminants, and restriction-of-scalars formulas. None constructs the
  locally free norm without a global basis.
- Loogle: `"norm", "charpoly"`: zero hits.
- Mathlib grep: `norm.*charpoly|charpoly.*norm`: one hit in
  `Mathlib/RingTheory/Norm/Basic.lean`, for a power basis.
- LeanSearch: “determinant norm of a finite locally free algebra constructed
  from the signed constant coefficient of its characteristic polynomial”:
  eight hits, including the matrix and free-linear-map signed constant-coefficient
  formulas and `Algebra.norm_apply`, but no locally free construction.
- Direct `rg` in both project roots for `determinantNorm`, `locallyFreeCharpoly`,
  `norm.*charpoly|charpoly.*norm` located the existing characteristic polynomial
  and unrelated analytic norm estimates, with no statement matching the item.
  The prescribed id search in `WeilConjectures` had no hit. Searches for the new
  declaration names in both roots, Mathlib and `dag/lean_names_upstream.json`
  had no hit. The Mathlib source explicitly documents that `LinearMap.det`
  defaults to `1` without a finite global basis, so `Algebra.norm` cannot serve
  as this node's construction in general.

The source read was `exercises.tex`, exercises `exercise-trace-det` and
`exercise-trace-det-rings` (Tags 02DU, 02DV), and `more-algebra.tex`,
`lemma-characterize-henselian-pair` (Tag 09XI), the characteristic-polynomial
gluing paragraph. The module docstrings retain all six proof steps: construction,
signed determinant calculation, finite-basis rank comparison, localization and
uniqueness, affine-open transport, and zero/empty cases.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

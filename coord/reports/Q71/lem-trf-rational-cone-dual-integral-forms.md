## Worker report

The module `lean/Sheaf/TraceFormula/RationalConeDualIntegralForms.lean` states
`rationalConeDualIntegralForms` for a finite free abelian group `L`, a finite family
`v : Fin m → L` (including `m = 0`), and the rational cone in the canonical scalar
extension presentation `V := ℚ ⊗[ℤ] L`, which is identified with the source's
`L ⊗[ℤ] ℚ` by the tensor symmetry.  The theorem has a `sorry` proof as required
for stage 2.

The hypotheses and conclusions render the node as follows.  The typeclass binders
`[AddCommGroup L] [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L]` say that
`L` is a finite free abelian group.  The binder `m : ℕ` and `v : Fin m → L`
represent the vectors, with `Fin 0` giving the empty family.  The `let V` line is
the rational vector space, and `C` is the set of finite nonnegative rational
combinations, using `q : Fin m → ℚ≥0` and `TensorProduct.tmul`.  The first
implication hypothesis `C ∩ (-C) = ({0} : Set V)` is pointedness.  The second,
`∀ x : V, ∃ c₁ ∈ C, ∃ c₂ ∈ C, x = c₁ - c₂`, is the stated reproducing/spanning
condition.

The conclusion supplies `r : ℕ`, integral additive homomorphisms
`φ : Fin r → L →+ ℤ`, and their rational linear extensions
`Φ : Fin r → V →ₗ[ℚ] ℚ`.  The displayed equation on
`TensorProduct.tmul ℤ (1 : ℚ) ℓ` says that each `Φ i` extends the corresponding
integral form.  `Submodule.span ℚ (Set.range Φ) = ⊤` says the extensions span the
full rational dual.  The equality
`C = {x | ∀ i, 0 ≤ Φ i x}` is the defining-inequality clause.  The final two
conjuncts encode the edge cases: if every vector of `V` is zero then `r = 0`,
and if some vector is nonzero then `0 < r`.

No statement dependency is needed to type this theorem.  The DAG's proof-only
node `lem-trf-rational-cone-dual-finite` is not imported because stage 2 states
this node without proving it.

I checked the edge cases `m = 0`, `L = 0` (hence `V` is zero and the empty family),
and a nonzero rank-one lattice (which forces a nonempty family).  The pointedness
condition excludes a full line, while the reproducing condition permits the cone
to be all of `V` when pointedness is separately satisfied (for example the zero
space).  The tensor presentation uses `ℚ ⊗[ℤ] L`, whose canonical commutativity
isomorphism is the source's `L ⊗[ℤ] ℚ`; this orientation is required by Mathlib's
available `Module ℚ` instance and does not change the mathematical object.

Searches made:

- `msearch.py ... leanfinder "finite free abelian lattice pointed rational cone integral linear forms span dual"`: eight unrelated hits (Z-lattice and span APIs); no exact declaration.
- `msearch.py ... loogle "TensorProduct, Module.Free, Module.Finite, Submodule.span, LinearMap"`: zero hits.
- `msearch.py ... grep "dual.*cone|cone.*dual|rational.*polyhedral" Mathlib/Geometry/Convex/Cone`: zero direct matches from the search wrapper; direct inspection found only the general `PointedCone.DualFG` API in `Mathlib/Geometry/Convex/Cone/DualFinite.lean`.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for rational-cone, dual-integral, and Minkowski forms: the existing `Sheaf.Paper.GordanRationalCone.gordan_rational_cone_finite` concerns lattice-point generation and is not this integral dual-form statement; no exact declaration exists.

The module compiles cleanly with `scompile.py`; the only expected warning is the
`sorry` proof warning.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

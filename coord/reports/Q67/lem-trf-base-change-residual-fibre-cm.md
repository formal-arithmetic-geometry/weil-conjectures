## Worker report

Item: `lem-trf-base-change-residual-fibre-cm` (Q67, stage 2).
Module: `Sheaf.AlgebraicGeometry.BaseChangeResidualFibreCM`.
Declaration: `AlgebraicGeometry.baseChange_residualFibre_cohenMacaulay`.

The delivery states the full node as one theorem with `sorry`. It introduces no
new definition, changes no statement or dependency, and proves nothing. The
canonical constructions are specified by their defining projection equations,
rather than by an uncharacterized isomorphism. Their witnesses can therefore be
used directly at stage 3. All variables and the universe are explicitly bound;
`autoImplicit` is disabled.

Sources read: `literature/stacks-project/divisors.tex`,
`lemma-base-change-relative-assassin` (Tag 05DC), especially the second proof
paragraph; `literature/stacks-project/algebra.tex`, `lemma-tensor-fields-CM`
(Tag 045M). The first explicitly identifies the residual fibre with the spectrum
of the tensor product. The second requires finite generation of just one field
extension and makes no separability assumption. The signatures and docstrings of
the recorded statement dependencies were read in the project/Mathlib sources.
The example CompactObject module is now withdrawn; its node binds an existing
Mathlib declaration. The delivered module follows the current module-mode rules.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| Schemes and a locally finite type morphism `f : X → S` | `{X S S' : Scheme.{u}}`, `(f : X ⟶ S)`, `[LocallyOfFiniteType f]` |
| Arbitrary base morphism `g : S' → S` | `(g : S' ⟶ S)` with no additional property |
| `X' = X ×_S S'`, with `g'` and `f'` | `pullback f g`, `pullback.fst f g`, `pullback.snd f g` |
| Fix `r'`, put `r = g(r')`, and fix `z` with `f(z) = r` | `(r' : S') (z : X) (hz : f z = g r')` |
| `k = κ(r)`, `k' = κ(r')`, and `κ_X(z)` | `S.residueField (g r')`, `S'.residueField r'`, `X.residueField z` |
| Field extensions through the canonical residue-field maps | The two `Algebra` instances, fixed by `hk'` and `hkz`; the latter uses `(S.residueFieldCongr hz).inv ≫ f.residueFieldMap z` |
| `Y = X_r`, `Y' = X'_{r'}` | `f.fiber (g r')`, `(pullback.snd f g).fiber r'` |
| Canonical `bar z` in `Y` | The witness `y` with `hy : f.fiberι (g r') y = z`; the fibre homeomorphism makes this point unique |
| Canonical residue-field isomorphism over `k` | `e : X.residueField z ≅ (f.fiber (g r')).residueField y`, with `e.hom` equal to the fibre projection's residue-field map transported along `hy`; the next equality identifies its composite from `k` with the map induced by `Y → Spec k` |
| Finite generation as a field, including nonclosed `z` | `(⊤ : IntermediateField (S.residueField (g r')) (X.residueField z)).FG` |
| `T = k' ⊗_k κ_X(z)`, with the specified multiplication | `TensorProduct (S.residueField (g r')) (S'.residueField r') (X.residueField z)`, using `Algebra.TensorProduct.instCommRing`; its `tmul_mul_tmul` is exactly `(a⊗b)(c⊗d)=ac⊗bd` |
| Canonical morphism `h : Y' → Y` | The witness `h`, whose two following equations prescribe its composites to `X` and `Spec k`; uniqueness is the universal property of `Y` |
| Canonical residual-fibre isomorphism | `E : h.fiber y ≅ Spec (CommRingCat.of T)`; `h.fiber y` is literally the pullback of `h` along `Y.fromSpecResidueField y` |
| The same isomorphism retains both field projections | The two equations on `E.inv` prescribe its composites to `Spec κ_Y(y)` and `Spec k'` by `e.inv ≫ includeRight` and `includeLeftRingHom`, respectively |
| Every point `z'` over `z,r'` | `∀ (z' : ↑(pullback f g)) (hx : pullback.fst f g z' = z) (hr : pullback.snd f g z' = r'), ...` |
| Canonical tensor map to `κ_X'(z')` | `∃ ψ : T →+* (pullback f g).residueField z'`, with its value on every `a ⊗ₜ b` equal to the product of the two residue-field images, transported along `hr` and `hx` |
| Point correspondence for that same `E` | `∃ w : h.fiber y`, with its image in `X'` equal to `z'`, and `(E.hom w).asIdeal = RingHom.ker ψ` |
| `T` Noetherian | `IsNoetherianRing T` |
| Every prime localization Noetherian local with depth equal to dimension | `∀ (q : Ideal T) [q.IsPrime], IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalRing (Localization.AtPrime q) ∧ ...`; the final equality uses `IsLocalRing.depth` coerced to `WithBot ℕ∞` and `ringKrullDim` |

The algebra binders do not impose an extra mathematical hypothesis: each is the
canonical field-extension structure from the node, encoded by an instance plus
an equality fixing its algebra map. Both always exist by `RingHom.toAlgebra`.
No arbitrary coefficient homomorphism is assumed. Similarly, `y`, `e`, `h`, `E`
and `ψ` are conclusions with characterizing equations, not extra assumptions.
The reverse orientation of `e` relative to the prose is immaterial because it is
an isomorphism and its actual forward map is fixed to the residue-field map of
the fibre projection. The equation involving `E.inv` uses `e.inv` in the required
contravariant direction.

For the point clause, the composite `h.fiber y → Y' → X'` is injective on points
(both maps are fibre projections). Thus `w` is the canonical point over `z'`, not
a freely chosen alternative. Pure tensors generate the tensor ring, so the
formula determines `ψ` uniquely. Existence of both `ψ` and `w` is asserted; the
point clause cannot become vacuous through an assumed tensor map. `E` is chosen
before the universal quantifier on `z'`, so all points refer to the same scheme
isomorphism. Its two projections determine it: the base-changed fibre square is
cartesian, and the residual fibre is another pullback.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (public through Fiber).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  base-change convention uses the existing `pullback`, `pullback.fst`, and
  `pullback.snd` of `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  No module-sheaf or geometric-fibre part of that convention is needed here.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`, and
  `Scheme.fromSpecResidueField` (public through Fiber).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, and
  `fiberToSpecResidueField`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `algebraMap`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; its commutative
  algebra multiplication and the two canonical inclusions come from
  `Mathlib.RingTheory.TensorProduct.Basic`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` (through Fiber).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- The recorded proof modules `Sheaf.AlgebraicGeometry.FibreStalkQuotient`,
  `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`, and
  `Sheaf.RingTheory.TensorFieldsCohenMacaulay` are imported privately. In
  particular the last already supplies
  `Algebra.TensorProduct.isNoetherianRing_and_local_depth_eq_dimension_of_fg`.
  The remaining Mathlib proof ingredients (affine stalks, residue fields at
  primes, tensor pushouts, affine pullbacks and fibre base change) are available
  through the listed private imports or the public fibre API.

Edge cases checked before writing:

- Empty schemes: point binders have no inhabitants; no nonemptiness assumption
  is added to either scheme.
- A nonclosed generic point of the affine line: `κ(z)=k(t)` is finitely generated
  as a field but not as a `k`-algebra. The statement uses `IntermediateField.FG`,
  not `Algebra.FiniteType`, and imposes no closed-point condition.
- Identity base change and degree-zero/transcendence-degree-zero extensions:
  the canonical maps specialize to the usual fibre and residue-field maps.
- Arbitrary inseparable extensions: the tensor ring may have nilpotents, and
  neither reducedness nor separability occurs among the assumptions.
- `k=ℚ`, `k'=κ(z)=ℚ(i)`: the two-prime tensor product tests the canonicality
  requirement. Twisting `e` by conjugation violates its explicit map equation;
  the same `E` must satisfy both projections and the kernel formula for all `z'`.
- Prime localizations are nonzero local rings, so the depth coercion to the
  dimension's `WithBot ℕ∞` correctly retains the extended-value convention.

Searches for an existing full statement:

- `msearch.py ... leanfinder "Residual fibre of a scheme base change is the
  spectrum of the tensor product of the residue fields and is Noetherian Cohen
  Macaulay"`: 8 hits, including `Scheme.Hom.fiberOverSpecResidueField`,
  `fiberToSpecResidueField`, `Scheme.Pullback.ofPointTensor`, and the Triplet
  tensor projections/pullback statements. These are ingredients; none states
  the finite-generation and Cohen–Macaulay conclusions together with the
  specified residual-fibre isomorphism and point formula.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.fiber, TensorProduct"`:
  0 hits.
- `msearch.py ... grep "Cohen.?Macaulay|residueField.*FG|residualFibre"`:
  4 hits, two each in `Algebra/Module/SpanRankOperations.lean` and
  `RingTheory/AdicCompletion/LocalRing.lean`; no full statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, using residual-fibre,
  Cohen–Macaulay and residue-field-FG patterns: the field tensor theorem is
  already supplied by the recorded proof dependency. The relative-assassin
  theorem uses the same argument in its proof docstring but states a different
  result. The finite-inseparable-reduction module contains a private field-FG
  ingredient, not this theorem. No duplicate statement was found.
- `grep -rn "lem-trf-base-change-residual-fibre-cm" lean/WeilConjectures`:
  no matches. The proposed full declaration name also has no upstream or
  project match.

Validation: prescribed `scompile.py` passed for both its sandbox probe and the
actual library module (2.4 s and 2.5 s), with no errors or unexpected warnings.
The only postponed proof is the named theorem above. No node fault or disputed
statement was found. Delivery dry-run and delivery results follow the wrapper's
preflight and compilation checks.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

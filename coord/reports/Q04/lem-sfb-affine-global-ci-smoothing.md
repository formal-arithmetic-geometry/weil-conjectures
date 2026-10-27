## Worker report

The module `Sheaf.RingTheory.AffineCompleteIntersectionSmoothing` states
`MvPolynomial.AffineCISmoothing.exists_smoothing`, with its proof `sorry`.
It also gives real, explicit constructions `equation`, `Quotient`, `ClosedFiber`,
`closedCoordinate`, `genericMap` and `structureMap`, all belonging to the displayed
polynomial construction in this node. None contains postponed data or a proof.
The item JSON is changed only in `lean`; no new notion, dependency repair, or
statement correction is needed.

Source read: `literature/stacks-project/examples-defos.tex`,
`lemma-smoothing-affine-lci` (Tag 0E7V), including its displayed equations,
flatness proof, and the final coefficient-choice exercise. The expected dimension
clause is the same construction's property used in Tag 0E7X, as recorded in the node.
The theorem docstring carries the complete ten-step proof plan of the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `k` is `(k : Type u) [Field k]`; `u` is explicit, with no characteristic,
  algebraic-closure, perfection, or cardinality assumption on `k`.
- The integers `0 ≤ c ≤ N` are `(N c : ℕ) (hc : c ≤ N)`. Nonnegativity is built into
  `ℕ`. The expected dimension `r` is written directly as `N - c`; `hc` ensures
  this natural subtraction is the specified integer subtraction.
- The specified equations are `f : Fin c → MvPolynomial (Fin N) k`.
  `P` is exactly `MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f)`.
- `P ≠ 0` is its `Nontrivial` instance. The hypothesis `hdim` says its prime
  spectrum has `topologicalKrullDim = ((N-c : ℕ) : WithBot ℕ∞)`.
  These are the given presentation's complete-intersection conditions, not an
  additional unrelated complete-intersection presentation.
- `R = k[[t]]` is `PowerSeries k`, and `t` is `PowerSeries.X`.
  The one-variable convention is exactly the specialization of recorded
  `MvPowerSeries`: Mathlib defines `PowerSeries k := MvPowerSeries Unit k`.
  `K = R[1/t]` is `Localization.Away (PowerSeries.X : PowerSeries k)`.
- `∃ a : Fin (N + 1) → Fin c → PowerSeries k` is the coefficient tuple.
  Row `0` indexes `a_{0j}`; row `i.succ` indexes the variable `x_i` in the
  zero-based `Fin N` variable indexing. Membership in `tR` is the first conjunct,
  `a i j ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))`.
- `equation f a j` is literally the coefficient lift
  `MvPolynomial.map (PowerSeries.C (R := k)) (f j)` plus
  `MvPolynomial.C (a 0 j)` plus
  `∑ i : Fin N, MvPolynomial.C (a i.succ j) * MvPolynomial.X i`.
  `Quotient f a` is the polynomial ring over `R` modulo the span of these equations.
- Flatness of the specified structure map is
  `(algebraMap (PowerSeries k) (Quotient f a)).Flat`, using `RingHom.Flat`.
- `ClosedFiber f a` is exactly `Q / Ideal.span {algebraMap R Q t}`.
  The existential `e : ClosedFiber f a ≃ₐ[k] P` gives an isomorphism of the
  induced `k`-algebras. The following condition for every `i : Fin N` says that
  `e` sends the class of `x_i` under the two quotient maps to its class in `P`.
  The algebra equivalence already fixes scalars. Thus this is the specific
  coordinate-induced isomorphism, not an unspecified isomorphism of rings.
  These coordinate images and the scalar images determine the map uniquely.
- `genericMap f a` is the actual localization of `algebraMap R Q`, constructed
  by `IsLocalization.Away.map`, with domain `R[1/t]` and codomain `Q[1/t]`.
  `Smooth (Spec.map (CommRingCat.ofHom (genericMap f a)))` is precisely the
  specified generic-fibre scheme morphism's smoothness.
- `structureMap f a` is `Spec.map` of the specified structure homomorphism.
  For each `y : Spec (.of (PowerSeries k))`, the geometric point used is
  `Spec.map` of `κ(y) → AlgebraicClosure (κ(y))`, followed by the recorded
  `fromSpecResidueField y`. The scheme `pullback (structureMap f a)` along
  this point is the geometric fibre, as in `def-weil-geometric-fibre`.
  `Scheme.IsPureDimension ... (N-c)` states the last clause. It is also imposed
  on empty fibres, where the recorded definition is vacuously true; hence this
  is exactly the node's assertion about every nonempty geometric fibre.
  Choosing Mathlib's algebraic closure is permitted by the definition's
  independence of the chosen closure. All rings, spectra, residue fields and
  algebraic closures here live in universe `u`; there is no independently
  smaller testing universe or restriction on coefficient fields.
- Both equations and coefficient families allow `c=0`. There is no `Nonempty`
  assumption on the equation index type and no positivity assumption on `N`.

Dependency declarations used, with source signatures and docstrings read:

| Node | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` |
| def-weil-pbc-mv-polynomial-ring | `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; coefficient map `MvPolynomial.map` in `Mathlib.Algebra.MvPolynomial.Eval` |
| def-weil-pbc-complete-intersection-over-field | `WeilConjectures.RingTheory.CompleteIntersectionOverField`, `Algebra.IsGlobalCompleteIntersection`: its defining presentation, nonzero and dimension conditions are the hypotheses here |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`; `Mathlib.RingTheory.PowerSeries.Basic`, `PowerSeries`, `PowerSeries.C`, `PowerSeries.X` |
| def-weil-pbc-flat-ring-map | `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` |
| def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`; `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.fromSpecResidueField`; `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `AlgebraicClosure` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension` |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map` |
| def-weil-ring-localization-away | `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`; the canonical induced map is `IsLocalization.Away.map` in `Mathlib.RingTheory.Localization.Away.Basic` |

Every already-stated proof dependency is imported privately using its recorded
module or Mathlib match's file. The sole unstated proof dependency,
`lem-sfb-generic-linear-perturbation-jacobian`, has no Lean record and therefore
has no import yet. Its statement is not needed to type this theorem.
No proof dependency is used as a hypothesis of the theorem.

Edge cases checked mathematically before writing and in the final reading:

- `N=c=0`: `P=k`, both equation and coefficient families are empty, `Q=k[[t]]`,
  the special-fibre map is the `k`-identification, and both geometric fibres have
  pure dimension zero. The coordinate condition is empty but the `k`-algebra
  condition still determines the special-fibre map.
- `c=0` with arbitrary `N`: the construction is affine space over `R`, and the
  required dimensions are `N`. No coefficients are demanded.
- `c=N>0`: zero-dimensional complete intersections are included.
- Repeated equations producing a larger-than-expected dimension are excluded
  exactly by `hdim`; the quotient by the unit ideal is excluded exactly by
  `Nontrivial`. No stronger regular-sequence hypothesis was added.
- Imperfect and finite fields, including characteristic two and equations with
  zero derivatives before perturbation, are included. The source's monomial
  coefficient-choice argument does not require an infinite base field.
- Empty geometric fibres have no components, making the last assertion
  vacuous as specified by `Scheme.IsPureDimension`.

Searches for an existing statement:

- `msearch.py ... leanfinder "A global complete intersection over a field admits
  a flat smoothing over formal power series by linear perturbations with smooth
  generic fibre and pure dimensional geometric fibres"`: eight hits, all
  concerning standard smooth algebras, their relative dimensions or flatness
  of already-smooth algebras. No construction of such a smoothing.
- `msearch.py ... loogle "PowerSeries, Algebra.Smooth"`: `OK 0 hit(s)`.
- `msearch.py ... grep "smoothing|Smoothing|perturbation|Perturbation" RingTheory`:
  `OK 0 hit(s)`.
- `rg -n 'smoothing|Smoothing|linearPerturb|LinearPerturb' lean/WeilConjectures
  lean/Sheaf`: unrelated Popescu/radicial smoothing and this item's consumer
  `Sheaf.RingTheory.LCILocalFittingSmoothing`; no affine-CI polynomial smoothing.
- `rg -n 'lem-sfb-affine-global-ci-smoothing' lean/WeilConjectures`: no match.
- `rg -n 'GenericLinear|generic_linear|affine_global_ci|AffineCISmoothing|AffineCompleteIntersectionSmoothing'
  lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`: no match before
  writing this module. Helper constructions are explicit terms of this node's
  construction, not alternative definitions of any existing general notion.

No disputed statement or node fault was found. The initial server compilation
of the entire module passed in sandbox and library mode. All compiles use the
prescribed `scompile.py` wrapper, with no local/global build and no repository
write. Final direct-import compile and delivery preflight are recorded below.

## Second reading by Q04

This is the dispatcher's worker's final rereading; no other agent was started,
as explicitly required by the brief. The maintainer supplies the independent
review. I reopened the node, source statement and completed Lean file and matched
every hypothesis and conclusion in the list above. I checked particularly the
constant row versus variable rows, the orientation of the special-fibre
isomorphism, both quotient maps in `closedCoordinate`, the canonical localization
map's direction under `Spec`, and the residue-field geometric point used in the
pullback. The draft had a missing pair of parentheses around the residue-field
argument of `algebraMap`; it was repaired before the first successful compile.
No mathematical mismatch or statement correction was needed. All helper data
are actual expressions, every variable/universe is explicitly bound, and the
only theorem has exactly a `sorry` proof.

Validation: final `scompile.py Q04 lem-sfb-affine-global-ci-smoothing` passed the
sandbox compile (5.3 s) and library-module compile (5.0 s), without errors or
unexpected warnings. The dry run `deliver2.py ... --no-push` printed
`OK (dry run): commit f79706f035c passes the preflight and compiles; nothing pushed`.
A local JSON comparison confirmed the only changed node key is `lean`, its stored
signature matches the file verbatim, all Lean lines have at most 100 characters,
and there is exactly one postponed theorem proof.

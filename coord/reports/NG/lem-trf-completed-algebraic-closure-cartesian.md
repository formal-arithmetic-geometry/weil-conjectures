## Worker report

Item: `lem-trf-completed-algebraic-closure-cartesian`.
Module: `Sheaf.FieldTheory.CompletedAlgebraicClosureCartesian`.
Declaration: `completedAlgebraicClosure_cartesian`.
Stage 2 only: its sole proof is `sorry`. No definitions, auxiliary theorems,
new nodes, dependency repairs, or statement corrections are introduced.

The theorem uses an arbitrary chosen algebraic closure `L` and its actual metric
completion `UniformSpace.Completion L`, with Mathlib's canonical ring operations,
norm, scalar action, and algebra map. In particular the completion is not replaced
by an arbitrary algebraically closed extension. Giving `L` a `NormedField` and
`NormedAlgebra K L` structure is an equivalent interface for the prescribed
spectral absolute value: `NormedAlgebra.norm_eq_spectralNorm K` says precisely
`‖x‖ = spectralNorm K L x` under the theorem's hypotheses. Conversely
`spectralNorm.normedField K L` and `spectralNorm.normedAlgebra K L` give these
structures on any chosen algebraic closure. These are Mathlib's structures,
not new constructions or assumptions of a special valuation.

Hypothesis and clause correspondence:

- Field with a nontrivial multiplicative real absolute value:
  `(K : Type u) [NontriviallyNormedField K]`. Its inherited `Field` and norm
  supply multiplicativity and definiteness. Nontriviality is equivalent to the
  stated nonzero element with absolute value different from one (taking an
  inverse when its value lies strictly between zero and one).
- Nonarchimedean: `[IsUltrametricDist K]`.
- Complete for the norm metric: `[CompleteSpace K]`.
- Stable: `(hK : IsStableNonarchimedeanField K)`, using the recorded definition
  verbatim, including its minimal-polynomial spectral norm.
- Chosen algebraic closure: `(L : Type v) ... [IsAlgClosure K L]`; its scalar
  homomorphism is the one in `[NormedAlgebra K L]`.
- The spectral absolute value on that closure: the normed-algebra interface
  described above; no extra separability, characteristic, or completeness of L.
- Metric completion with the extending absolute value:
  `UniformSpace.Completion L`, whose canonical norm restricts to that on L
  by `UniformSpace.Completion.norm_coe`. Its field structure is supplied by
  Mathlib's completion instance and `NormedField.instCompletableTopField`.
- Algebraically closed: `IsAlgClosed (UniformSpace.Completion L)`.
- Complete: `CompleteSpace (UniformSpace.Completion L)`.
- Nonarchimedean extending absolute value:
  `IsUltrametricDist (UniformSpace.Completion L)`; multiplicativity is part of
  the canonical `NormedField` instance already used in the signature.
- Extending K isometrically:
  `Isometry (algebraMap K (UniformSpace.Completion L))`. By
  `UniformSpace.Completion.algebraMap_def` this is the prescribed composite
  K -> L -> Completion L, not a newly chosen embedding. It is a ring map by
  construction and injective because it is an isometry.
- Every finite-dimensional K-linear subspace:
  `∀ (V : Submodule K (UniformSpace.Completion L)) [FiniteDimensional K V], ...`.
- A K-basis of that subspace, with precisely its dimension as index cardinality:
  `∃ b : Module.Basis (Fin (Module.finrank K V)) K V, ...`.
- For every coefficient family:
  `∀ a : Fin (Module.finrank K V) → K, ...`.
- Exact orthogonality for the restricted norm:
  `‖∑ i, a i • b i‖₊ = Finset.univ.sup (fun i ↦ ‖a i‖₊ * ‖b i‖₊)`.
  Submodule norms are the restricted ambient norms. Equality in `ℝ≥0` is
  equivalent to the real-valued equality in the node, by coercion to `ℝ`.
- Zero subspace: its finrank is zero, the index is `Fin 0`, and the existential
  basis is empty. Both the sum and the `ℝ≥0` finite supremum are zero. The use
  of `Finset.sup` avoids an empty supremum in `ℝ`.
- No spherical completeness or valuation discreteness appears anywhere.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`;
  its class signature/docstring were read, and its structure is inherited here.
- `def-trf-stable-nonarchimedean-field`: public import
  `Sheaf.FieldTheory.StableNonarchimedeanField`, declaration
  `IsStableNonarchimedeanField`; full definition and source docstring read.
  It tests finite extensions in the base universe, which loses none because a
  finite extension has a model there. Our arbitrary closure universe `v` is
  independent of `u`; there is no equality restriction on universes.
- `def-weil-algebraic-closure`: public import
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`; read `AlgebraicClosure`
  there and the complete signatures/docstrings of `IsAlgClosed` and
  `IsAlgClosure` in `Mathlib.FieldTheory.IsAlgClosed.Basic`. We use the latter
  two to allow any chosen closure, as that dependency explicitly provides.

Available proof inputs are imported with ordinary visibility:
`Mathlib.Analysis.Normed.Field.Approximation` (monic approximation and root
proximity), `Mathlib.Topology.Algebra.Module.FiniteDimension` (closedness), and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` (finite algebraic
adjoin). Spectral norm, completion, and splitting material are already reached
by the public imports. The two canonical completion modules are public because
the completion's algebra/field structures occur in the statement. The nodes
`lem-trf-cartesian-subspace` and
`lem-trf-finite-ultrametric-almost-orthogonal-basis` have neither a Lean record
nor a Mathlib match in the read repository; they are proof dependencies only,
so there is no module to import yet. No statement depends on their missing
interfaces. The docstring records all eight DAG proof steps and their inputs.

Edge cases checked before writing:

- `V = 0`: empty `Fin 0` basis; finite sum and NNReal maximum both zero.
- Zero coefficient family for positive dimension: both sides zero.
- Dimension one: the assertion is multiplicative scalar norm compatibility.
- K already algebraically closed: L may equal K and completion adds no points;
  the conclusion still includes every finite-dimensional subspace.
- Arbitrary characteristic and inseparable polynomials: no `CharZero` or
  separability hypothesis; the root approximation proof in the node works
  in positive characteristic as well.
- Complete stable fields with nondiscrete value group and without spherical
  completeness remain allowed.
- Different universes for K and L remain allowed.

Searches performed (2026-10-24 UTC):

- `msearch.py ... leanfinder`: "The completion of an algebraic closure of a
  complete stable nonarchimedean field is algebraically closed and every finite
  dimensional subspace has an orthogonal basis". Eight hits: spectral norm
  completeness/field structures and general completions; none states the item.
- `msearch.py ... loogle`: `"IsAlgClosed", "Completion"`. Zero hits.
- `msearch.py ... leansearch`: "completion algebraic closure complete
  nonarchimedean field orthogonal basis". Eight hits including `PadicComplex`,
  `AbsoluteValue.Completion`, and inner-product orthonormal bases; none is the
  stable-field result with exact nonarchimedean orthogonality.
- `msearch.py ... grep`:
  `IsAlgClosed.*Completion|Completion.*IsAlgClosed|cartesian`. Hits include
  `PadicComplex` and unrelated cartesian category material; no complete match.
- `rg` in `lean/Sheaf` and `lean/WeilConjectures` for
  `completedAlgebraic|CompletedAlgebraic|IsStableNonarchimedeanField|HasOrthogonalBasis|OrthogonalBasis`
  found the stability definition only. A further topic search for completion,
  cartesian, and orthogonal bases found `WeakSpectralCompletionProduct`,
  `CountableUltrametricBasis`, `FiniteAnalyticRamification`,
  `CondensedSubfieldBasis`, and `ValuedCurveEtaleParameter`; none has the item.
  Some guessed upstream topic directories do not exist, so the full-root
  search above is the authoritative source search.
- `grep -rn 'lem-trf-completed-algebraic-closure-cartesian'
  lean/WeilConjectures`: no match.
- Read `Mathlib.Analysis.Normed.Field.Dense`:
  `IsAlgClosed.of_denseRange` additionally assumes characteristic zero and does
  not assert orthogonality, so it cannot replace this characteristic-free item.
- Checked the proposed declaration name against Mathlib and both project roots;
  no existing declaration with that name.

Sources checked: the current blueprint `literature/blueprint/latest`,
`sec-trace-formula/sk-i-curve-zero`, including the unit and
`lem-trf-local-term-locality`; this item is a historical analytic input, not the
unit statement. Downloaded the node's primary BGR scan into the sandbox only.
It is image-only (pdftotext gives no text), so read rendered PDF pages 110
(printed 102, Corollary 2.4.3/10), 154 (printed 146, Proposition 3.4.1/3), and
225 (printed 219, the explicit k-cartesianness argument in 5.3.4/1).
They confirm the claimed completion and cartesianness. The source URL is
https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf .
No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NG

Self-review, not a separate agent: the dispatcher explicitly forbids starting
other agents; independent maintainer review follows delivery. Reopened the node
and the final Lean file and matched every hypothesis and clause as above.
The base uses exactly nontrivial norm, ultrametricity, completeness, and the
recorded stability predicate. The chosen closure is an actual `IsAlgClosure`,
its norm is the unique spectral one, and its completion has the canonical
composite scalar map. The four conclusion conjuncts describe algebraic
closedness, completeness, the extended nonarchimedean absolute value, and the
isometric base inclusion. The final universal quantifier includes every finite
dimensional submodule; its basis has `finrank` vectors and the equality is
exact for all coefficients. In particular `Finset.sup` in `ℝ≥0` gives zero
for `Fin 0`; no hidden nonemptiness restriction is present. Checked that there
is no characteristic, separability, discrete valuation, or spherical
completeness assumption, and no forced equality of universes. No mismatch or
statement correction was needed. The only new declaration is the sorried
statement corresponding to this node.

Validation: `scompile.py NG lem-trf-completed-algebraic-closure-cartesian
lean/Sheaf/FieldTheory/CompletedAlgebraicClosureCartesian.lean` passed both
sandbox and library module checks, with no compiler errors or warnings.

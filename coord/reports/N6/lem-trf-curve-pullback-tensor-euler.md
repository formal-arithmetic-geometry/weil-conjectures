## Worker report

The module `Sheaf.AlgebraicGeometry.CurvePullbackTensorEuler` states
`AlgebraicGeometry.Scheme.Modules.eulerChar_tensorPullback_tensor`. Its sole theorem
has proof `by sorry`; no new definition, dependency repair, or statement correction
is needed. The node copy changes only `lean`.

The statement matches the node hypothesis by hypothesis and clause by clause:

| Node text | Lean |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| C is a scheme over k | `(C : Scheme.{u}) [C.Over (Spec (.of k))]` |
| C is integral | `[IsIntegral C]` |
| C is proper over k | `[IsProper (C ↘ Spec (.of k))]` |
| Topological Krull dimension one | `(hdim : topologicalKrullDim C = 1)` |
| X is a scheme | `(X : Scheme.{u})` |
| Any scheme morphism j : C → X | `(j : C ⟶ X)` |
| Two invertible O_X-modules | `(L M : X.Modules) [L.IsInvertible] [M.IsInvertible]` |
| j*M is coherent | `(hM : RingedSpace.IsCoherent C.toRingedSpace ((tensorPullback j).obj M))` |
| Sheaf tensor product on X | `L ⊗ M` in the existing monoidal category `X.Modules` |
| Pullback of that tensor product | `(tensorPullback j).obj (L ⊗ M)` |
| χ(C, j*(L ⊗ M)) | `((tensorPullback j).obj (L ⊗ M)).eulerChar k` |
| deg_k(j*L) | `((tensorPullback j).obj L).degree k` |
| χ(C, j*M) | `((tensorPullback j).obj M).eulerChar k` |
| Claimed equality, with addition in Z | Left expression equals the sum of the last two |
| No flatness, immersion or dominance assumption | No additional binder or instance on j |

In particular coherence is the actual finite-type/kernel predicate exposed by the
recorded dependency, not merely its older quasi-coherent finite-type conjunction.
The upstream Euler characteristic and degree definitions are used verbatim. Their
cohomology has the field action induced by C's structure morphism. All objects use
the library's arbitrary universe `u`, explicitly declared; `autoImplicit` is false.
Neither an algebraically closed field nor smoothness or geometric integrality is assumed.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, for def-weil-field; available transitively.
- `AlgebraicGeometry.IsIntegral`, `Mathlib.AlgebraicGeometry.Properties`, for
  def-pc-integral-scheme.
- `AlgebraicGeometry.IsProper`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, for
  def-weil-proper-morphism. Its universally closed condition supplies quasi-compactness,
  so locally finite type here is precisely finite type as in the recorded match.
- `topologicalKrullDim`, `Mathlib.Topology.KrullDimension`, for
  def-kun-topological-krull-dimension, valued in `WithBot ℕ∞`.
- `AlgebraicGeometry.Scheme` and `Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme`,
  for def-pc-scheme; available through the public dependency imports.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, for def-sc-invertible-module.
- `AlgebraicGeometry.RingedSpace.IsCoherent`, exposed by the recorded
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, for pqf-def-coherent. Its defining
  module is `WeilConjectures.AlgebraicGeometry.Coherent`; it asks finite type of F
  and of every kernel of a map from a finite free module on an open.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, publicly exposed by the recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, for
  def-pc-module-pullback. Its defining module is
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; its object is the explicit
  inverse image followed by extension of scalars. Mathlib's other pullback is not used.
- The monoidal tensor on scheme modules from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, for
  def-pur-sheaf-tensor-product. The latter retains the existing localization tensor.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, for def-pc-euler-characteristic.
- `AlgebraicGeometry.Scheme.Modules.degree`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, for def-pc-degree-line-bundle:
  exactly chi(L) minus chi(O_C).

Private proof imports cover all recorded proof dependencies:
`invertible_pullback_tensor` from
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`;
`eulerChar_tensor_invertible_generic_rank` from
`Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank`;
the stalk functors from `WeilConjectures.Topology.PresheafModuleStalkFunctor`;
and `Module.finrank` from `Mathlib.LinearAlgebra.Dimension.Finrank`.
Statement dependencies shared with proof dependencies remain public.

The docstring follows the node's three proof steps: preserve invertibility under
pullback; apply the generic-rank Euler formula with a singleton basis at the generic
stalk; then transport Euler characteristic through the pullback/tensor isomorphism.
Read the source in `literature/stacks-project/varieties.tex`,
`lemma-degree-on-proper-curve` (0AYV) and `lemma-degree-tensor-product` (0AYX), and
`literature/stacks-project/modules.tex`, `lemma-tensor-product-pullback` (01CD) and
`lemma-constructions-invertible` (01CT). The sources impose no additional condition
on j. No source-based correction is necessary.

Edge cases checked before writing:

- Empty C is excluded by integrality and dimension one in the node itself; empty X
  admits no j from this nonempty C. The statement adds no nonemptiness assumption.
- Identity j and M = O_C recover the defining equation degree(L) = chi(L) - chi(O_C).
- On P1 with L = O(a), M = O(b) for arbitrary integers a,b, the identity is
  a+b+1 = a+(b+1), including negative degrees.
- Constant morphisms and nonflat morphisms remain allowed. Pullback and tensor
  compatibility hold for every morphism; no generic injectivity or dominance is used.
- Singular integral proper curves remain included: the proof uses the generic field
  and coherent Euler formula, not regularity or smoothness.
- Arbitrary characteristic and non-algebraically-closed k remain included.

Searches for an existing statement:

- `msearch.py N6 lem-trf-curve-pullback-tensor-euler leanfinder` with query
  "Euler characteristic of a tensor product of line bundles pulled back to a proper
  integral curve equals the degree of the first pullback plus Euler characteristic
  of the second": eight results, all scheme fibre-product carrier/tensor declarations
  in `Mathlib.AlgebraicGeometry.PullbackCarrier`, none asserting coherent Euler
  characteristic. Read the returned signatures and descriptions.
- `msearch.py ... loogle '"eulerChar", "tensor"'`: zero hits.
- `msearch.py ... grep 'eulerChar.*tensor|tensor.*eulerChar' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -n 'pullback.*tensor.*euler|eulerChar.*tensor|tensor.*eulerChar|tensorPullback.*degree|lem-trf-curve-pullback-tensor-euler'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: found generic-rank Euler,
  Hilbert-polynomial, divisor, and base-change statements, but no exact statement
  for an arbitrary morphism from an integral proper curve. In particular
  `CurveEulerTensorGenericRank` takes a coherent second factor and a specified
  generic point and concludes a rank-weighted formula; it is the proof dependency,
  not an exact existing match.
- Exact search for `eulerChar_tensorPullback_tensor` and for the item ID in both
  source trees: no existing declaration or attachment. No new notion is introduced.

Validation: `scompile.py N6 lem-trf-curve-pullback-tensor-euler` on the delivered file
passed in both sandbox and library module modes (2.2 and 2.5 seconds respectively),
with no compiler diagnostics. Every variable and universe is explicitly bound.

## Second reading by N6

Author's check against the open node and final Lean file; the maintainer supplies
the independent delivery review. Each row above occurs literally in the signature.
Checked especially that hM uses `RingedSpace.IsCoherent`, that all three occurrences
of pullback use `tensorPullback`, and that the left side pulls back the tensor on X
rather than replacing it by a tensor on C in the statement. The degree is evaluated
over k, as are both Euler characteristics, and no generic point or rank assumption
was added. The three-step proof is recorded in the theorem docstring, while its Lean
proof is only `sorry`. No mismatch or disputed statement was found.

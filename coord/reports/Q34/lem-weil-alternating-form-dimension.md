## Worker report

The module `Sheaf.LinearAlgebra.AlternatingFormDimension` states
`LinearMap.BilinForm.even_finrank_of_isAlt_of_char_ne_two`, with exactly one
postponed theorem and no new definitions. Its proof is `sorry`, as required in
stage 2. The declaration docstring gives the full finite-basis, Gram-determinant,
nondegeneracy, cancellation and odd-dimension contradiction proof from the node.

Hypothesis and conclusion correspondence:

- A field K: `{K : Type u} [Field K]`.
- Characteristic different from two: `(hchar : ringChar K ≠ 2)`. Mathlib's
  `ringChar` is the unique semiring characteristic, including zero.
- A K-vector space V: `{V : Type v} [AddCommGroup V] [Module K V]`.
  The field and vector-space universes are explicit and independent.
- Finite dimension: `[FiniteDimensional K V]`, Mathlib's finite-module
  abbreviation for vector spaces.
- The bilinear form β: `(B : LinearMap.BilinForm K V)`, the existing curried
  linear-map representation of a K-valued bilinear form.
- Nondegeneracy: `(hnd : B.Nondegenerate)`, the Mathlib predicate requiring both
  radicals to be zero. For alternating forms either radical condition implies
  the other, so this is the source's usual nondegeneracy condition.
- Alternation: `(halt : B.IsAlt)`, whose definition is `∀ x, B x x = 0`.
- The dimension is even: `Even (Module.finrank K V)`. Finite dimensionality
  makes this natural-number finrank exactly the dimension in the node.

There are no statement-dependency nodes. The recorded proof dependency
`lem-weil-bilin-form-nondegenerate-det` is a Mathlib leaf with match
`LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` from
`Mathlib.LinearAlgebra.Matrix.BilinearForm`; its module is imported without
`public`, for the future proof. I read its full signature and ambient assumptions:
a commutative domain, an additive group with a module structure, and a finite
decidable basis index. Specializing to a field and a finite basis gives exactly
the needed nonzero Gram determinant. Its iff is used in the forward direction.

The signature publicly imports `Mathlib.Algebra.CharP.Defs`,
`Mathlib.LinearAlgebra.BilinearForm.Properties`, and
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`, using their existing `ringChar`,
`LinearMap.BilinForm.IsAlt`, `LinearMap.BilinForm.Nondegenerate`,
`FiniteDimensional`, and `Module.finrank` declarations. No notion is copied.

Edge cases checked mathematically before writing:

- Dimension zero is included: the unique form is nondegenerate on the zero
  space, the empty Gram determinant is one, and zero is even.
- In dimension one every alternating form is zero and is degenerate, so there
  is no false one-dimensional case.
- Positive odd characteristic is included, for example the standard
  two-dimensional alternating form over the field with three elements.
- Characteristic zero is included without requiring a `CharZero` instance.
- Characteristic two is excluded exactly as in the node; no nonzero-dimension,
  nontrivial-vector-space or extra characteristic hypothesis was added.

Searches (2026-10-17):

- `msearch.py leanfinder`: "A finite dimensional vector space over a field of
  characteristic not two with a nondegenerate alternating bilinear form has
  even dimension". Eight hits included `IsAlt.self_eq_zero`, symplectic
  determinant facts and perfect-pairing finrank equality; none states this
  parity theorem.
- `msearch.py loogle`: "LinearMap.BilinForm.IsAlt,
  LinearMap.BilinForm.Nondegenerate, Even". Zero hits.
- `msearch.py leansearch`: "finite dimensional nondegenerate alternating
  bilinear form even dimension". Eight hits included the existing alternating
  and nondegenerate predicates and the Gram determinant criterion; no parity
  theorem.
- `msearch.py grep`, Mathlib LinearAlgebra:
  `alternating.*even|even.*[Ff]inrank|finrank.*[Ee]ven|IsAlt|def Nondegenerate`.
  Fourteen hits exposed the existing alternation predicates; no parity theorem.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, for the blueprint
  id, alternation/even-dimension phrases and `IsAlt`, found upstream
  `LinearMap.BilinForm.even_finrank_of_isAlt` in
  `WeilConjectures.Mathlib.LinearAlgebra.Matrix.BilinearForm`. I read the whole
  module: it has the additional `[CharZero K]` assumption, so it does not state
  this node's theorem for positive odd characteristic. The new theorem has a
  distinct name and the required broader characteristic hypothesis.
- `rg` in `dag/lean_names_upstream.json` for alternating dimension and even
  finrank returned no hit. A source search for the new declaration name found
  no existing declaration. Project Lean contains no matching theorem.

I compared the node with the current main-20261015 blueprint statement and its
proof; the mathematical statement agrees. No statement correction, dependency
repair, new node, or disputed statement is needed. Only the item's `lean` field
changes in its JSON copy.

Validation: the required `scompile.py Q34 lem-weil-alternating-form-dimension`
single-file check passed with no errors or warnings. Delivery preflight and its
repeat compile are run through `deliver2.py`.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review correction (2026-10-17)

The worker's search read the older slopmaster2 copy of
`WeilConjectures.Mathlib.LinearAlgebra.Matrix.BilinearForm`, whose
`LinearMap.BilinForm.even_finrank_of_isAlt` assumes `[CharZero K]`. On the
delivery's base and in the live published library, the same declaration assumes
`[NeZero (2 : K)]`. For a field, that is exactly char(K) ≠ 2. The module is
tagged `lem-weil-alternating-form-dimension` and its proof is complete. It
states the node exactly: a field K with characteristic not two, a
finite-dimensional K-vector space V in an independent universe, and a
nondegenerate, alternating `LinearMap.BilinForm K V` imply
`Even (Module.finrank K V)`.

One definition per notion therefore applies. The item's `lean` record is changed
to `existing: true` for this declaration, with `branch: "slopmaster2"`, and the
delivered module `Sheaf.LinearAlgebra.AlternatingFormDimension` is left out.
A check compile derived the delivered signature, with `ringChar K ≠ 2`, from the
existing declaration through `Ring.two_ne_zero`.

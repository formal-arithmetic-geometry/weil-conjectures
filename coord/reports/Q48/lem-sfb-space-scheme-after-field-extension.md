## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSchemeAfterFieldExtension` states
`AlgebraicGeometry.AlgebraicSpace.scheme_over_algebraicClosure_of_exists_field_extension`.
Its only theorem has proof `sorry`, as required in stage 2. There are no new definitions,
helper theorems, dependency modules, new nodes, or statement corrections. Only `lean` is
changed in the node copy.

Source read: Stacks `spaces-over-fields.tex`,
`lemma-when-scheme-after-base-change`, Tag 0B84, part (1), with its proof. The source
assumes quasi-separatedness, but neither quasi-compactness nor finite type for part (1).
The node expands this as quasi-compactness of the relative diagonal. The module retains
that expansion rather than imposing a stronger condition on X.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type u} [Field k]`.
- A fixed algebraic closure is `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. This allows any fixed closure with its specified k-algebra map,
  rather than restricting to one chosen implementation. `IsAlgClosure` includes both
  algebraic closedness and algebraicity over k. The base field and all scheme tests
  use the project's common size universe, not an independently smaller universe.
- An algebraic space over Spec k is `(X : AlgebraicSpace (Spec (.of k)))`.
  Its underlying presheaf is `X.obj.obj`; the existing full-subcategory construction
  supplies the fppf sheaf condition, representable diagonal, and surjective etale atlas.
- Its relative diagonal is `prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)` on the category
  `Over (Spec (.of k))`. The product there is the relative product over Spec k.
- The quasi-compact diagonal hypothesis is
  `IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)` of that diagonal.
  The existing predicate quantifies over EVERY scheme test T and map from h_T to
  the target and gives a representing scheme pullback whose projection is
  quasi-compact. Mathlib's `QuasiCompact.isCompact_preimage` is exactly the node's
  inverse-image condition for quasi-compact open subsets. No global compactness of
  X, its atlas, or its diagonal source is assumed.
- Existence of an extension K/k is the `hK` binder, beginning
  `∃ (K : Type u) (_ : Field K) (_ : Algebra k K)`. It is existential over all
  extension fields in the project's size convention; it requires neither finite
  generation, finiteness, separability nor an embedding of K into Ω.
- Schemeness of X_K is the further existential `(Y : Over (Spec (.of K)))` and
  `Nonempty` of an isomorphism from the restricted presheaf to `yoneda.obj Y`.
  The restriction is
  `(Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙ X.obj.obj`.
  For a K-scheme T, `Over.map`
  regards T as a k-scheme by composing its structural map. A pair of a section of
  X on T and the specified structural map to Spec K is precisely a section of
  X times Spec K. This is the base-change functor itself, not an arbitrary map or
  an unspecified comparison assumption.
- The conclusion is `∃ Y : Over (Spec (.of Ω)), Nonempty (...)` with the identical
  restricted-presheaf expression using `algebraMap k Ω`. Thus X_Ω is represented
  by a scheme over Ω, with its prescribed k-structure. No extra conclusion or
  hypothesis is inserted. In particular, there is no compactness, finite type,
  reducedness, smoothness, or group structure binder.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`,
  `Mathlib.Algebra.Field.Defs` (commutative nontrivial division ring).
- `def-weil-algebraic-closure`: Mathlib `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, and `IsAlgClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, the predicate explicitly specified in
  this node's `mathlib_match.how`. Read both signatures and docstrings; use
  `IsAlgClosure k Ω` to express an arbitrary fixed closure.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` and
  `AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`. Read the full definitions and docstrings.
- `def-pc-field-extension`: Mathlib `Algebra` in
  `Mathlib.Algebra.Algebra.Defs`, used with `[Field k] [Field K]` and its
  canonical `algebraMap`. This is the exact recorded field-extension interface.
- `lem-trf-space-fibre-products-etale-covers`: module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, declarations
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.etaleCover_pullback`, and
  `AlgebraicGeometry.AlgebraicSpace.etale_fibreProduct_isScheme`. Read their
  full signatures and proof docstrings. The module is publicly imported for the
  fibre-product interpretation; its covering statements are also part of the proof plan.

The theorem docstring records all six proof steps and their cited nodes: qcqs open
reduction, directed finitely generated subalgebras, the sheaf-limit identification,
eventual schematicity, finite residue-field specialization into Ω, and Zariski gluing.
Every currently stated proof dependency is imported. Mathlib leaves are imported via
`Morphisms.QuasiSeparated`, `Morphisms.Affine`, `GammaSpecAdjunction`,
`Spectrum.Maximal.Basic`, `Jacobson.Ring`, `IsAlgClosed.Basic`, and the already
imported scheme pullback theory. Other stated proof-dependency modules are
`AlgebraicSpaceAffineAtlasOpenCover`, `AlgebraicSpaceOpenSubspace`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`.

The following proof dependencies have no Lean record or Mathlib match in the read
node files, so there is no module to import for them yet:
`lem-sfb-space-qcqs-source-products`, `lem-sfb-space-integral-qcqs-permanence`,
`lem-sfb-qcqs-space-fibre-product`, `lem-sfb-space-affine-locality`, and
`lem-sfb-space-affine-limits-schematic-stages`. They are proof prerequisites, not
missing statement notions; the statement uses the already supplied algebraic-space
interface and requires no repair of them. No import cycle is introduced.

Edge cases checked before writing:

- X empty: both restrictions are represented by the empty scheme; the proof's
  assembly permits the empty cover. The theorem contains no nonempty hypothesis.
- K = k: allowed by the existential field and algebra binders; any schematic X
  has schematic base change to Ω. No proper-extension condition appears.
- Algebraically closed k, with Ω = k and its identity algebra: allowed;
  `IsAlgClosed.instIsAlgClosure` supplies the closure predicate.
- Imperfect k and inseparable extensions: allowed; the finite residue-field
  embedding needs algebraicity and algebraic closedness, not separability.
- Infinite disjoint unions and non-finite-type spaces: not excluded. The proof
  works on individual quasi-compact opens, with no finite cover of X required.
- Relative diagonal on scheme tests is not a vacuous identity-morphism hypothesis:
  its target is X times_k X, and its pullback detects intersections of scheme
  charts. It imposes the precise quasi-separatedness required by Tag 0B84.

Searches made (all before writing):

- `msearch.py ... leansearch` query: "A quasi-separated algebraic space that
  becomes a scheme over a field extension becomes a scheme over an algebraic closure".
  Result: 8 hits, about quasi-separated scheme morphisms, their diagonals, composition
  and base change. None is a field-extension schemeness theorem for algebraic spaces.
- `msearch.py ... leanfinder` query: "A quasi-separated algebraic space which is
  a scheme after a field extension is a scheme over the algebraic closure".
  Result: 8 hits, including `QuasiSeparated.of_quasiSeparatedSpace`,
  `quasiSeparatedSpace_iff_quasiSeparated`, and `IsIntegral`; none matches the node.
- `msearch.py ... loogle` query: `AlgebraicClosure, IsRepresentable`.
  Result: zero hits, unknown identifier `IsRepresentable` on that service.
- `msearch.py ... grep` query: `scheme_after|when_scheme_after|AlgebraicSpace`
  in Mathlib `AlgebraicGeometry`. Result: zero hits.
- `rg` of upstream `lean/WeilConjectures` for this node's blueprint id: zero hits.
- `rg` of upstream and `lean/Sheaf` for
  `scheme_after|when_scheme_after|schemeAfterField|scheme_after_field`: zero hits.
- Broader field/scheme and `Over.map` searches of both project trees found the
  existing downstream `SeparatedGroupSpaceGeometricScheme` statement; it assumes
  group operations and a closed diagonal, so it is not this theorem. It uses the
  same restriction encoding and explicitly cites this node as its final proof step.
- Searches for `IsRepresentableWith` and `QuasiCompact p.left` found the existing
  relative diagonal encoding in `AlgebraicSpaceDenseSchemeOpen`; its declaration
  and docstring confirm the same scheme-test condition. No duplicate predicate
  was introduced.
- The proposed full declaration name was searched in both project trees and
  `dag/lean_names_upstream.json`; no existing declaration was found.

Validation: `scompile.py` compiled the delivered file cleanly in sandbox and library
modes (1.7 s and 1.6 s respectively), with no errors or unexpected warnings.
All variables and the universe are explicitly bound, `autoImplicit` is false, and
all Lean lines are at most 100 characters. The node signature is copied verbatim
from the theorem keyword up to `:=`. No node fault or disputed statement was found.

The delivery dry run passed the server preflight and per-file compile. Its staged
packet contains exactly the module, the node lean record, and this report.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

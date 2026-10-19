## Worker report

The module `Sheaf.RingTheory.ColimitUnramifiedAlgebra` states
`Algebra.exists_unramified_stage_of_colimit`, with its proof postponed by `sorry`.
It is exactly the affine algebra assertion of Stacks Project, Algebra, Tag 0C4F
(`literature/stacks-project/algebra.tex`, lemma-colimit-unramified, lines 47570–47603).
The source statement and proof were read. No statement correction, new node,
dependency repair, or disputed statement is needed.

Clause-by-clause correspondence:

- The nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Its ring diagram is
  `F : I ⥤ CommRingCat.{u}`. The index and ring universe agree, as required
  by the project's colimit size convention; the two initial algebras have
  independent universes `v` and `w`.
- `A = colim Aᵢ` is `↥(colimit F)` with `[HasColimit F]`.
  This is the dependency's chosen categorical colimit, not a separate model.
- The initial index is `(i₀ : I)`. The two commutative rings are
  `B₀ : Type v` and `C₀ : Type w`, with their `CommRing` instances and
  `[Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]`.
- The initial map is `(φ₀ : B₀ →ₐ[F.obj i₀] C₀)`, which includes exactly
  compatibility with the two initial-base algebra maps.
- The colimit-base algebra structure comes from `(colimit.ι F i₀).hom.toAlgebra`.
  The rings `B` and `C` are written as the tensor products
  `↥(colimit F) ⊗[F.obj i₀] B₀` and
  `↥(colimit F) ⊗[F.obj i₀] C₀`. The map between them is
  `(Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) ↥(colimit F)) φ₀).toRingHom`.
  Mathlib's `map_tmul` says that it sends `a ⊗ b` to `a ⊗ φ₀ b`.
- `hunramified` requires that this specific ring map is `RingHom.FiniteType`
  and that its Kähler differential module is `Subsingleton`.
  The algebra structure used by `@KaehlerDifferential` is explicitly
  this ring map's `.toAlgebra`. For an additive group, `Subsingleton`
  means that every element is zero, exactly the vanishing in the node.
- The initial finite-generation assumption is `(hfg : φ₀.toRingHom.FiniteType)`.
  Mathlib defines this as `Algebra.FiniteType` for `φ₀.toRingHom.toAlgebra`,
  so it refers to `C₀` over `B₀` via the given map, not over the base ring.
- The conclusion is `∃ (i : I) (h : i₀ ≤ i), ...`.
  At this stage the initial-base algebra structure is exactly
  `(F.map (homOfLE h)).hom.toAlgebra`.
  The tensor rings are `(F.obj i) ⊗[F.obj i₀] B₀` and
  `(F.obj i) ⊗[F.obj i₀] C₀`; the map is again the tensor map `id ⊗ φ₀`.
  The conclusion asserts its finite type and the vanishing of its differential
  module, with the algebra structure explicitly induced by that map.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit` from
  `Mathlib.CategoryTheory.Limits.HasLimits`; its coprojection `colimit.ι`
  supplies the initial-base action. This dependency is already usable.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential` from
  `Mathlib.RingTheory.Kaehler.Basic`, with the docstrings and signatures of
  `KaehlerDifferential.D` and `KaehlerDifferential.linearMapEquivDerivation` read.
  The module is Mathlib's cotangent construction and universal derivation.
- Proof-only import `Mathlib.RingTheory.Kaehler.TensorProduct` supplies
  `KaehlerDifferential.tensorKaehlerEquivBase` and `tensorKaehlerEquiv` for
  `lem-weil-pbc-kahler-differentials-base-change`.
- Proof-only import
  `WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise`
  supplies `TensorProduct.directedColimitBaseChangeElementwise` for
  `lem-weil-pbc-directed-colimit-base-change-elementwise`. Its current full
  source and proof docstring were read through `scompile.py --source`,
  since the older local source checkout lacks that module.

Edge cases checked before writing: empty index sets are excluded exactly as
stated; a singleton index and the possibility `i = i₀` are allowed; zero rings,
a zero colimit, `C₀ = 0`, and noninjective transition maps are allowed.
There is no finite-presentation, nonzero, characteristic, or injectivity
assumption. If `C₀` needs zero algebra generators, its differential module
is already zero and the source argument permits the initial stage.
Finite type over the source of `φ₀` is not accidentally replaced by finite
type over `Aᵢ₀`. The only `letI` binders install the specified algebra structures;
no tensor ring or morphism is hidden behind an object-valued `let` binder.

Searches for an exact existing statement (the msearch evidence is also in
`searches.jsonl` in the sandbox):

- `msearch.py ... leanfinder`, query "A finite type algebra map over a directed
  colimit which is unramified is unramified at some finite stage": eight
  results, including `Algebra.Unramified`, `.finiteType`, `.comp` and pointwise
  ramification statements; none is colimit descent.
- `msearch.py ... leansearch`, query "Unramified ring homomorphism descends
  along directed colimits of commutative rings": eight results, including
  `Ring.DirectLimit`, `CommRingCat.Colimits.colimitIsColimit`,
  `Algebra.Unramified`, and `RingHom.FormallyUnramified`; no exact theorem.
- `msearch.py ... loogle`, query `Algebra.Unramified`: twelve results, including
  base change and composition; no finite-stage colimit descent.
- `msearch.py ... grep`, pattern `colimit.*[Uu]nramified|[Uu]nramified.*colimit`
  in Mathlib/RingTheory: zero hits.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
  `unramified.*colimit|colimit.*unramified|lem-trf-colimit-unramified-algebra`:
  only the parent `Sheaf/TraceFormula/UnramifiedLimitDescent.lean` proof
  docstring cites this item; it does not state the affine algebra theorem.
  The same search of `dag/lean_names_upstream.json` found no exact declaration.
- `rg` over Mathlib, upstream and project sources for
  `exists_unramified_stage` found no declaration-name collision.

Validation: `scompile.py Q78 lem-trf-colimit-unramified-algebra` compiled the
module both as a sandbox file and at its actual library module name, cleanly
(2.2 seconds and 2.1 seconds). The expected theorem proof is the only `sorry`.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc second reader, 2026-10-19)

The index binder `[PartialOrder I]` was replaced by `[Preorder I]`: a Stacks directed set
(Categories, Definition 00D3) is a preorder, and brief-stage2.md §3 (STATE line DIRECTED SETS)
prescribes `[Preorder I] [IsDirected I (· ≤ ·)]` for new modules; the cited proof dependency
`TensorProduct.directedColimitBaseChangeElementwise` is itself stated over `[Preorder I]`.
The node's `lean.statement` was updated verbatim. The module compiles cleanly (1.8 s).

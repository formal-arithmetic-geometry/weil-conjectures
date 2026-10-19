## Worker report

`sk-d-linear` is an existing-definition package. No new Lean module, theorem, proof,
or definition is delivered. Only the node's `lean` field changes. Its primary binding is
`Representation.CompositionSeries` in
`WeilConjectures.RepresentationTheory.CompositionSeries`, with the verbatim signature
`structure CompositionSeries`; the additional declarations list records the existing
representation constructions available through that module. The separately imported
semisimplicity API is identified explicitly in the record's note and below.

Source checked: the complete current blueprint unit
`literature/blueprint/main-20261015/blueprint/sec-algebraic-groups-lie-algebras/sk-d-linear/_section.md`.
Its text agrees verbatim with the node. There are no statement dependencies or proof
steps in this node. No repair note for `sk-d-linear` is present.

### Hypotheses and clauses

The common specialization is
`{k : Type u} [Field k] [IsAlgClosed k] [CharZero k]`,
`{B : Type v} [Group B]`, and
`{V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]`.
A second vector space has the analogous assumptions, with its own universe.
These are the source's standing conventions, not additional restrictions. The existing
APIs are more general and can be applied to precisely these objects. A section convention
is not a new coefficient-field structure, and no competing representation type is needed.

| Source clause | Existing Lean rendering and reason |
| --- | --- |
| Algebraically closed characteristic-zero coefficient field | `[Field k] [IsAlgClosed k] [CharZero k]` at each use in this unit. These assumptions are checked in the scratch consumer. |
| All vector spaces finite dimensional over `k` | `[AddCommGroup V] [Module k V] [FiniteDimensional k V]`, and likewise for every other space used. The constructions themselves do not need all these restrictions. |
| Linear endomorphisms `End(V)` | `Module.End k V`, the existing abbreviation for `V →ₗ[k] V`. |
| Invertible endomorphisms `GL(V)` | `Units (Module.End k V)`; equivalently linear automorphisms. No choice of basis or restriction to a particular coordinate space occurs. |
| A group representation is a homomorphism into `GL(V)` | `ρ : Representation k B V`, together with `ρ.asGroupHom : B →* Units (Module.End k V)`. Mathlib initially stores `B →* Module.End k V`; since `B` is a group, the inverse of `ρ g` is `ρ g⁻¹`. Thus `asGroupHom` gives exactly the required invertible action, not a representation by possibly singular maps. |
| Invariant subspace | `S : Subrepresentation ρ`, whose fields are `toSubmodule : Submodule k V` and `apply_mem_toSubmodule (g : B) : v ∈ S → ρ g v ∈ S`. This is preservation by every group element. |
| Simple means nonzero and no invariant subspaces other than zero and the whole space | `ρ.IsIrreducible`. It is `IsSimpleOrder (Subrepresentation ρ)`, which includes nontriviality. The published `Representation.isIrreducible_iff` says exactly `Nontrivial V ∧ ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤`. |
| Semisimple means a finite direct sum of simples | `ρ.IsSemisimpleRepresentation` in `Mathlib.RepresentationTheory.Semisimple`. This is the complemented-lattice definition; the published `Representation.isSemisimpleRepresentation_iff_exists_iSupIndep` identifies it, in finite dimension, with an independent spanning family of irreducible subrepresentations. Such a family is finite because every summand is nonzero and their dimensions add inside the finite-dimensional space. Its internal direct sum is the source's finite direct sum; conversely a finite direct sum supplies the independent spanning family. The zero representation corresponds to the empty family. |
| Faithful means injective homomorphism | `Function.Injective ρ.asGroupHom`. This is directly the source's predicate using existing `Function.Injective`, not an assertion that all representations are faithful. No new alias for injectivity is introduced. |
| Subquotient `S/U`, with invariant `U ≤ S ≤ V` | For `S U : Subrepresentation ρ` and `h : U ≤ S`, `S.subquotient U`. Its space is `S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype`; with `h`, the denominator is exactly `U` regarded as a subspace of `S`. Its action is induced by the restricted `ρ g` via `Submodule.mapQ`. Being a subrepresentation already expresses `S ≤ V`. |
| Composition series is a finite invariant filtration from zero to the whole representation | `s : ρ.CompositionSeries`. Its `series` is `_root_.CompositionSeries (Subrepresentation ρ)`, a finite chain whose adjacent terms form covers; `head_eq : series.head = ⊥` and `last_eq : series.last = ⊤` impose both required endpoints. The generic root `CompositionSeries` alone would not suffice and is not the primary binding. |
| Successive quotients are simple | `s.series.step i` is a cover. `Subrepresentation.isIrreducible_subquotient_iff` identifies a cover with simplicity of the quotient, and the existing `s.isIrreducible_factor i` exposes this property for every index. |
| Constituents are those successive quotients | `s.factor i`, for `i : Fin s.length`, is `(s.series i.succ).subquotient (s.series i.castSucc)`. Each occurrence retains its own index, so repetitions of equivalent simple factors are retained. The weaker unindexed predicate `Representation.IsConstituent` is not used to replace the indexed factors. |
| Direct sums have the componentwise action | `Representation.directSum ρs`, whose action is `DirectSum.lmap (fun i => ρs i g)`. For two summands the existing `ρ.prod σ` has action `(ρ g).prodMap (σ g)`. Finite direct sums are the source's finite-dimensional direct sums. |
| Tensor product has diagonal action | `ρ.tprod σ`, whose value at `g` is `TensorProduct.map (ρ g) (σ g)`, hence sends `v ⊗ₜ w` to `ρ g v ⊗ₜ σ g w`. |
| Exterior algebra is the tensor algebra modulo the square relations | `ExteriorAlgebra k V` is `CliffordAlgebra (0 : QuadraticForm k V)`. `CliffordAlgebra.Rel` imposes `ι v * ι v = algebraMap _ _ (0 v) = 0` on the tensor algebra and `CliffordAlgebra` is the generated ring-congruence quotient. This is exactly the ideal generated by all `v ⊗ v`. |
| Degree-`s` exterior power | `ExteriorAlgebra.exteriorPower k s V`, written `⋀[k]^s V`, is the `s`-th power of the range of the degree-one generating map inside that quotient: precisely the degree-`s` homogeneous component. |
| Induced action on the exterior power | `ρ.exteriorPower s`, defined by `toFun g := _root_.exteriorPower.map s (ρ g)`. This applies `ρ g` to every wedge factor. |
| Determinant representation in rank `r` | `ρ.exteriorPower (Module.finrank k V)`. This uses the representation on the top exterior power itself; it is not replaced by only the determinant character. |

### Existing declaration sources read

The declaration signatures, enclosing variables, definitions, and docstrings were read,
not inferred from declaration names:

- `Mathlib.RepresentationTheory.Basic`: `Representation`, `Representation.asGroupHom`,
  `Representation.directSum`, `Representation.prod`, `Representation.tprod`.
- `Mathlib.RepresentationTheory.Subrepresentation`: `Subrepresentation` and
  `Subrepresentation.toRepresentation`.
- `Mathlib.RepresentationTheory.Irreducible`: `Representation.IsIrreducible`.
- `Mathlib.RepresentationTheory.Semisimple`: `Representation.IsSemisimpleRepresentation`.
- `WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation`:
  `Subrepresentation.subquotient`.
- `WeilConjectures.Mathlib.RepresentationTheory.Irreducible`:
  `Representation.isIrreducible_iff` and
  `Subrepresentation.isIrreducible_subquotient_iff`.
- `WeilConjectures.Mathlib.RepresentationTheory.Semisimple`:
  `Representation.isSemisimpleRepresentation_iff_exists_iSupIndep`.
- `WeilConjectures.RepresentationTheory.CompositionSeries`:
  `Representation.CompositionSeries`, `Representation.CompositionSeries.factor`,
  and `Representation.CompositionSeries.isIrreducible_factor`. This newer published
  module was read using `scompile.py --source`; the older local upstream tree lacks it.
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`: `CliffordAlgebra.Rel`,
  `CliffordAlgebra.ringCon`, and `CliffordAlgebra`.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra` and
  `ExteriorAlgebra.exteriorPower`.
- `Mathlib.LinearAlgebra.ExteriorPower.Basic`: `exteriorPower.map`.
- `WeilConjectures.Mathlib.RepresentationTheory.Basic`:
  `Representation.exteriorPower`, including its source/blueprint documentation.
- `Mathlib.Order.JordanHolder`: the generic composition-series documentation explicitly
  warns that it imposes no endpoint conditions; the representation-specific structure
  above supplies them.

The node has `stmt_deps: []` and `proof_deps: []`, so there is no dependency record to
repair or import. The existing series/factor API is also already recorded by
`def-mg-weil-composition-series`; it is reused, not copied or modified.

### Edge cases

- `V = 0` is permitted. It is not simple: its subrepresentation lattice is trivial.
  It is semisimple as the empty direct sum. The composition-series structure permits
  length zero and then `Fin s.length` is empty, so there are no factors.
- A nonzero simple representation has the one-step series `0 < V`; no unnecessary
  lower bound of two steps is introduced.
- Repeated isomorphic factors retain separate `Fin s.length` indices.
- `U = 0` and `U = S` give `S` and the zero subquotient respectively. Neither is excluded.
- Empty finite sums are allowed. The tensor construction allows zero spaces.
- `s = 0` in the exterior power is allowed and gives the scalar line with its induced
  trivial action. In rank zero, the determinant is this zeroth exterior power, not zero.
  Exterior powers above the rank are also defined; no `s ≤ rank` restriction is imposed.
- `B` is an arbitrary group, without a finiteness assumption. Field, group, and vector
  space universes are independently bound; no universe equality is required.
- Characteristic zero and algebraic closure are standing scope assumptions, not a
  redefinition of representations; the same standard definitions remain available in
  the later finite-field subsection.

### Searches

All searches were made before deciding to reuse the existing APIs.

- `msearch.py`, LeanFinder, query
  `group representation invariant subspace irreducible semisimple composition series exterior power`:
  eight hits, including `Representation.IsIrreducible`; source inspection identified
  the exact existing simple-representation notion.
- `msearch.py`, Loogle, query
  `Representation, Subrepresentation, Representation.IsIrreducible, CompositionSeries`:
  zero hits for the combined query. A second query `CompositionSeries` returned twelve
  hits headed by the generic `CompositionSeries` and its equivalence relation; inspection
  revealed the endpoint issue addressed by the published representation-specific API.
- `msearch.py`, LeanSearch, query
  `representation subquotient composition series semisimple exterior power`:
  eight hits, including `ExteriorAlgebra.exteriorPower`, `exteriorPower.presentation`,
  `CompositionSeries`, and `exists_compositionSeries_of_isNoetherian_isArtinian`.
- `msearch.py`, Mathlib grep under `RepresentationTheory`, query
  `IsSemisimpleRepresentation|def exteriorPower|def directSum|def tprod|def quotient|def IsIrreducible`:
  twelve hits, including semisimplicity and the direct-sum, tensor, and quotient APIs.
- Direct `rg` in `WeilConjectures/` for `IsSemisimpleRepresentation`, `sk-d-linear`,
  subquotients, and composition series found the existing exterior-power definition,
  subquotient construction, and semisimplicity equivalence. Direct search for the item
  id located the exterior-power docstring and the algebraic-group representation overview.
- Direct `rg` in `lean/Sheaf/` found uses of representations and diagonal tensor actions,
  but no alternative package defining this sketch. No duplicate definition was written.
- Search in `dag/lean_names_upstream.json` and the algebraic-group DAG nodes identified
  `Representation.CompositionSeries` and `.factor` in the published composition-series
  module. `scompile.py --source` retrieved and verified that exact current source.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` is needed.

### Validation

The scratch consumer `scratch/ExistingInterface.lean` imports the published composition-series
and semisimplicity modules. It explicitly binds independent universes and the source's
field/group/finite-dimensional hypotheses, and checks every construction, the simplicity
and semisimplicity characterizations, the indexed factors, the zeroth exterior power,
and the determinant expression. This scratch file is not a delivered library module.
The scratch consumer compiled cleanly through the prescribed `scompile.py Q122 sk-d-linear`
wrapper, both in the sandbox and against the published library (5.4 s and 6.2 s; no warnings
or errors). The delivery dry run separately probed every name in `lean.declarations` and returned
`OK (dry run): commit d4ce66b4c6 passes the preflight and compiles; nothing pushed`.

## Second reading by Q122

No independent worker reading is claimed: the dispatcher brief requires direct delivery
and reserves independent review to the maintainer. The author reread the source unit,
the node, and the existing declaration bodies. The potential mismatch was the generic
Mathlib composition series with unrestricted endpoints; the delivery instead binds the
published `Representation.CompositionSeries` with `head_eq` and `last_eq`. The other
potential mismatch was the complemented-lattice definition of semisimplicity; the report
identifies the existing finite-dimensional direct-sum equivalence and the separate module
needed to use it. No source clause or hypothesis was changed.

## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure` states both
assertions of `lem-zl-geometric-irreducibility-subalgebra-colimit`. Its declarations are
`AlgebraicGeometry.geometricallyIrreducible_spec_of_injective` (clause 1) and
`AlgebraicGeometry.geometricallyIrreducible_spec_colimit` (clause 2). Both proofs are `sorry`;
there are no new definitions or additional nodes. Only the item's `lean` field changes.

Source checked: `literature/stacks-project/algebra.tex`, definition
`definition-geometrically-irreducible` and lemma
`lemma-subalgebra-geometrically-irreducible`, Tag 037N, assertions (1) and (3),
lines 11207–11257. The first assertion is stated for an injective algebra homomorphism,
as the node requests; passage to its image gives exactly the subalgebra formulation.
The docstrings give the node's proof, including affine base change, flatness, the prime
nilradical criterion, the underlying module colimit construction, tensor commutation,
and detection of each nilpotence relation at a stage.

Hypotheses and conclusions, clause by clause:

- The field is `{k : Type u} [Field k]` in both statements.
- In clause 1, `{A S : Type u} [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]`
  gives the commutative unital algebras with their fixed maps from `k`.
- `(u : A →ₐ[k] S)` is exactly a unital ring homomorphism preserving these maps,
  and `(hu : Function.Injective u)` imposes precisely the required injectivity.
- `(hS : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k S))))`
  asserts geometric irreducibility of `Spec S` over `k`. Its conclusion replaces `S` by `A`.
  No additional morphism or structure on these schemes is chosen.
- In clause 2, `{I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]`
  expresses a nonempty small directed poset. The standard preorder category has the unique
  morphism `i ⟶ j` exactly when `i ≤ j`.
- `(F : I ⥤ CommAlgCat.{u} k)` supplies the entire diagram, including unital algebra
  transition maps, identity laws and composition laws. There is no injectivity assumption.
- `(hF : ∀ i : I, GeometricallyIrreducible
  (Spec.map (CommRingCat.ofHom (algebraMap k (F.obj i))))))` is the condition at every stage.
- The conclusion is geometric irreducibility of
  `Spec.map (CommRingCat.ofHom (algebraMap k (colimit F : CommAlgCat.{u} k)))`.
  The category annotation is essential to prevent Lean from interpreting the colimit as
  a colimit in `Type`. `CommAlgCat` already has the required colimits, so no colimit-existence
  hypothesis is added.
- There are no finite-generation, reducedness, domain, characteristic, or nontrivial-ring
  binders. Nonemptiness of spectra is part of Mathlib's irreducibility notion.
- The single explicit universe `u` is shared by the field, ring carriers and index type,
  as required by the project convention for small algebra colimits. There is no independent
  universe for test extensions that could make geometric irreducibility vacuous.

Recorded statement dependencies used, after reading their records and source declarations:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`,
  `Mathlib.AlgebraicGeometry.Over`. The canonical structure morphism is displayed explicitly,
  as required by the recorded geometric-irreducibility interface.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIrreducible`,
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`. The equivalence
  `geometrically_iff_of_commRing` in `Geometrically.Basic` confirms the quantification over
  field extensions and the prescribed base-change interpretation.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`,
  `Mathlib.CategoryTheory.Limits.HasLimits`. `Mathlib.Algebra.Category.CommAlgCat.Basic`
  supplies `CommAlgCat`, its algebra-hom morphisms and the `HasColimits` instance.

All stated proof dependencies are imported through their recorded Mathlib modules. These give
`pullbackSpecIso`, `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`,
`Module.FaithfullyFlat`, `Module.Free.of_divisionRing`, `RingHom.FaithfullyFlat`,
`RingHom.Flat`, `Algebra.TensorProduct`'s algebra operations and universal property,
`TensorProduct` and its induced linear maps, `Concrete.isColimit_exists_rep`,
`Concrete.isColimit_rep_eq_iff_exists`, the algebra/under-category equivalence and connected
forgetful-colimit preservation, filtered-colimit preservation for rings and modules,
and the tensor-right adjunction with `isColimitOfPreserves`. Proof-only imports are ordinary
imports; statement imports are public. No proof dependency is omitted for an import cycle.

Edge cases checked mathematically before finalizing:

- The zero ring has empty spectrum, hence cannot satisfy any geometric irreducibility
  hypothesis. It is not unnecessarily excluded by an added `Nontrivial` instance.
- A field and the dual numbers `k[ε]/(ε²)` satisfy geometric irreducibility. The latter
  checks that no reducedness or domain condition has slipped into either statement.
- `k × k` has reducible spectrum and does not satisfy the hypotheses.
- Singleton directed diagrams give the original algebra, as expected. An empty index type
  is excluded exactly as in the node. Indices need not have a least or greatest element.
- The two-stage directed diagram `k[ε]/(ε²) → k` given by the quotient has a noninjective
  transition and satisfies the clause; its colimit is `k`. Thus transition injectivity
  must not be imposed. The statement does not impose it.
- Nothing in the signatures restricts the characteristic or the size of generators.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: “Geometric irreducibility of a field algebra is preserved under
  injective algebra maps and directed colimits”. Eight hits, headed by
  `Algebra.IsGeometricallyReduced.of_injective` and `.of_forall_fg`. They concern geometric
  reducedness, and none states either requested geometric irreducibility closure assertion.
- `msearch.py`, Loogle: `GeometricallyIrreducible, CommAlgCat`. Zero hits; the service reported
  the unqualified name `GeometricallyIrreducible` unknown.
- `msearch.py`, Mathlib grep:
  `geometric.*irreducib|irreducib.*(colimit|directLimit|subalgebra)`.
  Sixteen hits in geometrically irreducible/integral/reduced scheme files and affine space;
  none states these closure assertions.
- `rg` on upstream `WeilConjectures` and project `lean/Sheaf`:
  `geometric.*irreducib|[Gg]eometricallyIrreducible`. Upstream geometric image and
  smooth/connected results and applications were found, but no exact closure assertion.
- `rg` for the exact blueprint id in upstream: no matches.
- `rg` for both proposed declaration names in Mathlib, upstream, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no matches. There is no duplicate declaration.

Compilation uses only the authorized `scompile.py` wrapper. Initial elaboration exposed an
incorrect preorder import path and an ambiguous coercion around `colimit F`; both were repaired
by using `Mathlib.CategoryTheory.Category.Preorder` and annotating the colimit category.

No statement correction, disputed statement, unusable dependency interface, or new notion
was found. The maintainer performs the independent review after this direct worker delivery.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

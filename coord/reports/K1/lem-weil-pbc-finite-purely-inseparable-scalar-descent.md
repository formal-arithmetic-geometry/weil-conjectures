## Worker report

The module `Sheaf.FieldTheory.FinitePurelyInseparableScalarDescent` states
`Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct`, with one `sorry`
and no new definitions. The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- Fields `K ⊆ L`: `(K : Type u) (L : Type v)`, `[Field K] [Field L]
  `[Algebra K L]`. The structure map is `algebraMap K L`, automatically injective.
- Commutative `K`-algebra `B`: `(B : Type w) [CommRing B] [Algebra K B]`.
- The algebra `L ⊗_K B`: `L ⊗[K] B`, with Mathlib's tensor-product ring
  structure and `Algebra.TensorProduct.leftAlgebra`. Its structure map is
  `l ↦ l ⊗ₜ 1` by `Algebra.TensorProduct.algebraMap_def`.
- It is a field: `(hfield : IsField (L ⊗[K] B))`. This predicate concerns the
  existing ring operations; it does not introduce potentially incompatible operations.
- It is finite over `L`: `[Module.Finite L (L ⊗[K] B)]`, finite-dimensional
  because `L` is a field.
- It is purely inseparable via that same structure map:
  `[IsPurelyInseparable L (L ⊗[K] B)]`.
- `B` is a field: the first conjunct `IsField B`.
- The original structure map makes `B` finite purely inseparable over `K`:
  `Module.Finite K B ∧ IsPurelyInseparable K B` uses the given `[Algebra K B]`.
- Dimension equality: `Module.finrank K B = Module.finrank L (L ⊗[K] B)`.
  Finiteness occurs explicitly on both sides, so finrank is actual dimension.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with
  fields as specified by its `mathlib_match`.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, and `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`. The recorded conjunction is usable
  directly. Pure inseparability is defined for rings and specializes correctly
  under `IsField`; `IsField.toField` extends the existing ring operations.
  `isPurelyInseparable_iff_pow_mem` identifies it with the Stacks definition.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`.

Edge cases checked before writing: the zero algebra `B` gives a zero tensor
product, hence cannot satisfy `hfield`; no nontriviality assumption on `B`
is added. Characteristic zero forces the extensions to be trivial, with
dimension one. Positive characteristic permits exponent `p^0 = 1` and
includes the trivial extension. No finiteness or separability is imposed on
`L/K`, and no initial field or domain hypothesis is imposed on `B`.
The three carriers have separate explicit universes. No empty-basis case
is lost: the field hypothesis forces nonzero `B`.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanSearch, `finite purely inseparable field extension descends from L tensor K B to B`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- LeanFinder, `If L tensor over K B is a finite purely inseparable field extension of L then B is a finite purely inseparable field extension of K with the same dimension`:
  eight hits on field towers, intermediate fields and inseparable degrees;
  none states scalar descent.
- Loogle, `IsPurelyInseparable, TensorProduct`: four hits on powers in
  tensor products and universal homeomorphisms, none states this descent.
- Mathlib grep, `IsPurelyInseparable.*TensorProduct|TensorProduct.*IsPurelyInseparable|finrank_baseChange|isField_of.*tensor`:
  nine hits, including `Module.finrank_baseChange` and the tensor-product
  power lemmas; only ingredients, no matching theorem.
- `rg` of `WeilConjectures` for `purely.?inseparable|scalar.?descent` and
  `IsPurelyInseparable`: universal-homeomorphism, residue-field and
  field-tower results, no matching descent theorem. Read the source extension
  `WeilConjectures/Mathlib/FieldTheory/PurelyInseparable/Basic.lean`;
  its main result is about connectedness under purely inseparable base change.
- `rg` of `lean/Sheaf/FieldTheory` for the same concepts: `FieldTower.lean`
  describes field towers, not scalar descent. Broader ring-theory searches
  give uses of `IsField`, not this theorem.
- Search for the exact node id throughout `WeilConjectures`: no hits.
- Search for the proposed declaration name in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

The literature checkout has no local Stacks text files on this machine.
Read the authoritative [Tag 07QG](https://stacks.math.columbia.edu/tag/07QG)
and [Tag 09HE](https://stacks.math.columbia.edu/tag/09HE) online instead.
The node's agent-written seven-step basis proof is included in the declaration
docstring, with each dependency identified. No statement correction or dispute
is needed, and no new node or dependency module is needed.

Validation: the server compiled the module cleanly in 1.4 seconds, exit code zero.
The delivery dry run is the final validation; independent second reading is
reserved for the second worker.

## Second reading by K1

I independently read the repository node, its three statement dependencies,
the sandbox node and Lean module, and the actual Mathlib declarations below.
No mismatch was found; the Lean module and node record are retained unchanged.
There are no new nodes, dependency modules, or statement corrections to review.

Source check: the local literature directory contains no Stacks `.tex` files.
I read the raw upstream `algebra.tex` at
`lemma-geometrically-regular-over-subfields` and `fields.tex` at
`definition-purely-inseparable`, as well as the rendered
[07QG](https://stacks.math.columbia.edu/tag/07QG) and
[09HE](https://stacks.math.columbia.edu/tag/09HE).
07QG uses a finite purely inseparable extension descended from a subfield;
the node isolates the algebraic descent justification. The ambient geometric
regularity and directed system belong to the application, not hypotheses of
this descent lemma. There is no missing Noetherian, separability, perfection,
or characteristic hypothesis. The source's displayed tensor identification
has an apparent left-hand-side typo (`k_i`); this does not affect the isolated
node, whose mathematical assertion is correct by its basis argument.
09HE includes the arbitrary-characteristic convention after the definition.

The node's complete object/hypothesis/conclusion list and Lean correspondence:

1. Fields K and L, with K included in L: `(K : Type u) (L : Type v)`,
   `[Field K] [Field L] [Algebra K L]`. The dependency
   `def-pc-field-extension` records precisely Mathlib `Algebra`; I read its
   class in `Algebra/Algebra/Defs.lean:95`. Its unital map is injective for
   fields, so an arbitrary algebra structure expresses exactly the inclusion.
   Verdict: exact, with no restriction on L/K.
2. A commutative K-algebra B: `(B : Type w) [CommRing B] [Algebra K B]`.
   No field, domain, or nontriviality of B is assumed. Verdict: exact.
3. The ring A = L tensor_K B and the specified L-algebra map l to l tensor 1:
   `L ⊗[K] B`. I read `Algebra.TensorProduct.leftAlgebra` and
   `algebraMap_def` in `RingTheory/TensorProduct/Basic.lean:281,291`:
   with S = A = L this is includeLeftRingHom, exactly the required map.
   Its module action is the action on the left factor. Verdict: exact.
4. A is a field: `(hfield : IsField (L ⊗[K] B))`.
   I read `IsField` and `IsField.toField` in `Algebra/Field/IsField.lean`:
   the predicate gives nontriviality and inverses for the existing ring,
   and the constructed Field preserves that ring. No incompatible field
   operations are being quantified over. Verdict: exact.
5. A/L is finite: `[Module.Finite L (L ⊗[K] B)]`.
   I read `Module.Finite` in `RingTheory/Finiteness/Defs.lean:117`:
   finite generation of the module, equivalent to finite dimension over L.
   This is the finite clause of the recorded dependency
   `def-weil-pbc-finite-purely-inseparable-extension`. Verdict: exact.
6. A/L is purely inseparable via the map in item 3:
   `[IsPurelyInseparable L (L ⊗[K] B)]`.
   I read the class at `FieldTheory/PurelyInseparable/Basic.lean:107` and
   `isPurelyInseparable_iff_pow_mem` at line 211. Under the field hypothesis
   its ring-general formulation is exactly the 09HE power criterion,
   including characteristic zero via exponential characteristic one.
   It uses the same inferred leftAlgebra, not the right-factor map.
   Verdict: exact; instance binders are propositions, not extra hypotheses.
7. B is a field: first conjunct `IsField B`, for the given commutative ring.
   Verdict: exact, and stronger assumptions on B were not substituted.
8. The original K-algebra map makes B finite purely inseparable over K:
   `Module.Finite K B ∧ IsPurelyInseparable K B`, following `IsField B`.
   Both use the original `[Algebra K B]`; combined with the first conjunct,
   these are precisely the dependency's field-extension specialization.
   Verdict: exact; no new map or existentially chosen algebra structure.
9. Equality of dimensions: `Module.finrank K B =
   Module.finrank L (L ⊗[K] B)`. I read the recorded dependency
   `def-weil-vector-space-dimension` and the definition of finrank in
   `LinearAlgebra/Dimension/Finrank.lean:62`. The hypothesis and conclusion
   explicitly supply finiteness, so these natural numbers are the actual
   finite dimensions, not the convention for infinite rank. Verdict: exact.

Edge cases: the zero K-algebra is permitted as input but its tensor product
is zero, contradicting `hfield`; no unnecessary Nontrivial instance excludes
it in advance. An empty basis is likewise ruled out by the field hypothesis.
The trivial extensions (including L = K and B = K) are covered. In positive
characteristic the power criterion allows n = 0; no uniform exponent or
positive exponent is imposed. Characteristic zero forces dimension one and
surjectivity of the original structure map, as 09HE requires. Three independent
explicit universes u, v, w cover arbitrary carrier sizes; every type and
universe is bound and autoImplicit is false. No scheme, open set, or external
index set occurs, so empty-scheme cases do not arise.

Independent searches, with queries different from the first reader's:

- LeanSearch through msearch: `A commutative algebra whose scalar extension
  is a finite radicial field extension is itself a finite radicial field
  extension`. Service returned Internal Server Error, recorded unavailable;
  no absence verdict is inferred from this search.
- Loogle through msearch: `IsField, TensorProduct`. Ten hits concern linear
  disjointness, algebraicity of a factor, and constructing a tensor field.
  None descends the field, finite, and purely inseparable clauses together.
- LeanFinder through msearch: `Descent of finite radicial field extensions
  under extension of scalars`. Eight hits concern PRadical criteria,
  intermediate-field finite generation, unramified composition, geometric
  reducedness, and tensor fields; none states the node.
- rg on Mathlib FieldTheory and RingTheory and on both the whole source
  `WeilConjectures` tree and project `lean/Sheaf`, using `radicial`,
  `scalar.?descent`, and purelyInseparable with tensor/baseChange in both
  orders, plus the broader `IsPurelyInseparable` search. No duplicate was
  found. Read the related upstream
  `RingHom.IsPurelyInseparable.of_comp_eq` in
  `WeilConjectures/Mathlib/RingTheory/Etale/FiniteSplitting.lean:49`:
  it assumes three fields and powers landing in the original source image;
  it neither descends fieldness nor finiteness from a tensor product.
  Read the source PurelyInseparable/Basic.lean connectedness theorem: it is
  about idempotents over a separably closed field, not this statement.
  `Module.finrank_baseChange` and the Mathlib tensor-product power lemmas
  are ingredients, not declarations of this node.
- The proposed declaration name has no collision in the repository, source,
  Mathlib, or `dag/lean_names_upstream.json`.

Conventions/proof review: one named theorem with proof `by sorry`, no
hollow definitions or additional proved facts. The module and declaration
both name 07QG, 09HE and the exact blueprint id. The docstring follows all
seven DAG proof steps, with dependency ids: nonzero B, basis through 1,
scalar-extended basis and finite dimension, injection/domain, fieldness,
powers in positive characteristic, and the characteristic-zero case.
Imports serve purely inseparability/tensor algebra, IsField, and finrank.
All Lean lines are at most 100 characters. The node's `lean.statement`
is verbatim the theorem signature up to `:=`, with no unbound variables.

Second-reader validation: scompile compiled the module cleanly on the server
in 1.4 seconds, exit code 0, with no diagnostic warnings. No Lean or node
repair was necessary; the only addition is this independent review report.

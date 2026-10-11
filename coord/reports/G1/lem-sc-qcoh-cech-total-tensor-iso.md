## Worker report

The module `Sheaf.Algebra.Homology.TensorKunneth` states
`HomologicalComplex.tensor_kunneth`, with proof `sorry`. It states existence of a linear
isomorphism and specifies its action on every pure tensor of cohomology classes by
cocycle representatives. This expresses both well-definedness and the isomorphism
assertion without choosing representatives or defining a map using postponed data.
No statement correction or disputed statement was needed.

The source read was Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`, especially
`equation-kunneth-on-cech`, in the local Stacks mirror
`/home/ubuntu/c1-stacks-review/varieties.tex`, lines 5442–5541. The repository's literature
file is absent on this machine. The three-step linear algebra proof is reproduced in
the theorem docstring, including the homotopy signs and the boundary calculation.

Hypotheses and clauses, in order:

- The field is `{k : Type uk} [Field k]`. The dependency `def-weil-field` has Mathlib
  match `Field`, whose full signature and docstring were read in
  `Mathlib.Algebra.Field.Defs`, lines 169–180. It is used through Mathlib, without a
  dependency replacement.
- `A B : CochainComplex (ModuleCat.{vm} k) ℤ` are integer-indexed vector spaces with
  linear differentials squaring to zero. This is Mathlib's `HomologicalComplex` with
  shape `ComplexShape.up ℤ`, not a new complex definition. Universes `uk` and `vm`
  are explicitly bound and independent; the two carrier families can be placed in
  their common carrier universe. In particular a small field and large vector spaces
  are allowed.
- The two bounded-below hypotheses are `hA` and `hB`: each says there exists an
  integer lower bound below which the corresponding terms are `IsZero`. In
  `ModuleCat` this means the vector space is zero, without requiring literal type
  equality with a chosen zero object. No finite-dimensionality or uniform common
  lower bound is imposed.
- `A.cycles p`, `A.iCycles p`, and `A.homologyπ p` render the kernel, its inclusion,
  and its quotient by incoming boundaries; `A.homology p` renders `H^p(A)`.
  The same declarations apply to `B`. Their definitions and docstrings were read in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, lines 65–105.
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` provides the module homology
  interface; its `moduleCatCyclesIso` and `moduleCatHomologyIso` identify the
  categorical objects with the kernel and kernel/image quotient.
- `mapBifunctor A B (ModuleCat.tensorBifunctor k) (ComplexShape.up ℤ)` is the total
  tensor complex. Mathlib's `HomologicalComplex.mapBifunctor` and
  `HomologicalComplex.ιMapBifunctor` were read in `Mathlib.Algebra.Homology.Bifunctor`,
  lines 110–135. Its totalization takes coproducts over pairs with sum equal to the
  target degree. Module coproducts are direct sums. The differential is the sum of
  `D₁` and `D₂`; `d₁_eq`, `d₂_eq`, `ι_D₁`, and `ι_D₂` at lines 237–263 identify the
  restrictions to the summands. `Mathlib.Algebra.Homology.ComplexShapeSigns`, lines
  155–162 and 182–192, gives the first sign as 1, the second sign as `p.negOnePow`,
  and the degree as addition. Thus this is exactly the stated signed differential,
  also in negative degrees. `ModuleCat.tensorBifunctor` supplies the missing
  independent-universe tensor functor; it uses existing tensor products and maps.
- `n : ℤ` ranges over every degree. The domain of `e` is the `DirectSum` over
  `{pq : ℤ × ℤ // pq.1 + pq.2 = n}` of
  `(A.homology pq.1) ⊗[k] (B.homology pq.2)`. The codomain is the degree-`n` homology
  of that total complex. `≃ₗ[k]` states that the map is a linear isomorphism.
- For every degree pair `s`, and every pair of cycles `a` and `b`, the existential
  `z` has underlying tensor equal to the summand inclusion of
  `A.iCycles ... a ⊗ₜ[k] B.iCycles ... b`. This explicitly includes the assertion
  that a tensor of cocycles is a cocycle; it is not merely a conditional equation.
- The final equation says that `e` applied to the direct-sum inclusion
  `DirectSum.lof k _ _ s` of `[a] ⊗ [b]` equals `[z]`. Thus it is the specific map
  `[a] ⊗ [b] ↦ [a ⊗ b]`, rather than an arbitrary isomorphism. `iCycles` is injective
  and `homologyπ` is surjective in module homology, so the equation covers every
  pure tensor of classes and uniquely specifies the linear map. Since `e` is a
  linear map on the quotient spaces, changing representatives leaves its value
  unchanged. Pure tensors and the direct-sum inclusions generate the domain.

Edge cases checked: either complex zero; complexes concentrated in arbitrary single
integer degrees; negative degrees and arbitrary negative lower bounds; degrees below
the sum of the bounds; arbitrary-dimensional terms; characteristic two, where the
signs agree but the mixed terms still cancel; and arbitrary positive characteristic.
The index subtype itself is not artificially made finite, although only finitely
many summands can be nonzero in a fixed degree under the bounded-below hypotheses.
No bounded-above condition, finite basis, nonzero term, or excluded degree is imposed.

Searches actually run (recorded by `msearch.py` in `searches.jsonl`):

- LeanSearch: `Kunneth formula tensor product cochain complexes over a field`:
  unavailable, HTTP Internal Server Error; not counted as evidence of no match.
- LeanFinder: `homology tensor product complexes canonical map from tensor product
  of homology`: eight hits, including `HomologicalComplex.tensorObj`, `tensorHom`,
  `HasTensor`, and `ιTensorObj`; no Kunneth theorem.
- Loogle: `HomologicalComplex.homology, TensorProduct`: zero hits.
- Mathlib grep: `Kunneth|homology.*tensor|tensor.*homology` in `Algebra/Homology`:
  zero hits.
- Project grep for `Kunneth|kunneth.*[Cc]omplex|[Cc]omplex.*kunneth` in the source
  and `lean/Sheaf`: hits on the geometric six-functor Kunneth comparisons, not this
  field-linear complex theorem. Source grep for the item ID: zero hits.
- `tools/lean_names_upstream.py show` was consulted; no attachment for this item.
  Full-name grep for `tensor_kunneth` in Mathlib, source, project, and the upstream
  name list found no existing declaration.

All variables and universes are explicitly bound. Final combined server compilation
of the two modules succeeded in 1.8 seconds with no errors or warnings. An initial
same-universe monoidal draft was replaced after an explicit server check showed that
`ModuleCat.{1} ℚ` has no Mathlib monoidal instance. The final statement uses the
independent-universe bifunctor and no longer has that restriction. Every theorem
proof in the delivery is `sorry`; the new definition's objects and maps are explicit.

## New nodes

`def-sc-module-tensor-bifunctor` defines the tensor bifunctor on `R`-modules with
independent scalar and carrier universes. Its source is Stacks Algebra, Tag 00CX,
`lemma-tensor-product`, using the universal property and the generation by pure
tensors, read at `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 1703–1768. Its
statement cites `def-weil-pbc-module-tensor-product`, whose Mathlib match is
`TensorProduct`; the recorded signatures for `TensorProduct`, `mk`, `lift`, `lift.tmul`,
`ext'`, `LinearMap.rTensor`, `rTensor_tmul`, and `rTensorHom` were read in their recorded
files. The new module imports and uses the existing `TensorProduct` and
`TensorProduct.map`; it does not define another tensor product.

The new module is `Sheaf.Algebra.Category.ModuleCat.TensorBifunctor`, declaring
`ModuleCat.tensorBifunctor`. Its explicit object is `ModuleCat.of R (M ⊗[R] N)`;
its maps are `ModuleCat.ofHom` of the existing tensor maps with one identity factor.
The named postponed proofs `tensorBifunctor_id`, `tensorBifunctor_comp`, and
`tensorBifunctor_naturality` supply the functor laws; `tensorBifunctor_preservesZero`
and `tensorBifunctor_obj_preservesZero` supply the two zero-preservation instances.
Each has a complete pure-tensor verification in its docstring and belongs to this
new definition node. No data field is `sorry`. Each identity, composition,
commutation, and zero-preservation clause of the new node is respectively rendered
by these named statements. The functor definition uses them only for proof fields.
The edge cases of the zero ring, zero modules, and independent universes are allowed.

Searches for this new notion: LeanSearch query `tensor product bifunctor category
modules arbitrary universe independent scalar ring universe` was unavailable with
Internal Server Error. LeanFinder query `tensor product bifunctor ModuleCat arbitrary
universe modules ring` gave eight hits on the same-universe monoidal construction.
Mathlib grep `tensorBifunctor|curriedTensor|def tensorObj` in
`Algebra/Category/ModuleCat` gave three hits, on presheaf tensors and semimodule tensors.
The full monoidal module was read: its instances fix the module universe to the
scalar universe, so they do not provide this bifunctor. Full-name source and project
grep found no `ModuleCat.tensorBifunctor`; Mathlib's localization namespace has an
unrelated `tensorBifunctor`. DAG grep for `tensor bifunctor|tensorBifunctor|tensor functor`
gave nodes about derived tensor products and sheaf tensors, not this functor.
`tools/blueprint_refs.py search 'tensor product of modules'` and `search 'tensor bifunctor'`
both returned zero blueprint matches. The ancestor command returned
`thm-sc-theorem-of-cube`; the new node records its exact field-linear Kunneth place
and the item's via chain. The item gains only this new definition node in `stmt_deps`.

## Second reading by G1

Independent reading of both delivered nodes and both modules against Stacks
`varieties.tex`, section Kunneth formula I, Tag 0BED, especially
`equation-kunneth-on-cech`, and `algebra.tex`, conventions and Tag 00CX.
The local source copies are `/home/ubuntu/c1-stacks-review/varieties.tex` and
`/home/ubuntu/c1-stacks-review/algebra.tex`. Verdict: the Lean says exactly what
this algebraic node says. No mathematical or signature repair was needed.

Object, hypothesis, and conclusion checklist:

1. A field k: `{k : Type uk} [Field k]`, matching `def-weil-field` and
   `Mathlib.Algebra.Field.Defs.Field`. Its commutative-ring and nontrivial
   division-ring structures give precisely the field in the node. PASS.
2. Integer-indexed cochain complexes A and B of vector spaces:
   `(A B : CochainComplex (ModuleCat.{vm} k) ℤ)`. The up shape gives linear
   differentials from p to p+1 with consecutive composite zero. PASS.
3. Each complex bounded below: `hA` and `hB` separately quantify an integer
   lower bound and require `IsZero` below it. Zero objects of ModuleCat are
   exactly zero vector spaces; there is no extra boundedness or dimension
   requirement. PASS.
4. Cycles, boundaries, and cohomology: `cycles`, `iCycles`, `homology`, and
   `homologyπ` use the existing Mathlib homological-complex interface.
   I opened `ShortComplex.HomologicalComplex` and `ShortComplex.ModuleCat`:
   `moduleCatLeftHomologyData` has kernel object K, quotient K/range object H,
   subtype inclusion i, and quotient projection π; `moduleCatCyclesIso` and
   `moduleCatHomologyIso` identify these with the categorical objects. PASS.
5. Total tensor complex: `mapBifunctor A B (ModuleCat.tensorBifunctor k)
   (ComplexShape.up ℤ)`. I opened `Homology.Bifunctor`, `TotalComplex`, and
   `ComplexShapeSigns`. Totalization uses coproducts over p+q=n (direct sums
   in modules); the up-integer shape uses π(p,q)=p+q, ε₁=1, ε₂=p.negOnePow.
   The bifunctor's objects are the existing tensor products and its maps are
   tensor maps. Thus the differential is d_A tensor 1 + (-1)^p 1 tensor d_B,
   including negative p. No unavailable totalization instance is assumed
   as an extra theorem binder. PASS.
6. Every integer degree: `(n : ℤ)` after both boundedness hypotheses. PASS.
7. Source of the canonical map: the displayed `DirectSum` over the subtype
   `{pq : ℤ × ℤ // pq.1 + pq.2 = n}`, with summands
   `A.homology p ⊗[k] B.homology q`. PASS.
8. Target and isomorphism: `∃ e : ... ≃ₗ[k] (...).homology n` asserts a
   k-linear isomorphism with exactly the target total-complex cohomology.
   This is not an arbitrary isomorphism, because the remaining clause fixes
   its action on all pure tensors of classes. PASS.
9. Well-defined class map: for every degree pair s and cycles a,b, `∃ z`
   asserts that their tensor summand inclusion is the underlying vector of
   a cycle. The first conjunct uses `iCycles` and `ιMapBifunctor` to identify
   this cycle; the second says e sends `lof s ([a] tensor [b])` to `[z]`.
   The injectivity of iCycles uniquely determines z, and the surjectivity of
   homologyπ covers all classes. Linearity and generation by pure tensors
   then specify exactly the class map and its independence of representatives.
   Quantifier order is: complexes, bounds, degree, isomorphism, degree pair,
   representatives, tensor cycle. PASS.

Source hypotheses: the geometric Stacks lemma assumes quasi-compact schemes
with affine diagonal and quasi-coherent sheaves to identify their cohomology
with Cech complexes. This node isolates the field-linear algebra step, with
arbitrary bounded-below vector-space complexes; it does not assert the Cech
comparison map is an isomorphism of complexes (Stacks explicitly warns it
is not). Consequently no scheme, separation, finiteness, or sheaf instance
belongs in this algebraic theorem. The node's three complement/contraction/
class-map proof steps are all present in its theorem docstring.

Edge cases: zero A or B and zero terms are allowed; below the sum of the
bounds all summands vanish without requiring an empty type of degree pairs.
The pair index is infinite, and `DirectSum` enforces finite support rather
than silently taking a product. The empty scheme yields zero complexes in
applications and is not excluded. Degree zero, negative degrees and lower
bounds, characteristic two and other positive characteristics all remain
covered. There is no characteristic assumption or finite-dimensionality.
`uk` and `vm` are independent bound universes; complexes from different
carrier universes can be placed in their common universe. No unbound
variable or implicit universe was found.

New-node review (H12): `def-sc-module-tensor-bifunctor` is a genuine curried
functor on independent-universe module categories, not a second tensor
product. I checked all its fields against brief-stage2 section 5, including
its existing tensor-product dependency, empty proof fields, creation record,
blueprint ancestry, chapter/unit, search records, and complete Lean record.
Tag 00CX's universal bilinear map and generation by pure tensors yield the
specified identity, composition, commuting-variable and zero-map laws;
Stacks' ring convention is commutative with 1 and permits the zero ring.
The module's `tensorBifunctor_id`, `_comp`, `_naturality`, `_preservesZero`,
and `_obj_preservesZero` state these laws with `sorry` proofs and complete
pure-tensor arguments in their docstrings. The functor data are explicit
`ModuleCat.of`, `TensorProduct`, and `TensorProduct.map`, with only proof
fields supplied by the named theorems. H5 and H6 pass. There are no
replacement dependency modules and no statement correction to review.
I opened the tensor-product dependency node and its recorded Mathlib
`TensorProduct` definition and `TensorProduct.map` signature as well.

Independent searches (different wording from the first reader):

- `msearch.py ... leanfinder "cohomology cross product linear equivalence
  tensor cochain field"`: eight hits, primarily group-cohomology cochain
  and cocycle identifications; none states this Kunneth theorem.
- `msearch.py ... loogle "TensorProduct.map"`: existing tensor-map API;
  no complex Kunneth equivalence (the map is reused by the definition).
- `msearch.py ... leanfinder "ModuleCat tensor product functor different
  universes"`: eight hits on ModuleCat's monoidal API and FGModuleCat.
  I opened `ModuleCat/Monoidal/Basic.lean`, whose documentation explicitly
  fixes ring and module universes equal, and whose actual instances are
  on `ModuleCat.{u} R` for `R : Type u`. These do not supply the new notion.
- `msearch.py ... grep "kunneth|Kunneth|tensorBifunctor"`: the returned
  tensorBifunctor is in the localization namespace and requires a monoidal
  input, not this independent-universe module functor.
- Direct `rg` in source `WeilConjectures`, project `lean/Sheaf`, Mathlib
  homology and ModuleCat modules, and DAG nodes, with
  `k[uü]nneth|homology.*tensor|tensor.*homology|tensor.*bifunctor`:
  geometric Kunneth, derived tensor models and same-universe monoidal
  totalizations exist; no duplicate of either delivered declaration.
  The landed mixed tensor uses scalar extension and is a different functor.
  The worker's LeanSearch unavailability remains explicitly recorded,
  not counted as a negative search result.

Mismatches found: none. Changed only this second-reading report; kept the
correct Lean and node signatures intact. All declarations have source and
blueprint docstrings, every theorem has only a postponed proof, and the
node signatures were checked verbatim against their Lean files. Combined
server compilation of both modules is the validation for this delivery.

## Reviewer fix (R-qct1327)

H12/H4: the new node def-sc-module-tensor-bifunctor (`ModuleCat.tensorBifunctor`) is a second
definition of the tensor bifunctor on modules, a notion the project already records as
`CategoryTheory.MonoidalCategory.curriedTensor` on def-pc-tensor-complex-sheaves and uses on
`ModuleCat.{u} A` in landed files (MixedTotalTensor, KFlatDerivedTensorAssociator,
OpcyclesTorSurjection, IsKFlatTilde). The node states nothing about universes, so the
independent-universe generality is not needed. The node is dropped (`--drop-nodes`) with its
module, and the theorem is restated with `{k : Type u} [Field k]`, complexes in
`ModuleCat.{u} k` and the total complex `mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
(ComplexShape.up ℤ)`; everything else (bounded-below hypotheses, direct sum over p+q=n,
linear equivalence pinned on pure tensors of classes via iCycles/homologyπ) unchanged.
Compiled in lean/.sandbox/L.

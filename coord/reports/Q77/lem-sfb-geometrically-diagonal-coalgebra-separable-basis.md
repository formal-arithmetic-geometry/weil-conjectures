## Worker report

The module `Sheaf.RingTheory.GeometricallyDiagonalCoalgebraSeparableBasis` states
`Coalgebra.geometricallyDiagonal_separableClosure_basis`, with its proof `sorry`.
It introduces no definitions or auxiliary theorems. Only the item's `lean` field changes.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The separable closure is `{ks : Type v} [Field ks] [Algebra k ks]
  [IsSepClosure k ks]`. Mathlib's `IsSepClosure` supplies separable closedness and
  algebraic separability, hence algebraicity, exactly as the recorded dependency's
  upstream module describes it.
- The algebraic closure is `{kbar : Type w} [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]`. This is the arbitrary fixed algebraic closure permitted
  by the dependency's Mathlib match, rather than a restriction to a concrete implementation.
- The inclusion ks into kbar is `[Algebra ks kbar] [IsScalarTower k ks kbar]`.
  A field algebra map is injective; the tower says this inclusion agrees with the
  original k-structures. These are the node's inclusion and its compatibility,
  not an extra mathematical assumption.
- The coalgebra C is `{C : Type t} [AddCommGroup C] [Module k C] [Coalgebra k C]`.
  The last class has linear `comul`, `counit`, `coassoc`,
  `rTensor_counit_comp_comul`, and `lTensor_counit_comp_comul`, exactly the stated data
  and three identities. No cocommutativity or bialgebra structure is assumed.
- The two scalar extensions are `kbar ⊗[k] C` and `ks ⊗[k] C`, with their canonical
  extended coalgebras from `TensorProduct.instCoalgebra`. Its implementation and
  `comul_tmul`/`counit_tmul` were read: for a scalar a the comultiplication is obtained
  by scalar extension of Delta, and the counit sends a tensor c to a epsilon(c).
- `IsGroupLikeElem F c` is Mathlib's conjunction of the exact equations
  `counit c = 1` and `comul c = c ⊗ₜ[F] c`.
- `hgeom` quantifies over a `Module.Basis ι kbar (kbar ⊗[k] C)` and requires every
  basis vector to be group-like. The index universe `max w t` is the universe of
  that tensor-product space. This loses no basis: every basis can be indexed by
  its image as a subtype of the vector space. Empty and infinite indices are allowed.
- The conclusion is existence of a `Module.Basis` indexed by the entire subtype
  `{c : ks ⊗[k] C // IsGroupLikeElem ks c}`, with `b c = c.val` for every index.
  This is exactly the assertion that all group-like elements, with their actual
  underlying values, form a basis; there is no enumeration or omitted element.
- No finite-dimensionality hypothesis appears, nor any restriction on characteristic
  or relation among the four explicitly bound universes.

Dependency declarations used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pd-separable-closure`: import
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`, whose recorded declaration
  `IsSepClosure.exists_intermediateField_mem` and docstring were read in full.
  The module explicitly identifies the notion as Mathlib's `IsSepClosure`, used here.
- `def-weil-algebraic-closure`: `IsAlgClosure`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as expressly permitted by its Mathlib match.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` (Defs), `TensorProduct.lift`
  (Basic), `LinearMap.rTensor` (Map); their signatures and source were read. The
  public coalgebra tensor-product module imports the tensor-product infrastructure.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, used for
  k/ks, k/kbar and ks/kbar.

The file also has plain proof imports for the stated proof dependencies:
`Sheaf.RingTheory.FiniteSubcoalgebra`;
`Mathlib.RingTheory.Flat.Basic` (field freeness/flatness and tensor exactness);
`Mathlib.RingTheory.Artinian.Module` (finite algebras Artinian, reduced Artinian
residue-field product);
`Mathlib.LinearAlgebra.TensorProduct.Pi`;
`Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced`.
The separably closed trivial-extension result is already in the public upstream
field-theory import. `lem-sfb-finite-coalgebra-dual-base-change` has no recorded
Lean declaration at the read snapshot, so there is no module to import for it yet.
It is only a proof dependency; the current statement requires no part of its interface.
The theorem docstring carries all eight proof steps, including that dependency.

Source checked: the actual Milne PDF, printed pp.237–238, Theorem 12.18 and
Corollary 12.19, using pdftotext. The finite-coalgebra reduction in the node extends
Milne's coordinate-coalgebra argument without adding a group/Hopf assumption.
No statement correction or disputed statement was needed.

Edge cases checked before writing:

- C = 0: epsilon is zero, hence there are no group-like elements over a field;
  both basis index sets can be empty. The conclusion gives the empty basis of zero.
- Infinite-dimensional C: all bases and group-like index types are unrestricted;
  the proof uses finite subcoalgebras per vector, never a global dimension bound.
- Imperfect fields and positive characteristic: no perfection assumption is used;
  ks need not equal kbar. Both closure classes retain their full generality.
- Already separably closed or algebraically closed k: identity algebra towers are
  allowed. Thus the identity-closure cases are included.
- The group-like predicate includes epsilon = 1; merely Delta(c) = c tensor c
  would incorrectly include zero, and is not used here.

Searches (all run through the prescribed wrapper; raw results in searches.jsonl):

- leanfinder, “A coalgebra with a group-like basis over an algebraic closure has a
  group-like basis over a separable closure”: eight hits, including
  `linearIndepOn_isGroupLikeElem` and unrelated field bases; no splitting theorem.
- loogle, `IsGroupLikeElem, Coalgebra, IsSepClosure`: zero hits.
- grep, `baseChange|BaseChange|IsGroupLikeElem|[Ss]eparab` in `RingTheory/Coalgebra`:
  five group-like-definition/documentation hits, no separable-splitting result.
  Direct reading of `Coalgebra/TensorProduct.lean` supplies the canonical scalar
  extension, so no helper definition is needed.
- leansearch, “coalgebra geometrically group-like basis separable closure”: eight
  hits on `SeparableClosure`, `IsSepClosure`, and their constructor/projections;
  none assert the desired coalgebra theorem.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `geometrically.diagonal|separable.basis|` the item id `|Coalgebra|IsGroupLikeElem`:
  coalgebra constructions, finite subcoalgebras/comodules and the downstream
  antiduality docstring, but no existing theorem of this statement.
- The upstream-name index was searched for coalgebra/the proposed theorem name;
  no matching theorem was found. `Coalgebra.geometricallyDiagonal_separableClosure_basis`
  is a new declaration, while every notion in its type is an existing Mathlib notion.

Validation: scompile.py compiled the file in sandbox and library modes cleanly.
The only postponed proof is the named item theorem; no data is postponed.

## Second reading by Q77

(Written by the maintainer's independent second reader, review of delivery 6bf3284c, 2026-10-24.
The delivered section was a self-check by the same worker, so it is replaced here.)

Node statement, clause by clause, against `Coalgebra.geometricallyDiagonal_separableClosure_basis`:

1. Field k [def-weil-field]: `{k : Type u} [Field k]`. OK.
2. Separable closure k^s [def-pd-separable-closure]: `{ks : Type v} [Field ks] [Algebra k ks]
   [IsSepClosure k ks]`. Mathlib `IsSepClosure` is separably closed + algebraic separable, the
   node's notion (the recorded module `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` is about it). OK.
3. Algebraic closure k̄ [def-weil-algebraic-closure]: `{kbar : Type w} [Field kbar] [Algebra k kbar]
   [IsAlgClosure k kbar]`, the recorded mathlib_match. OK.
4. k^s ⊂ k̄: `[Algebra ks kbar] [IsScalarTower k ks kbar]`, a k-embedding (field maps are injective).
   Not a stronger assumption: such an embedding always exists, and the conclusion does not mention it. OK.
5. k-coalgebra C (Δ, ε, coassociativity, two counit identities): `[AddCommGroup C] [Module k C]
   [Coalgebra k C]`; no cocommutativity, bialgebra, Hopf or finiteness class. OK.
6. C_F = F ⊗_k C with scalar-extended structure [def-weil-pbc-module-tensor-product,
   def-pc-field-extension]: `kbar ⊗[k] C`, `ks ⊗[k] C` with Mathlib `TensorProduct.instCoalgebra`
   (S = R-algebra A = F, B = C; `comul_tmul`, `counit_tmul` read in
   Mathlib/RingTheory/Coalgebra/TensorProduct.lean), the same convention as the landed
   lem-sfb-finite-coalgebra-dual-base-change. OK.
7. Group-like: Mathlib `IsGroupLikeElem F c` = `counit c = 1 ∧ comul c = c ⊗ₜ c` (GroupLike.lean:37). OK.
8. Hypothesis "C_{k̄} has a k̄-basis of group-like elements": `∃ ι : Type (max w t), ∃ b : Basis ι kbar
   (kbar ⊗[k] C), ∀ i, IsGroupLikeElem kbar (b i)`. The index universe is that of the space itself,
   so no basis is excluded (re-index by the image). OK.
9. Conclusion "the set of all group-like elements of C_{k^s} is a k^s-basis": a `Basis` indexed by the
   full subtype `{c // IsGroupLikeElem ks c}` with `b c = c.val` for every c. This is exactly the set
   being a basis (not just some group-like basis). OK.
10. "No finite-dimensionality assumption": none present. OK.

Edge cases: C = 0 (no group-likes since ε = 0 ≠ 1; empty basis of 0 — covered); k separably
or algebraically closed (identity towers allowed); imperfect k, any characteristic; infinite
dimension; four independent universes u v w t, none forced equal; all variables bound.

Records: only the item's `lean` field changes (diffed against the side-live node); `lean.statement`
is a verbatim substring of the file starting at `theorem`; stmt_deps unchanged, every stmt_dep
notion is used as recorded. Module docstring and theorem docstring carry the Milne source place and
`(blueprint: lem-sfb-geometrically-diagonal-coalgebra-separable-basis)`; the theorem docstring
carries the node's eight proof steps. No definitions, nothing proved beyond `sorry`, no pro-étale
material. Imports exist in the live tree (`Sheaf.RingTheory.FiniteSubcoalgebra`,
`Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced`).

Searches: rg for `IsGroupLikeElem`, `geometricallyDiagonal` and the item id over lean/Sheaf and
lean/WeilConjectures: only the downstream antiduality docstring cites this node; Mathlib
RingTheory/Coalgebra has group-like independence (`linearIndepOn_isGroupLikeElem`) but no splitting
theorem. No duplicate. No mismatch found; the Lean is unchanged.

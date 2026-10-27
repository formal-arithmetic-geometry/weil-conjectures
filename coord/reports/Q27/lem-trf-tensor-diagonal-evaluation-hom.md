## Worker report

The module `Sheaf.RingTheory.TensorDiagonalEvaluation` states
`Algebra.TensorProduct.tensor_diagonal_evaluation_existsUnique`, with its sole theorem proof
`sorry`. It also constructs the source ring and its double pure tensors directly from Mathlib's
existing tensor product, tensor map, multiplication map, and ring structures. These are helpers
for the exact objects introduced in this node, not independent notions or alternate tensor
products. No node statement or dependency changes.

Source read: `literature/stacks-project/algebra.tex`, label
`lemma-geometrically-reduced-over-separable-algebraic` (Tag 0C2Y), especially the second proof
paragraph and its displayed identity
`K ⊗_{k'} A = (K ⊗_k A) ⊗_{k' ⊗_k k'} k'`. The node deliberately generalizes the evaluation
construction in this identity to arbitrary commutative base rings; this generalization is valid.
The five-step proof is included in the theorem docstring, including both balancing conditions,
finite-sum multiplicativity, and uniqueness without imposing linearity on competing ring maps.

Hypotheses and clauses, individually:

- A commutative ring k: `(k : Type u) [CommRing k]`.
- A commutative k-algebra L: `(L : Type v) [CommRing L] [Algebra k L]`.
- Commutative L-algebras B and C: `(B : Type w) (C : Type x)`, their `CommRing` instances,
  and `[Algebra L B] [Algebra L C]`.
- B and C regarded as k-algebras by restriction: `[Algebra k B] [Algebra k C]` with
  `[IsScalarTower k L B] [IsScalarTower k L C]`. The tower requirements express precisely
  compatibility with the specified L-actions, not flatness or an additional algebraic condition.
  Every L-algebra admits these instances via `Algebra.restrictScalars` and
  `IsScalarTower.restrictScalars`; no ring is excluded.
- Tensor products and multiplication/unit: Mathlib `TensorProduct`, `TensorProduct.tmul`, and
  `Algebra.TensorProduct.instCommRing`, whose multiplication is factorwise and whose unit is
  `1 ⊗ 1`. The source ring's named instance uses exactly that existing structure.
- R = L tensor_k L: `L ⊗[k] L`, used literally as the outer tensor's coefficient ring.
- D = B tensor_k C: `B ⊗[k] C`, used literally as its first factor.
- ψ: `tensorDiagonalScalarMap k L B C`, defined using `Algebra.TensorProduct.map` on
  `IsScalarTower.toAlgHom k L B` and `IsScalarTower.toAlgHom k L C`. On `s ⊗ t` it sends
  the two factors to `(algebraMap L B s) ⊗ (algebraMap L C t)`, exactly the prescribed formula.
- The R-algebra structure of D: the actual `.toRingHom.toAlgebra` of this ψ, installed in
  `tensorDiagonalBaseChange`, its ring instance, and `tensorDiagonalPureTensor`.
- μ and the R-algebra structure of L: `(Algebra.TensorProduct.lmul' k (S := L)).toRingHom.toAlgebra`.
  Mathlib's `lmul'_apply_tmul` gives μ(s tensor t) = st. This is the second installed structure.
- The source D tensor_R L: `tensorDiagonalBaseChange k L B C` is a transparent construction
  of exactly `(B ⊗[k] C) ⊗[L ⊗[k] L] L` with those two actions. Its helper does not choose
  an object from an existence theorem or introduce an arbitrary map or algebra structure.
- A unique unital ring homomorphism β: `∃! β : tensorDiagonalBaseChange k L B C →+* B ⊗[L] C`.
  `RingHom` preserves 1, multiplication, addition and 0. It imposes no extra R-linearity.
- The formula for every b,c,λ: `∀ (b : B) (c : C) (l : L),
  β (tensorDiagonalPureTensor k L B C b c l) = (l • b) ⊗ₜ[L] c`.
  The helper is exactly `(b ⊗ₜ[k] c) ⊗ₜ[L ⊗[k] L] l`; scalar multiplication on B is its
  given L-algebra action, so `l • b = (algebraMap L B l) * b`.
- No other conditions: there is no `Nontrivial`, field, injectivity, finite-generation,
  flatness or reducedness binder. Universes u,v,w,x are independent and explicitly bound.

Dependency declarations read and used: the only dependency,
`def-weil-pbc-module-tensor-product`, is a Mathlib leaf. Its recorded declaration is
`TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`, together with the clause matches
`TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.lift.tmul`, `TensorProduct.ext'`,
`LinearMap.rTensor`, `LinearMap.rTensor_tmul`, and `LinearMap.rTensorHom`. Their definitions,
full signatures and docstrings were read. The public import
`Mathlib.RingTheory.TensorProduct.Maps` publicly supplies these and the ordinary tensor-ring
construction; it also supplies `Algebra.TensorProduct.map`, `lmul'`, and the tower algebra maps.
The proof dependency is the same node, so a second import is unnecessary.

Edge cases checked mathematically: B=0 or C=0 makes both source and target zero, with the unique
unital ring map between zero rings; L=0 forces B=C=0; k=0 forces L=B=C=0. For L=k, the formula
is ordinary tensor evaluation. For k=ℤ, L=B=C=ℤ[i], it is multiplication after diagonal base
change; it requires neither a separable nor an injective multiplication map. The non-flat
case k=ℤ, L=ℤ/4, B=C=ℤ/2 is included. Zero elements are empty sums in the proof, and no
finiteness or nonempty indexing assumption occurs. Independent object universes are preserved.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with “Unique ring homomorphism from (B tensor k C) tensor
  (L tensor k L) L to B tensor L C sending (b tensor c) tensor l to (l b) tensor c” returned
  eight hits, including `Algebra.TensorProduct.lift`, `lmul'`, `lmul''`, `rTensor`, and `lTensor`.
  These are general constructors, not the statement with both specified actions and uniqueness.
- `msearch.py ... leansearch` with “Unique evaluation ring homomorphism for tensor diagonal
  base change (B tensor k C) tensor (L tensor k L) L” returned eight hits, including
  `Algebra.TensorProduct.ext`, `ext'`, `algHomOfLinearMapTensorProduct_apply`, and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`; none has the node's source and formula.
- `msearch.py ... loogle 'Algebra.TensorProduct.map'` returned twelve tensor-map facts,
  including `map`, `map_tmul`, `map_comp`, and `lmul'_comp_map`. None is the diagonal evaluation
  theorem. An initial multi-name query was malformed and returned zero hits; the corrected
  single-name query is the search used here.
- `msearch.py ... grep 'diagonal|def lmul|def map|cancelBaseChange' RingTheory/TensorProduct`
  returned six hits including `cancelBaseChange` and `mapOfCompatibleSMul`.
  `cancelBaseChange` has source `A ⊗[S] (S ⊗[R] B)`, not this diagonal base change.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for tensor/diagonal combinations located
  unrelated geometric, derived and action-tensor constructions, no statement with this source.
  A search of `lean/WeilConjectures` for the exact node id returned no hits.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  all five proposed full-name suffixes found no collisions.

No statement faults or disputes were found. No new nodes or dependency repairs are needed.
Compilation and delivery checks are recorded below after completion.

## Second reading by Q27

Independent second reading by the maintainer's reviewer (the delivered section was the
author's own pass). Node read against Stacks `algebra.tex`, Tag 0C2Y
(`lemma-geometrically-reduced-over-separable-algebraic`), second proof paragraph, display
`K ⊗_{k'} A = (K ⊗_k A) ⊗_{(k' ⊗_k k')} k'`; the node is the agent generalization of the
evaluation direction to commutative rings, which is true (balancing:
`(sb ⊗ tc) ⊗ λ ↦ λst(b ⊗ c)` and `(b ⊗ c) ⊗ stλ ↦ stλ(b ⊗ c)` agree).

Clause list and Lean rendering:

- k commutative ring: `(k : Type u) [CommRing k]`. Correct.
- L commutative k-algebra: `(L : Type v) [CommRing L] [Algebra k L]`. Correct.
- B, C commutative L-algebras regarded as k-algebras by restriction: `[CommRing B] [CommRing C]
  [Algebra L B] [Algebra L C] [Algebra k B] [Algebra k C] [IsScalarTower k L B]
  [IsScalarTower k L C]`. The standard equivalent encoding of restriction; no extra condition.
- Tensor products of def-weil-pbc-module-tensor-product with factorwise multiplication, unit
  1⊗1: Mathlib `TensorProduct` with `Algebra.TensorProduct.instCommRing`. Correct.
- R = L ⊗_k L, D = B ⊗_k C: `L ⊗[k] L`, `B ⊗[k] C`. Correct.
- ψ: `tensorDiagonalScalarMap = Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L B)
  (IsScalarTower.toAlgHom k L C)`, so `s ⊗ t ↦ algebraMap s ⊗ algebraMap t = (s1_B) ⊗ (t1_C)`.
  Correct; installed by `.toRingHom.toAlgebra`.
- μ: `Algebra.TensorProduct.lmul' k (S := L)`, `s ⊗ t ↦ st` (`lmul'_apply_tmul`). Correct.
  Mathlib has no global `Algebra (L ⊗[k] L) (B ⊗[k] C)` or `Algebra (L ⊗[k] L) L` instance
  (grep of RingTheory/LinearAlgebra), so the `letI` structures are the only ones in play, and the
  type, ring instance and pure-tensor helper use the same `letI` terms.
- D ⊗_R L as a ring: `tensorDiagonalBaseChange : Type (max v w x)` with
  `tensorDiagonalBaseChangeCommRing` = the ordinary tensor ring. Real data, not hollow.
- Unique unital ring hom β (no R-linearity imposed on competitors): `∃! β : … →+* B ⊗[L] C`.
  Correct, and not weaker than the node.
- Formula for all b, c, λ: `∀ b c l, β ((b ⊗ₜ[k] c) ⊗ₜ l) = (l • b) ⊗ₜ[L] c`, with
  `l • b = algebraMap L B l * b`. Correct, quantifiers inside the predicate as in the node.
- No other assumptions: no Nontrivial/field/flat/finite binders. Universes u, v, w, x are
  independent.

Edge cases: B = 0 or C = 0 (both rings zero, unique map); L = 0 or k = 0 force the zero cases;
L = k (ordinary evaluation); non-flat ℤ → ℤ/4 → ℤ/2. All are covered, since no binder excludes
them.

H4: no Mathlib or project declaration states this map. `cancelBaseChange`,
`tensorTensorTensorComm`, `lmul'`, `lift` are general constructors. `tensorDiagonal` is absent
from lean/Sheaf. The sibling node lem-trf-tensor-diagonal-unit-hom has no Lean record yet. Its
statement should reuse `tensorDiagonalBaseChange` and `tensorDiagonalPureTensor` from this module
rather than redefine the ring.

H5/H6/H8/H9: one `sorry`, the theorem only. Every helper carries the source place and
`(blueprint: lem-trf-tensor-diagonal-evaluation-hom)`. The theorem docstring carries the node's
five proof steps. The module has a `module` header, a public import, `autoImplicit false`, and
no private or local instances. `lean.statement` is verbatim in the file. Only the `lean` field of
the node changed.

No mismatch found. The Lean was not changed.

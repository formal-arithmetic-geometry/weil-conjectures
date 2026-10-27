## Worker report

Item: `lem-trf-tensor-diagonal-unit-hom`, group Q44, stage 2.
Module: `Sheaf.RingTheory.TensorDiagonalUnitHom`.
Main declaration: `Algebra.TensorProduct.Diagonal.existsUnique_unitHom`.

The module states existence and uniqueness of the specified unital ring map. Its
only theorem has proof `sorry`. Four auxiliary declarations implement exactly
objects already introduced by this node: the map ψ, the diagonal tensor product,
its standard commutative ring instance, and its pure tensors. They use actual
Mathlib constructions and no choice, placeholder data, or additional theorem.
There are no new nodes, dependency modules, or statement corrections.

Source read: `literature/stacks-project/algebra.tex`, label
`lemma-geometrically-reduced-over-separable-algebraic` (Tag 0C2Y), especially the
second proof paragraph's identity
`K ⊗_{k'} A = (K ⊗_k A) ⊗_{k' ⊗_k k'} k'`.
The node explicitly generalizes the forward map to arbitrary commutative rings;
its four-step proof is reproduced in the theorem's docstring. This delivery
states that generalization without importing the field, separability, or
reducedness assumptions of the surrounding application.

Hypotheses and clauses, with the node and module open:

| Node text | Lean rendering |
| --- | --- |
| k is a commutative ring | `(k : Type u) [CommRing k]` |
| L is a commutative k-algebra | `(L : Type v) [CommRing L] [Algebra k L]` |
| B,C are commutative L-algebras | Independent types `(B : Type w) (C : Type z)`, their `CommRing` instances, and `[Algebra L B] [Algebra L C]` |
| Regard B,C as k-algebras by restriction | `[Algebra k B] [Algebra k C] [IsScalarTower k L B] [IsScalarTower k L C]`; these express compatibility with composition of the given structure maps, not flatness or injectivity |
| Use the module tensor product | Mathlib `TensorProduct`, notation `⊗[k]`, `⊗[L]`, and `⊗[L ⊗[k] L]`; no new tensor product definition |
| Multiplication and unit as specified | Mathlib tensor `CommRing` structures, inherited directly by `baseChangeCommRing`; `Algebra.TensorProduct.tmul_mul_tmul` and `one_def` give precisely the stated formulas |
| R = L tensor over k L, D = B tensor over k C | Literally `L ⊗[k] L` and `B ⊗[k] C` throughout |
| ψ(λ tensor λ') = (λ1_B) tensor (λ'1_C) | `scalarMap k L B C` is `Algebra.TensorProduct.map` of the two `IsScalarTower.toAlgHom` structure maps; `map_tmul` is its defining formula |
| D is an R-algebra through ψ | The internal instance `(scalarMap k L B C).toRingHom.toAlgebra` in `baseChange` |
| L is an R-algebra through μ(λ tensor λ') = λλ' | The internal instance `(Algebra.TensorProduct.lmul' k (S := L)).toRingHom.toAlgebra`; `lmul'_apply_tmul` is exactly this formula |
| Codomain D tensor over R L | `baseChange k L B C` unfolds to this Mathlib tensor product with exactly the preceding two instances |
| There is a unique unital ring homomorphism α | `∃! α : B ⊗[L] C →+* baseChange k L B C`; `RingHom` preserves 1 and uniqueness ranges over all ring homomorphisms |
| α(b tensor c) = (b tensor c) tensor 1, for every b,c | `∀ (b : B) (c : C), α (b ⊗ₜ[L] c) = baseChangeTmul k L B C (b ⊗ₜ[k] c) 1` |
| No injectivity, flatness, reducedness, finite generation, or field assumption | No such binders or predicates appear |
| Zero algebras are allowed | No `Nontrivial`, field, or domain instance is assumed |

All four universes are explicitly declared and independent. `baseChange` lives
in `Type (max v w z)` because the tensor carrier depends on its factor universes,
not the scalar ring universe. Every variable and instance is bound explicitly;
`autoImplicit` is disabled. The theorem has no `let` binders. The internal
`letI` expressions occur only in real definitions to fix the prescribed actions;
they introduce no file-local instance and no alternative global action on D or L.

Dependency interfaces read and used:

- `def-weil-pbc-module-tensor-product` is a Mathlib leaf without a `lean` record.
  Its `mathlib_match` is `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its quotient definition and
  canonical bilinear `TensorProduct.mk` were read, along with `TensorProduct.lift`,
  `lift.tmul`, and `ext'` in `Mathlib.LinearAlgebra.TensorProduct.Basic`.
  The module uses that exact `TensorProduct` and its pure-tensor notation.
- The proof dependency
  `lem-weil-pbc-algebra-tensor-pushout-universal-property` is also a Mathlib leaf.
  Its recorded interfaces were read in
  `Mathlib.RingTheory.TensorProduct.Basic` (`instCommRing`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `ext`) and
  `Mathlib.RingTheory.TensorProduct.Maps` (`productMap`,
  `productMap_apply_tmul`, `productMap_left`, `productMap_right`).
  The public import of `Mathlib.RingTheory.TensorProduct.Maps` supplies the
  statement's real constructions and all of these proof interfaces, so an
  additional proof-only import would be redundant.
- The further existing constructors `Algebra.TensorProduct.map`, `map_tmul`,
  `lmul'`, `lmul'_apply_tmul`, and `RingHom.toAlgebra` were read in their source
  files and reused directly. No dependency interface needed repair.

Edge cases checked before writing and on rereading:

- If B or C is zero, both the relative tensor and D, and hence the codomain,
  are zero rings. Their unique ring map satisfies the pure-tensor formula.
- If L is zero, its unital algebra structures force B and C to be zero, so the
  same reasoning applies. If k is zero, all the algebras are zero as well.
- If L = k, the map agrees with the usual tensor unit identifications.
- A noninjective structure map such as Z → Z/2 is allowed: only unital algebra
  data and its restriction compatibility are required.
- The nonflat example k = L = Z, B = Z/2, C = Z/3 has zero tensor products,
  which is included. Nilpotents, arbitrary characteristic, and infinite
  algebras are unrestricted by every construction.
- Uniqueness is among all ring maps, not just maps for a separately assumed
  L-algebra structure. Thus no hidden linearity assumption narrows uniqueness.

Searches for an existing statement (2026-10-24; full machine logs are in the
sandbox's `searches.jsonl`):

1. `msearch.py ... leanfinder` query:
   "For commutative k algebras L B C there is a unique unital ring homomorphism
   from B tensor over L C to (B tensor over k C) tensor over (L tensor over k L)
   L taking b tensor c to (b tensor c) tensor 1".
   Eight hits: `Algebra.TensorProduct.lift`, `liftEquiv`, `liftEquiv_apply`,
   `TensorProduct.isPushout`, `lift_tmul`,
   `Algebra.IsPushout.tensorProduct_tensorProduct`, `TensorProduct.isPushout'`,
   and `Algebra.TensorProduct.map`. None states this prescribed diagonal map.
2. `msearch.py ... leansearch` query:
   "There exists a unique ring homomorphism B tensor over L C to (B tensor over
   k C) tensor over (L tensor over k L) L sending b tensor c to (b tensor c)
   tensor 1". Eight hits, including `Algebra.TensorProduct.ext`,
   `algHomOfLinearMapTensorProduct`, `productMap`, `includeLeftRingHom`, `map`,
   and unrelated linear/bialgebra tensor maps. These provide reusable
   constructors, not the statement with these two prescribed scalar actions.
3. `msearch.py ... loogle` initially queried
   `Algebra.TensorProduct.map, Algebra.TensorProduct.lmul, Algebra.TensorProduct.lift`;
   it reported the unknown identifier `Algebra.TensorProduct.lmul`.
   Corrected query `Algebra.TensorProduct.lift` returned twelve hits, including
   `lift`, its restriction and pure-tensor formulas, `lmul'_comp_map`, and
   `Algebra.pushoutDesc_apply`. They do not supply this complete statement.
4. `msearch.py ... grep` queried
   `diagonal|cancelBaseChange|productMap|def lmul` in `RingTheory/TensorProduct`.
   Ten hits, chiefly `cancelBaseChange` and `productMap`; cancellation has
   differently nested factors and does not itself express the node.
5. Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `tensorDiagonal|tensor_diagonal|diagonal.*[Bb]ase[Cc]hange|diagonal.*[Uu]nit`
   found unrelated geometric and representation-theoretic diagonal constructions.
   An exact item-id search in `lean/WeilConjectures` found no declaration.
   Exact proposed-namespace/name searches across Mathlib, both project roots,
   and `dag/lean_names_upstream.json` found no collision or existing statement.

Validation: scompile.py compiled both its sandbox probe and the named library
module cleanly. An initial attempt to obtain the ring instance via
`inferInstanceAs` generated mismatched auxiliary declarations; replacing that
with the direct existing `Algebra.TensorProduct.instCommRing` term resolved it.
No mathematical statement or dependency was changed. Delivery dry run and push
results are recorded below when completed.

No statement dispute or node fault was found.

## Second reading by Q44

This is the dispatcher's single-worker workflow; the maintainer supplies the
independent review. I reread the final node and module together rather than
claiming that a second agent reviewed them. The table above checks every
hypothesis and conclusion against the actual declarations. In particular I
checked ψ uses both L-structure maps, μ is multiplication rather than one of
the two projections, the codomain ring and its pure tensors use identical
instances, and the existential is unique over `RingHom`. Zero rings and
independent universes remain admitted. The signature is explicitly bound and
contains neither a `let` nor an unstated assumption. The only rereading changes
were making the theorem's parameter binders explicit in its own signature and
using the direct Mathlib tensor ring instance; the node is unchanged outside
its `lean` field.

Delivery validation: `deliver2.py Q44 lem-trf-tensor-diagonal-unit-hom --no-push`
printed `OK (dry run): commit 099d4adec11 passes the preflight and compiles;
nothing pushed`. The final explicitly bound signature compiled cleanly in both
sandbox and library module mode. The final delivery uses the same Lean and node
files; this validation note is the only subsequent report addition.

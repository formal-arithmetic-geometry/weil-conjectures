## Worker report

The module states `SymmetricInvariantFrobenius.symmetric_invariant_frobenius_projection`.
Its only theorem proof is `sorry`. Its four helper definitions have real data:
`projectionForBasis` reads the finitely supported coordinates of the tensor-word basis,
retains the constant words and sends each to `1 ⊗ b`; `projection` uses the chosen
vector-space basis; `twistMap` is `LinearMap.baseChange`; `tensorComparison` is the
inverse of `TensorProduct.AlgebraTensorModule.distribBaseChange`. These are the maps
specified in this node, not additional hypotheses or independent missing notions.

Source read: Milne, Algebraic Groups (2017), Section 11(i), printed pp. 224–225
(PDF pages 236–237), including the invariant-tensor diagram preceding Definition 11.39.
The seven coordinate-proof steps of the DAG node are included in the theorem docstring.

Hypotheses and objects, matched to the node:

* The field is `(k : Type u) [Field k]`. Characteristic `p > 0` is expressed as
  `(p : ℕ) [Fact p.Prime] [CharP k p]`: the positive characteristic of a field is
  prime, so this imposes exactly the stated characteristic hypothesis.
* `M : Type v` and `N : Type w` have only `AddCommGroup` and `Module k` instances.
  There is no finite-dimensionality or perfection assumption. The field, the two
  spaces and the basis index `J : Type j` have independent explicitly bound universes.
* The tensor power is `⨂[k] (_ : Fin p), M` (`PiTensorProduct`).
  The Frobenius endomorphism is `frobenius k p`, the map `a ↦ a^p`.
* The twist is the existing object
  `(ModuleCat.extendScalars (frobenius k p)).obj (ModuleCat.of k M)`.
  Its underlying tensor product is `k ⊗[k, frobenius k p] M`. The node uses the
  opposite order: `m ⊗ c` is represented here by `c ⊗ m`. Its balancing rule is
  `c ⊗ (a • m) = (a^p * c) ⊗ m`; its outer k-action is multiplication on c.
  Thus the scalar structure is the node's second-factor scalar structure.
* The invariant subspace is the displayed intersection of Mathlib's
  `LinearMap.fixedSubmodule` for every `PiTensorProduct.reindex` permutation.
  In elementwise clauses the identical condition is written explicitly as
  `∀ e, PiTensorProduct.reindex ... e x = x`.

Each conclusion, in the order of the theorem's six conjuncts:

1. For every basis `B : Module.Basis J k M`, the first conjunct produces an actual
   `Module.Basis` of the intersection of fixed submodules. Its indices are
   `Set.range (fun t ↦ Finset.univ.image (fun e ↦ t ∘ e))`: distinct orbit finsets,
   not representatives with repetitions. The displayed equality says its vectors
   are exactly the sums of the distinct tensor words in those orbits.
2. The second conjunct specifies the projection on every orbit sum. The condition
   `∀ i, t i = t ⟨0, p.pos⟩` is exactly that the word is constant, equivalently its
   permutation orbit is singleton. Its image is `1 ⊗ B (t 0)` (the node's
   `B (t 0) ⊗ 1`); every nonconstant orbit sum maps to zero.
3. The third conjunct says that for every invariant x, `projectionForBasis B x`
   equals `projection M x`. This is basis independence, comparing every basis
   against the chosen basis. The map lambda is the restriction of the displayed
   k-linear `projection` to the invariant submodule. We construct its ambient
   diagonal-coordinate extension, but all intrinsic assertions are restricted to
   invariant inputs; no naturality outside invariants is asserted.
4. `PiTensorProduct.map (fun _ ↦ h)` is the tensor power of h. The fourth conjunct
   asserts that it carries every invariant x to an invariant tensor and that
   `projection N (map h x) = twistMap h (projection M x)`. By its actual definition
   `twistMap h` is the canonical base-changed map `c ⊗ m ↦ c ⊗ h(m)`.
   This is both the restriction to `I_p(h)` and the requested naturality equality.
5. `PiTensorProduct.map₂ (fun _ ↦ TensorProduct.mk k M N) x y` is interleaving
   on pure inputs, by `PiTensorProduct.map₂_tprod_tprod`, extended bilinearly.
   The fifth conjunct first asserts its invariance under paired-factor permutations
   for invariant x,y, then asserts the lambda tensor identity. `tensorComparison`
   is the specified canonical linear isomorphism, sending
   `(a ⊗ m) ⊗ (b ⊗ n)` to `(a*b) ⊗ (m ⊗ n)` by
   `AlgebraTensorModule.distribBaseChange_symm_tmul`. After reversing the order
   in each Frobenius tensor, this is exactly the formula for kappa in the node.
6. The last conjunct applies the inverse unit isomorphism of extension of scalars
   to `projection k (tprod (fun _ ↦ 1))`, and states that the result is 1.
   Mathlib's `ModuleCat.extendScalars_ε` identifies this unit isomorphism with
   `AlgebraTensorModule.rid`; on `c ⊗ a` its inverse is `c * a^p`. This is the
   node's canonical identification `a ⊗ c ↦ a^p*c`.

Dependencies read and used:

* `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, lines 116–125 and 174–180,
  including the nontrivial division-ring axioms inherited by `Field`.
* `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift` and `TensorProduct.ext'`, Mathlib.LinearAlgebra.TensorProduct
  Defs (81 and 376) and Basic (123–145). Canonical tensor products are used throughout.
* `def-weil-module-base-change`: `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`, the recorded module
  Mathlib.LinearAlgebra.TensorProduct.Tower, lines 441–470 and 661–710. Imported
  publicly; `twistMap` and `tensorComparison` specialize those declarations to
  Frobenius. ModuleCat.ChangeOfRings, lines 350–420, supplies the existing bundled
  tensor object and explicitly records its coefficient multiplication and map formula.
* Proof dependencies: `Module.Free.of_divisionRing` and `Module.Basis.ofVectorSpace`
  (Mathlib.LinearAlgebra.Basis.VectorSpace, 147–157);
  `Basis.piTensorProduct`, `Basis.piTensorProduct_repr_tprod_apply`,
  `Basis.piTensorProduct_apply` (Mathlib.LinearAlgebra.PiTensorProduct.Basis, 33–50);
  `Module.Basis.baseChange`/`baseChange_apply`
  (Mathlib.LinearAlgebra.TensorProduct.Basis, 64–76);
  `iterateFrobeniusOfPrime` (WeilConjectures.Mathlib.Algebra.CharP.Lemmas, 26–44).
  The recorded Frobenius module is imported privately as a proof dependency; the
  field specialization uses Mathlib `frobenius` publicly in the statement itself.

Edge cases checked mathematically before writing: M or N zero, an empty basis index
for the zero module, infinite-dimensional spaces and bases, p=2, arbitrary primes p,
and imperfect fields. Primality excludes p=0 and p=1 exactly as positive field
characteristic does. Because p is positive, the index 0 used to recognize constant
words exists. Only finite support and finite permutation orbits are summed; no
finite basis, division by p, division by p!, or Frobenius inverse is used. Distinct
orbit finsets prevent stabilizer multiplicities. In the zero-space case all orbit
and basis clauses allow empty indices. Distinct universes impose no equality
between M and N or either space and the field.

Searches run for an existing statement:

* `msearch.py leanfinder`, query “Natural Frobenius projection from symmetric
  invariant tensor powers of arbitrary vector spaces compatible with tensor
  products”: eight hits, including `SymmetricPower.mk`, `SymmetricPower.tprod`,
  `SymmetricPower.Rel`, `TensorPower`; none is this invariant-subspace projection.
* `msearch.py leansearch`, query “diagonal coefficient projection from permutation
  invariant p-fold tensors to Frobenius base change is natural and compatible with
  tensor products”: eight hits, including `IsBaseChange`, `TensorPower.cast_tprod`,
  `PiTensorProduct.map_reindex` and `SymmetricPower.tprod_equiv`; no exact match.
* `msearch.py loogle`, query `"TensorProduct", "frobenius"`: zero hits.
* `msearch.py grep`, query `Frobenius|frobenius|invariant|orbit` in
  Mathlib/LinearAlgebra/TensorPower: zero hits.
* Direct `rg` of `lean/WeilConjectures/LinearAlgebra` for
  `Frobenius|frobenius|invariant|orbit` finds the semilinear fixed-point theory,
  which does not state this projection. Direct grep for this node id in
  `lean/WeilConjectures` finds no declaration.
* Direct `rg` of `lean/Sheaf` for `symmetricInvariant|invariantTensor|FrobeniusTwist|
  frobeniusTwist|orbitSum`, followed by opening the full module, finds
  Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung. Its projection requires
  a commutative k-algebra and has codomain a ring pushout; its theorem concerns
  coordinate Hopf algebras, not arbitrary vector spaces or the stated naturality
  and tensor identity. It is a consumer of this node. We avoid an import cycle:
  the invariant submodule and finite orbit expressions here use Mathlib directly,
  without declaring a second invariant-submodule or orbit definition. The new
  projection definitions supply the arbitrary-module extension-of-scalars interface.
* Direct Mathlib search also located `LinearMap.fixedSubmodule`,
  `ModuleCat.extendScalars`, and its monoidal unit, which are reused instead of
  defining new notions.

No node correction, new node, unusable dependency record or statement dispute was
needed. All variables are explicit (`set_option autoImplicit false`). The prescribed
scompile.py succeeded via its server confirmation; local temporary storage sometimes
reported ENOSPC, and the wrapper's normal fallback compiled the same source cleanly.
No launcher script or library file was edited.

## Second reading by NE

Author's second reading, not the maintainer's independent review: I reopened the
node and the final Lean module and matched its clauses as above. I checked the
Frobenius tensor order and outer scalar action against ModuleCat.ChangeOfRings,
the kappa formula against Tower.distribBaseChange_symm_tmul, and the unit orientation
against ModuleCat.extendScalars_ε. The orbit indices are distinct finsets, and the
basis is of the invariant subspace itself. The two cases for the basis projection
and basis independence are both present; naturality includes preservation of
invariants, and tensor compatibility includes simultaneous invariance. The unit
clause is a scalar equality, not merely existence of an identification.

During elaboration I replaced the bundled base-change unit (which imposed a
universe constraint) by its explicit balanced tensor generator, and replaced the
bundled functor map by the recorded unbundled `LinearMap.baseChange`. Thus the final
statement has independent field/space/index universes. I also replaced an attempted
monoidal comparison on differently sized module categories by the existing
`distribBaseChange` comparison; no mathematical hypothesis was added. These are
implementation repairs; the DAG statement and all other node fields are unchanged.

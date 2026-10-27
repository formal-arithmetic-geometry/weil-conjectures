## Worker report

Record the existing declaration
`AddCommGroup.exists_compatible_lift_of_bijective_nsmul` in
`Sheaf.GroupTheory.CompatibleAbelianGroupLifting`, source file
`lean/Sheaf/GroupTheory/CompatibleAbelianGroupLifting.lean:33`.
No Lean module, definition or proof is added. Only the item's `lean` changes.
The natural-language statement is string-identical to the landed node
`lem-per-compatible-abelian-group-lifting`. Its `reviewed_lean` explicitly asks
that the sfb node attach to this declaration with `existing: true`.
Read the entire existing declaration and docstring locally and confirmed the
identical live source using `scompile.py --source
Sheaf.GroupTheory.CompatibleAbelianGroupLifting`.

Clause-by-clause correspondence:

- Five arbitrary abelian groups: the explicit type binders `A`, `B`, `E`,
  `E₀`, `J` and their five `AddCommGroup` instances. Universes `uA`, `uB`,
  `uE`, `uE₀`, `uJ` are independently declared in the existing module.
- Finite generation for the canonical integer scalar action:
  `[Module.Finite ℤ A] [Module.Finite ℤ B]`. No arbitrary alternative module
  structure is quantified over.
- The group homomorphism `u`: `(u : A →+ B)`.
- `K = ker u`: `u.ker`, with `[Finite u.ker]`.
- `C = B/u(A)`: `B ⧸ u.range`, the actual additive quotient group.
- Its torsion subgroup: `AddCommGroup.torsion (B ⧸ u.range)`, with the
  corresponding `Finite` instance. Mathlib's torsion subgroup consists of
  elements of finite additive order; by the additive version of
  `isOfFinOrder_iff_pow_eq_one`, this means exactly `∃ n > 0, n • c = 0`.
- The short exact sequence's maps: `(i : J →+ E) (π : E →+ E₀)`.
- Injectivity on the left: `hi : Function.Injective i`.
- Surjectivity on the right: `hπ : Function.Surjective π`.
- Exactness in the middle: `hexact : π.ker = i.range`. This is genuine
  equality of subgroups, including both inclusions and `π ∘ i = 0`.
- Multiplication by the finite kernel order is an automorphism of `J`:
  `hK : Function.Bijective (fun j : J ↦ Nat.card u.ker • j)`.
- Multiplication by the finite torsion-cokernel order is an automorphism:
  `hC : Function.Bijective (fun j : J ↦
  Nat.card (AddCommGroup.torsion (B ⧸ u.range)) • j)`.
  Natural multiplication is automatically additive on an abelian group,
  so bijectivity is equivalent to being an additive group automorphism;
  no arbitrary inverse or stronger divisibility assumption appears.
- Given maps: `(a : A →+ E) (b₀ : B →+ E₀)`.
- The commuting square: `hcompat : π.comp a = b₀.comp u`.
- Existence of a group homomorphism: `∃ b : B →+ E`.
- Extension of the prescribed map: `b.comp u = a`.
- The specified lift of `b₀`: `π.comp b = b₀`.
  Both conclusions occur together as a conjunction.

Dependency declarations read and used:

- Statement dependency `def-weil-finitely-generated-module`:
  `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs`, whose full class
  signature and docstring identify finite generation with `fg_top`.
  The existing module publicly imports it.
- Proof dependency `lem-sbc-finitely-generated-abelian-group-structure`:
  `AddCommGroup.equiv_free_prod_directSum_zmod` from
  `Mathlib.GroupTheory.FiniteAbelian.Basic`; read its complete signature,
  docstring, and proof, including the absence of positivity on exponents.
  Also read `Module.Finite.iff_addGroup_fg` in the first module.
  No new statement module is being created, so its proof-only import is
  not added to the read-only existing module in this delivery.
- Mathlib's existing `AddCommGroup.torsion`, read through its `to_additive`
  source definition in `Mathlib.GroupTheory.Torsion`, supplies the actual
  torsion subgroup. No auxiliary definition or new DAG node is needed.

Edge cases checked before recording the statement:

- Zero groups and trivial kernel or torsion subgroup are allowed.
  Their `Nat.card` is 1, so the order actions are identity maps, as required.
- A torsion-free cokernel is allowed even if it is infinite. The finite
  hypothesis applies only to its torsion subgroup, not to the whole quotient.
- `u = 0` and `u` an isomorphism are covered; there is no hidden injectivity
  or surjectivity assumption on `u`.
- For multiplication by a nonzero integer `d` on `ℤ`, the kernel order is
  1 and the torsion-cokernel order is `|d|`; these are exactly the required
  actions on `J`. If `d = 0`, the kernel is infinite and correctly excluded.
- `J = 0` is permitted. No nonzero, characteristic, or equality-of-universes
  restriction is imposed. Independent universes retain all five groups.
- Neither finiteness nor bijectivity was silently dropped merely because
  some instances make it redundant.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`, query: "Lift a compatible square of
  homomorphisms of finitely generated abelian groups across a short exact
  sequence when finite kernel and torsion cokernel orders act invertibly
  on the kernel". Eight hits: finite short exact sequences, SnakeLemma
  and five-lemma surjectivity; none is the desired compatible lift.
- `msearch.py ... loogle`, query: `AddMonoidHom, Function.Bijective, lift`.
  No hits, with unknown identifier `lift`; retried with the valid query
  `"AddMonoidHom", "lift"`. Twelve hits, including
  `AddMonoidHom.liftOfSurjective` and `liftOfRightInverse`; none supplies
  this relative lift from the finite-order assumptions.
- `msearch.py ... leansearch`, query: "Lift a compatible square of
  homomorphisms between finitely generated abelian groups through a short
  exact sequence if multiplication by the finite kernel order and torsion
  cokernel order is invertible on its kernel". Eight hits including
  `CategoryTheory.Abelian.monoLift`, short-complex lifts, ordinary quotient
  factorization and `ZMod.lift`; no exact match.
- `msearch.py ... grep`, query `compatible.*lift|lift.*torsion|exists.*lift`,
  subdirectory `GroupTheory`: one congruence-factorization hit, no match.
- `rg -n 'compatible.*(lift|abelian)|abelian.*lift|lem-sfb-compatible-abelian-group-lifting'`
  on both `lean/WeilConjectures` and `lean/Sheaf`: found the exact existing
  theorem in `Sheaf/GroupTheory/CompatibleAbelianGroupLifting.lean`.
- `rg -n 'compatible_abelian_group_lift|compatibleAbelianGroupLift|lem-sfb-compatible-abelian-group-lifting'`
  on both source roots and `dag/lean_names_upstream.json`: confirmed that
  module's explicit sfb citation. A subsequent search for the module and
  `exists_compatible_lift` in `dag/nodes` identified the owning per node
  and its maintainer note. No additional source theorem matched.

Validation: a temporary sandbox `Check.lean` imported the existing module under
its public module header and checked the full declaration with `#check`.
`scompile.py Q159 lem-sfb-compatible-abelian-group-lifting <Check.lean>`
passed both sandbox and library checks without errors or warnings (4.7 s and
8.3 s). The diagnostic file was removed and is not delivered.

No statement correction or disputed statement. The existing theorem retains
its stage-2 `sorry`; recording it does not claim to prove it. The old docstring
points to the sfb DAG proof; that six-step proof remains unchanged in this
item and is the actual structure-theorem/cyclic-correction proof for stage 3.
Sharing the declaration does not introduce a second theorem or an import cycle.

## Second reading by Q159

This is a separate self-check, not a claim of an independent agent review;
the dispatcher forbids starting other agents and the maintainer supplies
independent delivery review. Reopened the item's node, the per node and the
existing module. Their natural-language statements agree verbatim. Rechecked
all binders and each clause listed above: two integer finite-generation
instances, the actual finite kernel and torsion quotient, injective/surjective
maps, kernel-range equality, two bijective order actions, compatibility and
both conclusions. Found no mismatch. In particular `Finite` is never applied
to the full cokernel and the two scalar orders are not interchanged. The
record's signature is extracted directly from the source, with its original
line breaks. No extra node, dependency changes or module changes are needed.
The existing-module route follows the explicit maintainer instruction in
`lem-per-compatible-abelian-group-lifting.reviewed_lean`.

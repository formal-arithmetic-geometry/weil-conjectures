## Worker report

The module `Sheaf.RingTheory.FlatnessFaithfullyFlatExtension` states
`Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension`, with `sorry`
as its only proof. It states Stacks Algebra Tag 0584(2),
`lemma-flatness-descends-more-general`, with R=A, S=B, S'=C and M=N.
I read the source lemma and proof in `literature/stacks-project/algebra.tex`.
The node's natural statement, dependencies and proof are unchanged. No new
notions or dependency repairs are needed.

Hypothesis and clause correspondence:

- The commutative rings A, B and C are `{A : Type u} {B : Type v}
  {C : Type w}` with `[CommRing A] [CommRing B] [CommRing C]`.
- The ring homomorphisms A → B → C are `[Algebra A B] [Algebra B C]`.
  For commutative rings each algebra structure is precisely such a ring map.
- The composite action on C is `[Algebra A C] [IsScalarTower A B C]`.
  The tower forces this algebra map to be the composite A → B → C;
  it is compatibility data, not an added mathematical restriction.
- The arbitrary B-module N is `{N : Type t} [AddCommGroup N] [Module B N]`.
- Its induced A-module structure is `[Module A N] [IsScalarTower A B N]`.
  The tower forces `a • n = (algebraMap A B a) • n`; any B-module has
  this restriction of scalars. No independent A-action is permitted.
- C faithfully flat as a B-module is `[Module.FaithfullyFlat B C]`.
  No flatness of B over A or C over A is assumed.
- The scalar extension is Mathlib's `C ⊗[B] N`. Its inferred A-action
  acts on the C factor, using `Algebra A C`. On a pure tensor it is
  `a • (c ⊗ n) = (a • c) ⊗ n`, hence is exactly the action through
  A → B → C specified in the node.
- The conclusion is exactly `Module.Flat A N ↔ Module.Flat A (C ⊗[B] N)`.
  Both flatness predicates are over A, and both directions are included.
- The four independent universes u, v, w, t allow unrelated carrier sizes.
  Every variable and universe is explicitly bound.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: recorded module
  `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`, and its explicitly
  listed module predicate `Module.Flat` from `Mathlib.RingTheory.Flat.Basic`.
  The statement uses `Module.Flat`, whose equivalence with the node's
  injectivity test is `Module.Flat.iff_lTensor_preserves_injective_linearMap`
  (and its right-tensor counterpart). The recorded module is publicly imported.
- `def-weil-pbc-faithfully-flat-ring-map`: recorded
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`.
  Its equivalence with preservation and reflection of exactness is
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`; the class includes flatness.
- `def-weil-pbc-module-tensor-product`: the Mathlib leaf's `mathlib_match`
  supplies `TensorProduct` from `Mathlib.LinearAlgebra.TensorProduct.Defs`.
  This module is publicly imported; there is no missing Lean record to repair.
  I also read `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`, `ext'`
  and `LinearMap.rTensor`/`rTensor_tmul` from the recorded source files.

All proof dependencies are these same three definition nodes, so the public
statement imports also supply the full proof plan. The declaration docstring
includes all four steps of the node's proof: faithful-flat detection of
injections, tensor interchange with naturality on pure tensors, preservation,
and reflection of the flatness injection test.

Edge cases checked before writing:

- N=0: both N and its scalar extension are zero, hence flat over A.
- B=C with the identity map: tensor cancellation reduces the equivalence
  to flatness of N over A on both sides.
- B=0: a unital map B → C forces C=0, and any B-module is zero;
  the assertion remains valid. If A=0, all the rings and modules are zero.
  No `Nontrivial` assumption excludes these cases.
- A=Z, B=Z/2, C=B[t], N=B: C is faithfully flat over B, but both sides
  are nonflat over Z. The statement does not inadvertently assume B/A flat.
- Faithfulness is essential: B=Z, C=Q, A=Z and N=Z/2 gives a nonflat N
  with zero (flat) extension. The hypothesis correctly excludes this example.
- No finite generation, finite presentation, locality or noetherian condition
  is used or added. No index universe or nonempty indexing assumption occurs.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “For ring maps A to B to C with C faithfully flat
  over B, a B module N is flat over A iff C tensor B N is flat over A”.
  Eight hits, including `Module.Flat.of_flat_tensorProduct`,
  `Module.Flat.iff_flat_tensorProduct`, and faithfully flat base-change results.
  None compares both modules' flatness over the smaller ring A.
- `msearch.py loogle`: `Module.Flat.iff_flat_tensorProduct`. One hit with
  conclusion `Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M`, which has
  a different base ring in the tensor-product flatness predicate.
- `msearch.py grep`: `iff_flat_tensorProduct|of_flat_tensorProduct|
  lTensor_injective_iff_injective` in `RingTheory/Flat`. Seven hits;
  I read Basic.lean's same-base descent and injectivity reflection signatures.
- `msearch.py leansearch`: “flatness over a smaller base ring is preserved
  and reflected by faithfully flat extension along an intermediate algebra”.
  Eight hits, again base-change stability and the different same-base criterion.
- `rg` in upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `iff_flat_tensorProduct`,
  `of_flat_tensorProduct`, `flat_iff.*faithfully`, and `flat_iff.*tensor`:
  no exact intermediate-extension module equivalence. The upstream
  `Module.Flat.of_flat_of_faithfullyFlat` was read in full signature:
  it concludes A-flatness of the ring B from A-flatness of C, not the
  assertion for an arbitrary B-module N.
- The side `NoetherianLocalModelTowerBaseFlat` contains a private
  `flat_tensor_over_algebra` for just the forward implication with a flat
  extension. It is neither a public exact equivalence nor a replacement
  for the present faithfully flat criterion.
- `rg` for the proposed full declaration name in Mathlib, upstream,
  side `lean/Sheaf`, and the upstream names index: no collision.

Validation: `scompile.py Q44 lem-trf-flatness-faithfully-flat-extension`
compiled this module as both sandbox and library modules, with no diagnostics.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

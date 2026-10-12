## What changed

Proved both declarations in `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`.
Added proof-only imports of `Mathlib.LinearAlgebra.TensorProduct.Basis` and
`Mathlib.LinearAlgebra.Basis.VectorSpace`. All existing signatures, visibility,
public imports, and docstrings are unchanged.

`TensorProduct.injective_and_range_eq_invariants` follows the existing six-step
DAG plan. Choose `Module.Basis.ofVectorSpace` and use
`TensorProduct.equivFinsuppOfBasisLeft` for coordinates. Tensor induction proves
that each automorphism acts coordinatewise. Injectivity follows from coordinate
uniqueness and injectivity of `algebraMap`. For an invariant tensor, `hfixed`
provides base-field preimages of its coordinates. These preimages are unique
because `algebraMap` is injective, and vanish wherever the tensor's coordinates
vanish. `Finsupp.onFinset` therefore constructs their finitely supported family;
applying the inverse basis representation gives the required vector.

`Algebra.TensorProduct.range_eq_invariants_and_equiv` specializes the first
result and uses `AlgEquiv.ofInjective` for the canonical isomorphism onto the
range. No node update is needed: the original basis route and its three
Mathlib-backed dependencies are retained. No definition or statement changed.

## Proved and sorry left

Closed 2 original holes:

- `TensorProduct.injective_and_range_eq_invariants`.
- `Algebra.TensorProduct.range_eq_invariants_and_equiv`.

Both belong to `lem-weil-pbc-tensor-field-extension-galois-invariants`.
No holes remain, and no holes were added or split off. The module compiles
without warnings using `lcompile.py`.

## No longer needed

None. No original imports, DAG nodes, or modules were removed. The existing
basis-existence, scalar-extension, and field-extension dependencies are all
used through Mathlib. No additional Sheaf dependency is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The coordinate proof works for infinite-dimensional
vector spaces because its coefficients have finite support. It also covers the
zero vector space, the trivial extension, and arbitrary (possibly infinite)
automorphism subgroups satisfying `hfixed`. The algebra assertion requires no
commutativity assumption on `A` beyond its original signature.

Searches were run with `msearch.py` (LeanFinder for fixed tensors, Loogle for
`AlgEquiv.ofInjective`, and grep for `equivFinsuppOfBasisLeft`) and local `rg`
over Mathlib and both project roots. No existing complete theorem was found;
Mathlib provides all the ingredients of the original argument.

## Second reading by B2

1. **Visible interfaces: PASS.** Compared the only delivered module with the
   repository using `diff -u`. Both existing declaration signatures, all
   docstrings, visibility, and the three public imports are byte-for-byte
   unchanged. The only changes are two proof bodies and two plain, proof-only
   Mathlib imports. There are no definitions, new declarations, adapted modules,
   or change records, and no relevant open interface change was found.
2. **Proof and trust: PASS.** Independently compiled the module with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for
   both declarations: each uses only `propext`, `Classical.choice`, and
   `Quot.sound`. Checked the complete source for `sorry` and forbidden trust
   escapes: none. The coefficient witnesses come from a proved consequence of
   `hfixed`, and are unique by injectivity of `algebraMap`; no data is chosen from
   an unproved existence statement. The equivalence onto the range comes from
   Mathlib's proved `AlgEquiv.ofInjective`.
3. **Split statements: PASS (none).** No new statement or hole is split off.
   Read the coordinate-action induction and finite-support construction in full.
   Zero spaces, the trivial extension, an empty basis, infinite-dimensional spaces,
   and infinite automorphism subgroups require no extra assumption. The algebra
   specialization uses only the original `Ring A` and `Algebra k A` assumptions.
4. **Route and pruning: PASS.** Read the original six-step node proof and
   `dag/units/sk-thm-p1.json`, including `realized`. The delivered argument retains
   the basis, scalar-extension coordinates, fixed coefficients, and injectivity
   route; it bypasses no unit step. Rechecked Mathlib tensor-basis declarations
   and the upstream joint-injectivity tensor lemma. The latter does not prove the
   invariant-range assertion and offers no shorter complete route. Fresh
   LeanFinder search for simultaneous fixed vectors after scalar extension and
   Loogle search for `LinearMap.lTensor, Set.range`, together with local `rg`,
   found no replacement theorem. Both added imports supply proof ingredients;
   original public imports supply the statements. No old proof dependency is
   unused, so `## No longer needed` is complete.
5. **DAG agreement: PASS.** Read the item's node and all three dependency records.
   Basis existence, tensor coordinates, and field-extension injectivity are
   Mathlib-backed and used by the proof. The original `proof`, `proof_deps`, and
   agent-written `proof_origin` describe this argument accurately and need no
   edit. There are no new nodes to validate.

Second reading changed only this report, adding the independent checks and
verdicts. No Lean repair was needed. Confirmed accounting: two holes closed,
zero added, zero split off, and no modules pruned.

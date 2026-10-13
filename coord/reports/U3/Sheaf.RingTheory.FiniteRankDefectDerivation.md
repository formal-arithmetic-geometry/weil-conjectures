## What changed

Proved `Algebra.exists_finite_rank_defect_derivation` with its signature and public imports
unchanged. Added the proof-only import `Sheaf.RingTheory.FiniteKernelScalarExtension`.
Its theorem `LinearMap.exists_extension_finite_error` is also fully proved from Mathlib.
It isolates the finite-support basis argument for arbitrary vector spaces: a finite kernel
on scalar extension allows extension with a finite error over the smaller field.

The main proof constructs the K-action on I through the given section, proves compatibility
with its existing k-action using the annihilation hypothesis, and constructs the integer
relative derivation from theta. Middle Jacobi--Zariski exactness makes the base-change
kernel finite. The new linear-algebra theorem supplies the corrected map; universal
Kahler differentials and the k-linear inclusion of I give the requested ring-valued
identities and finite span. Both modules compile cleanly using lcompile.py --all.

The unchanged signature includes hI and hp, which the stronger integer-relative argument
does not need. The unused-variable linter is disabled only for this existing theorem.
No statement, definition, public import, or downstream module was changed.

## Proved and sorry left

Closed the original hole `Algebra.exists_finite_rank_defect_derivation`
(node `lem-weil-pbc-finite-rank-defect-derivation`).
Proved the new theorem `LinearMap.exists_extension_finite_error`
(node `lem-weil-pbc-finite-kernel-scalar-extension`).
No sorry remains in either delivered module; no holes were added or split off.
This is a proof, not a decomposition. All proof dependencies are proved Mathlib declarations.

## No longer needed

No original imports, modules, or dependency nodes were removed. The original
Jacobi--Zariski module and all three original DAG dependencies remain used.
No prime-field action, basis consisting of exact differentials, or injectivity of the
Jacobi--Zariski connecting map is needed: the proof uses an arbitrary basis of Omega(k/Z)
and exactness at the scalar extension alone. No separate nodes for those stronger steps
were imported or introduced.

The provisional core/error theorem files used during initial exploration were removed;
they are not part of this delivery. The new helper uses only the statement imports
TensorProduct.Basic and Finiteness.Defs, with proof imports TensorProduct.Basis,
Basis.VectorSpace and Finiteness.Basic.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the existing statement or plan. The plan can be
simplified by working over Z, which preserves the source's finite-support route and all
unit-level requirements. Its restriction to positive characteristic is unnecessary for
this sublemma, but its original signature has been preserved.

The source proof was read at https://stacks.math.columbia.edu/tag/07FG, paragraphs on the
basis and finite subset J0. The local literature/stacks-project/smoothing.tex copy is absent on this
machine. Blueprint searches for "finite kernel", "linear map", and "07FG" found no
existing blueprint statement of the new helper. The ancestor script returns None for
the item's module-based created.item chain; the new node instead inherits the item's
already recorded ancestor thm-weil-pbc-finite-etale-lifting and records the precise step.

Edge cases of the new helper: a zero kernel gives an empty support and exact extension;
zero vector spaces and the zero ideal are permitted; no Nontrivial M or finite-dimensional
V assumption is present. Only the kernel is assumed finite. The error span is over k,
not over K; this is proved by spanning V with its original k-basis.

## New nodes

`lem-weil-pbc-finite-kernel-scalar-extension` is the general linear-algebra argument in
Tag 07FG, steps choosing finite kernel support and extending the remaining independent
images. Its module is `Sheaf.RingTheory.FiniteKernelScalarExtension`, its theorem is
`LinearMap.exists_extension_finite_error`, and it is fully proved. The node records the
actual LeanSearch (unavailable), LeanFinder, Loogle, and grep queries and results.
No change record is needed because existing signatures and visibility are unchanged.

## Second reading by U3

1. Compared the delivered module with the repository using diff and compared the
   existing theorem signature byte for byte: identical. Public imports and visibility
   are unchanged. The new helper has its own new module and node; its only import in
   the item is proof-only. No statement, definition or downstream module changed.
   Verdict: pass.
2. Read both proofs in full. Both modules compile cleanly in import order with
   lcompile.py --all. Neither has sorry, an axiom, unsafe, opaque, implemented_by,
   extern, or a kernel-check bypass. All local constructions use proved Mathlib
   results; no data is selected from an unproved existence theorem. A scratch copy with #print axioms for both theorems compiled: each
   uses exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   Verdict: pass.
3. No statement was split off with sorry. The new, fully proved linear-algebra helper
   is strictly a part of the derivation argument. Checked its finite-support bound,
   independence modulo the kernel, extension identity, and base-field span argument.
   Zero V, W or M, the zero ideal, an empty complementary family, and zero kernel
   introduce no missing nontriviality assumption. Independent LeanFinder and Loogle
   searches for extension of a subspace linear map found LinearMap.exists_extend,
   already used; grep for finite error, rank extension and kernel, together with
   searches of lean/Sheaf and lean/WeilConjectures, found no duplicate helper.
   Verdict: pass.
4. Checked the top-down route against Tag 07FG (https://stacks.math.columbia.edu/tag/07FG)
   and the Mathlib middle-exactness and linear-extension declarations. Working over
   integers needs only middle exactness and an arbitrary basis; no stronger
   prime-field theorem is needed. Every delivered import serves a signature or a
   proof step. All three old proof dependencies remain used, so the list of pruned
   nodes is empty. Checked dag/units/sk-thm-p1.json: this helper is below the unit's
   realized statement and steps, which are preserved. Verdict: pass.
5. Checked both nodes' proof steps, their uses/proof_deps union, proof_origin,
   exact Lean signatures, sources and new-node fields. They agree with the code.
   Verdict: pass.

Changed only the item's natural-language proof sketch: it described exact-differential
bases over F_p, while the actual proof uses an arbitrary basis over Z and the new
helper. The corrected sketch now describes the actual argument. No Lean proof changed.

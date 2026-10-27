## What changed

Proved `CategoryTheory.ConstantCompletion.finiteFreeComplexDualPullback` with its
published statement unchanged. The delivery changes its module and DAG node,
and adds the fully proved helper module `Sheaf.Paper.RingComplexEndomorphismSelfDual` with its node. All other
supporting lemmas are private and fully proved.

The ordinary comparison is the transpose of pulled-back evaluation. The existing
generic Hom-complex transport supplies its differential compatibility and
naturality. Its module components are invertible on the ring by the tensor-Hom
adjunction, and additive naturality extends invertibility to finite biproducts.
Reindexing a finite basis transfers this to every finite free module. A Hom
complex into the ring in degree zero has only one surviving product factor in
each degree, so this proves invertibility of the chain comparison, including for
unbounded sources. Postcomposition uses the given `j`. Self-duality of ring-module
endomorphisms under evaluation at one gives the required normalization by an
explicit construction of `u`.

The proof imports the generic transport and independent-universe adjunction
helpers, the ordinary canonical tensor comparison, the single-target Hom
helpers, and evaluation naturality. Added imports in the item are private proof
imports; the new helper publicly imports the definitions its statement needs.
No shared definition, existing public interface, target, or blueprint unit route changes.

Remote `lcompile.py --all` passed without warnings: the item compiled in 54.4 s
and the helper in 15.7 s. Both files meet the 60-second limit.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.ConstantCompletion.finiteFreeComplexDualPullback`.

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the item: 0.
The new helper `CategoryTheory.ConstantCompletion.ringComplexEndomorphism_selfDual`
is fully proved. No unfinished auxiliary theorem is introduced.

The argument includes finite rank zero, arbitrary coefficient maps, zero rings,
empty sites, and unbounded source complexes. It uses neither exactness of module
pullback nor preservation of infinite products.

## No longer needed

The planned dependency `lem-sfb-ringed-complex-tensor-pullback`, in
`Sheaf.Paper.RingedComplexTensorPullback`, is not used or imported. The ordinary
module tensor comparison suffices; constructing the total tensor comparison and
its unit coherence is unnecessary for this proof. This is a removal from this
node's proof dependencies, not a withdrawal of that module from other users.

No original import was removed: the original module had only its public
statement import, which is preserved. A scratch import of
`WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` was
removed because the contravariant finite-biproduct calculation uses the existing
basic biproduct identities directly.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned use of a total-complex tensor comparison
was stronger than necessary. The normalization can be established algebraically
from the dual comparison at the rank-one complex and self-duality of scalar
endomorphisms, without proving a separate pure-tensor formula for `u`.

The enclosing theorem in `RingedHomComplexPullbackShift` assumes exactness, but
its generic transport helpers used here require only additivity. No exactness
hypothesis is introduced. The DAG now records the ordinary comparison, the
finite-biproduct argument, collapse of the single-target Hom product, and the
actual algebraic normalization.

## New nodes

`lem-sfb-ring-complex-endomorphism-self-dual`, implemented by the proved
`CategoryTheory.ConstantCompletion.ringComplexEndomorphism_selfDual` in
`Sheaf.Paper.RingComplexEndomorphismSelfDual`, is the scalar self-duality identity
needed only for unit normalization. It is strictly a part of the argument and
has no `sorry`. It was moved into its own module after profiling and reducing
unfolding in the original complete proof: generic naturality and component
arguments, irreducible private constructions with explicit projection lemmas,
and an uncurrying API had reduced the single-file compile to about 60 seconds.
This self-contained proved algebra calculation allows both files to compile
separately below the limit. There is no definition or statement repair and no
change record is needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

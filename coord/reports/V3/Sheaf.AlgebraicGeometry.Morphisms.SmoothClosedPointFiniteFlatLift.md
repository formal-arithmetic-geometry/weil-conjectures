## What changed

Proved `AlgebraicGeometry.Scheme.exists_smooth_closed_point_finite_flat_lift` in
`Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointFiniteFlatLift`, with its existing
signature and public imports unchanged. Added one proof-only import:
`Sheaf.RingTheory.FiniteFreeLocalFieldFactorization`.

The new module proves `IsLocalRing.exists_finite_free_local_field_factorization`.
Its private, proved helper constructs one monic quotient at a time. Finite-set induction
then realizes a finite set of module generators of the prescribed field; the final
map is surjective because its image contains their entire module span. No data is
chosen from an unproved theorem.

The scheme proof first obtains a finite map `A → κ(x)` from the closed-fibre point,
using Mathlib's closed immersion and Jacobson finiteness lemmas. It applies the new
ring construction, derives Noetherianity and flatness from module finiteness and
freeness, and constructs the point by `pullback.lift`. Surjectivity of the residue map
of `Spec beta`, and injectivity of field maps, prove that the projection's residue
map is bijective, hence etale. The small private residue-surjectivity helper is proved
from surjectivity on stalks.

Updated the original DAG node's proof, proof dependencies and proof origin. Added a
node for the new, fully proved ring theorem. The unit route stays the residue-extension
base change of Tags 0EYB and 07NE. Read both source tags on the Stacks Project website;
the local checkout contains citation lists but no Stacks source files.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_smooth_closed_point_finite_flat_lift`
(node `lem-sbc-smooth-closed-point-finite-flat-lift`).

Added the fully proved theorem
`IsLocalRing.exists_finite_free_local_field_factorization`
(node `lem-sbc-finite-free-local-field-factorization`), with no added hole.
Both private helpers are also completely proved. No `sorry` remains in either
module. This is a proof, not a decomposition: holes closed 1, holes added 0.

Both modules compile together using `lcompile.py --all`, without warnings.
The delivery dry run checks axioms of every declaration. Edge cases: local rings and
fields are nontrivial; the original finite-free construction handles a degree-one
extension by its initial stage; inseparable extensions need no primitive-element
or separability assumption. An empty fibre admits no input point. The finite set
induction is valid for the empty set, and all constructions remain in `Type u`.

## No longer needed

None of the original public imports or DAG dependencies was removed: the original
node had no proof dependencies. No module is claimed pruned.

The proof does not use the general arbitrary-residue-field construction
`Sheaf.RingTheory.FlatLocalExtensionGivenResidueField`, its transfinite tower, or its
direct limit. Those modules were not imported before and are not imported now.
The finite polynomial-quotient construction gives the needed finite freeness directly.

## Where the brief, the DAG or earlier work was wrong

The node's three steps had empty `uses` lists despite requiring a finite free residue
realization. The new ring node makes that dependency explicit, and it is proved here.
No statement, definition or target interface was changed.

The literal `blueprint_refs.py ancestor` lookup for the item returns `None`, because
its `created.item` is a Lean module name. The new node instead inherits the original
node's recorded blueprint ancestor `sbc-thm-spreading-finite-etale-galois` and adds the
original node to its `via` list. The whole-blueprint search for "finite free local"
returned no matching blueprint statement.

## New nodes

`lem-sbc-finite-free-local-field-factorization`, in
`dag/nodes/sec-smooth-base-change/`, states and proves the algebraic part of Tag 07NE
for a local base ring. Its module is
`lean/Sheaf/RingTheory/FiniteFreeLocalFieldFactorization.lean`. Mathlib searches are
recorded from actual `msearch.py` calls: LeanSearch was unavailable, Loogle and
LeanFinder returned only component results, and source grep found the monic-ideal,
monic-power-basis and integral maximal-contraction lemmas used in the proof.
No change record is needed: all existing signatures and visibility stay unchanged.

## Second reading by V3

1. Compared both delivered Lean modules with the repository versions. The existing target
   signature is byte-for-byte unchanged; the only interface addition is the explicitly
   recorded new factorization module and node.
2. Compiled both modules with `lcompile.py --all`; compilation is clean. The delivered
   declarations contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow
   definitions; their proofs use only the permitted foundational axioms.
3. Checked the factorization statement and its finite-set induction on empty and
   singleton cases, and checked that the scheme theorem supplies exactly the stated
   local, finite, flat lift and etale residue map. The new statement is true and is
   strictly the algebraic reduction needed by the target.
4. Reviewed the proof route against the available Mathlib declarations and the source
   tags. The finite polynomial-quotient construction is the shortest available route;
   no unnecessary proof-only import or old dependency is present.
5. The DAG proof, proof dependencies, proof origin, and new node agree with the Lean
   declarations. The unit route remains the residue-extension base change through the
   recorded Tags 0EYB and 07NE steps.

I changed only this report section; no Lean proof or statement required repair.

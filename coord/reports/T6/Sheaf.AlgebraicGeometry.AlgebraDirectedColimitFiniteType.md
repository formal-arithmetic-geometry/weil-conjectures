## What changed

Proved `AlgebraicGeometry.Scheme.CommAlgebraSheaf.directed_colimit_finiteType` with its
statement unchanged. Use the existing multiplication-image and symmetric-images theorems,
and the directed finite-presentation module theorem. Construct the inclusion cocone at A.
A proved private helper constructs the ring colimit of a directed union, for arbitrary
index universes, from Mathlib's filtered-colimit criterion for types; its ring-operation
checks move two representatives to a common stage. Extend the affine universal maps using
the affine-basis morphism equivalence, check the structure map through any one stage,
and establish factorization and uniqueness. No objects are chosen from an unfinished
existence theorem to define new library data.

Updated the existing node's proof, proof dependencies and proof origin to this route.
The declaration docstring now records the actual proof. Public imports and signatures
are unchanged. A theorem-local transparency option and a named affine component equation
avoid repeated unfolding of the universal sheaf map. No other module was changed.

Searches: msearch leanfinder for directed unions of subsheaves found scheme-gluing
colimits, not this theorem; loogle found no applicable result; msearch grep and local rg
found Mathlib's filtered-colimit criterion for types and the affine-basis extension API.
Read the declared dependencies and Stacks Properties 05JS/05JT. The unit route is retained.

Validation: lcompile.py compiled the complete item without warnings or local holes.
The delivery preflight performs the declaration/axiom probe. The proof still uses the
existing unfinished construction theorems, as intended by stage 3.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.CommAlgebraSheaf.directed_colimit_finiteType`
(node `lem-weil-pbc-algebra-directed-colimit-finite-type`). Added 0 holes; split off 0.
No `sorry` remains in the item or is added elsewhere. The private helper `ringUnionIsColimit`
is fully proved. This closes the item from the existing declarations; it does not claim
that their transitive proofs are finished.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`
- `WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`

The item no longer depends directly on `lem-weil-pbc-quasi-coherent-algebra-colimit` or
`lem-weil-pbc-filtered-colimit-algebras-elementwise`: the affine cocone is shown to be a
ring colimit directly, then its universal maps extend from the affine basis. The node's
proof dependencies now say this. The remaining removed imports were components of the
old unsplit construction plan; their uses are encapsulated by the two declared construction
lemmas, rather than repeated here. Some remain transitively needed by those lemmas or
other modules; no module is withdrawn and no claim of global pruning is made.

## Where the brief, the DAG or earlier work was wrong

The Lean docstring and imports still described the older unsplit proof, although the DAG
already exposed the multiplication-image and symmetric-images lemmas. The recorded
algebra-colimit theorem takes an index in Type u, whereas the full subobject subtype has
a larger universe. The direct affine universal-property proof works for that index
without changing any definition or statement. No mathematical statement was found false.
The empty scheme is covered: nonemptiness comes from the nonempty module index, not from
choosing an affine point; basis extension and uniqueness also apply to the empty basis.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

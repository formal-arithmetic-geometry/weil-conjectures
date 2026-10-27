## What changed

Proved `AlgebraicGeometry.finiteLocallyFree_principalBasisCover` without changing its
statement or either auxiliary definition. All changes to Lean are inside the assigned module.
The proof first obtains the fixed rank and quasi-coherence from the existing structure-sheaf
result. It restricts the local free isomorphisms to principal opens and extracts a finite
subcover indexed by `Fin m`. Indexing by actual points ensures the cover is empty for the
zero ring and each retained open is nonempty.

The canonical identifications use structure-sheaf localization directly on `Spec A` and
`Spec B`. Restricting scalars makes the localization at the image of `f` an A-module
localization at `f`; its universal property supplies the additive equivalence, and the
fraction multiplication formula supplies the algebra localization ring equivalence.
Extension of scalars proves compatibility with `A_f`. Finally, the coordinate basis of the
free sheaf on sections is transported through the ring and additive equivalences. The
projection-inclusion identities prove the required equation on each generator.

Added private proof imports of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` and
`Mathlib.RingTheory.Localization.Module`. Updated the item's DAG proof and dependency list
to reflect the direct structure-sheaf argument. No shared interface changed, no other module
was adapted, and no target or unit route changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteLocallyFree_principalBasisCover`
(node `lem-a1-finite-locally-free-principal-basis-cover`).
Added zero holes, split off zero statements, and left no `sorry` in the delivered module.
All five private helper theorems have complete proofs. The complete file compiled through
`lcompile.py` in 43.4 seconds; the sole unused-simp warning was then removed. The delivery
command performs the final clean compile and declaration-axiom checks.

The edge cases include the zero ring, rank zero, and principal opens that are empty.
Localization equivalences are constructed for every `f`, including nilpotent `f`, and only
the cover selection discards empty opens. The coordinate arguments use finite types and
therefore also apply to `Fin 0`. No Noetherian or global freeness hypothesis was added.

## No longer needed

Removed the proof imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.AlgebraicGeometry.ResidueField`, and
`Mathlib.AlgebraicGeometry.AffineScheme`.

The proof no longer needs node
`lem-weil-pbc-affine-module-basic-open-localization`, whose two declarations are
`Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen` and
`Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
The module sheaf here is specifically a structure-sheaf pushforward, so localization of
structure-sheaf sections on the source spectrum gives its sections directly. Removed that
node from `proof_deps`, the step uses, and the top-level `tool_uses` list. This does not
withdraw or change the upstream declarations or assert that their module has no other users.
All the other originally declared mathematical dependencies remain in use.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned generic quasi-coherent section-localization
argument was unnecessary for this particular pushforward. The shorter direct affine
structure-sheaf argument is the only mathematical change of route.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

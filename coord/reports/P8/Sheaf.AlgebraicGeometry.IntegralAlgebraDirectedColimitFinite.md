## What changed

Proved `AlgebraicGeometry.integral_algebra_directed_colimit_finite` without changing its
signature, hypotheses, universes, or public imports. Added proved private helpers for
integrality of subalgebras, functoriality of constructed symmetric algebra sheaves,
affine identification of universally characterized quotients, and finite presentation.
The second colimit is proved directly on affine sections before restricting to the
cofinal directed subtype of eventually finite quotients. Updated the existing DAG node
to match this argument. No other library module is changed.

The source read was Stacks Properties Tag 0817, the complete proof at properties.tex
lines 3424–3496, together with its stated interfaces for Tags 01PK, 05JT, and 086N.
All compilation uses the project compile server. The delivery preflight checks every
new declaration's axioms and direct holes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.integral_algebra_directed_colimit_finite`: 1 of 1 proved from the
existing stated dependencies. Zero holes remain in the item; zero holes added; zero
statements split off. Every new private helper has a complete proof.
Change record: `coord/changes/P8-integral-algebra-proof-commands.md` records the local
namespace and elaboration commands requested by the static checker. Public types and
imports are unchanged; no consumer adaptation is needed.

The theorem still uses existing named dependencies with postponed proofs, as intended
by stage 3; this report does not claim their transitive axioms have been eliminated.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.FinitePresentationHomDirectedColimit`: its lifting argument
  is already packaged in the retained `KernelIdealDirectedPairs` dependency.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`: use the constructed symmetric
  algebra's core universal property and affine comparison directly.

The item no longer directly needs these planned nodes:
- `lem-weil-pbc-quasi-coherent-symmetric-algebra`: replaced by its core and affine nodes.
- `lem-weil-pbc-generated-ideal-quotient-colimit`, module
  `Sheaf.AlgebraicGeometry.GeneratedIdealQuotientColimit`: direct affine-section colimit
  comparison proves the required total colimit without constructing separate row colimits.
- `lem-weil-pbc-directed-pairs-colimit-transitivity`, module
  `Sheaf.CategoryTheory.DirectedPairsColimitTransitivity`: the same direct comparison
  avoids iterating the row and base colimits.
- `lem-weil-pbc-filtered-colimit-rings-zero`: no converse equality criterion is needed;
  a cocone identity sends each representative that vanishes later to zero in the colimit.

These are dependency-edge prunings for this item, not withdrawals of those modules or
claims that no other target route uses them. The finite-presentation Hom lemma remains
needed transitively through KernelIdealDirectedPairs. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The old module docstring described an older
nine-step plan, while the current DAG had already introduced four additional interfaces.
The proof and docstring now give the implemented route. The quotient-pairs interface
specifies its quotient by a universal property; the proof compares it with the existing
generated-ideal quotient to obtain the affine kernel and surjectivity facts, instead of
assuming them. Finiteness is transported through the actual affine ring quotient
isomorphisms. The empty affine open and empty generating lists are covered by the ring
lemmas; nonemptiness of both directed approximations handles choices of row indices.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

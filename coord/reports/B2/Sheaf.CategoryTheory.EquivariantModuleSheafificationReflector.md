## What changed

Proved `CategoryTheory.InternalActionSite.equivariantModuleSheafification_reflector`
in `Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector`, preserving its full
signature and every public import. All construction helpers are private and proved.
The action is the unique extension of the set-valued action through the product of
K with the ordinary module sheafification unit. Local preimages and separatedness
prove its group and linearity laws, uniqueness, and equivariance of ordinary module
extensions. Natural hom-set bijections give the reflector and adjunction. The comparison
with ordinary module sheafification has identity components and preserves its unit.
The copied DAG proof now describes this implementation.

Validation: the final module compiled cleanly through lcompile.py in 20.7 seconds.
No declaration signature, universe, attribute, public import, or existing docstring changed.

Searches used the launcher LeanFinder, Loogle, and grep services, plus source searches
in Mathlib, WeilConjectures, and Sheaf. Ordinary sheafification APIs suffice; no existing
internal-equivariant reflector was found. The four recorded proof dependencies are all
used through their Mathlib declarations.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.InternalActionSite.equivariantModuleSheafification_reflector`
(node `lem-sfb-equivariant-module-sheafification-reflector`). Added 0 holes; split off 0.
No sorry remains in the delivered module. Existing dependencies in
`InternalActionSitePresentation` retain their own proof obligations.

## No longer needed

No DAG dependency, node, or module was pruned. No new proof-dependency module is needed:
the four dependencies are Mathlib leaves. The redundant private import
`Mathlib.CategoryTheory.Sites.Sheafification` was removed; it is already imported
publicly by the existing module sheafification import. All existing public imports stay.

## Where the brief, the DAG or earlier work was wrong

The assertion is correct as stated. The construction actually works for an arbitrary
presheaf of groups K: only id_K times the sheafification unit needs to be inverted,
so hK is unnecessary for the proof. Its hypothesis and the finite-limits hypothesis
remain in the signature unchanged. Local preimages give a shorter implementation of
the law checks than constructing all the finite-product sheafification comparisons.
There are no new statements, definition repairs, or consumer adaptations.
The static gate treats the local section/variable commands as potentially visible;
`coord/changes/B2-equivariant-sheafification-private-proof-context.md` records their
scope and the two downstream modules. Neither existing signature nor semantics changes.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

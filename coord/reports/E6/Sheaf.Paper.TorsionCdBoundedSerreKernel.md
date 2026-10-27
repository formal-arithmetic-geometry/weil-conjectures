## What changed

The statement of `AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_kernel` is unchanged.
Its proof now treats finite discrete coefficients directly, using
`FiniteDiscreteOrdinary.finiteDiscrete_serreHeart_cohomology_vanishes`, exact coefficient
restriction, and kernel closure of the weak Serre coproduct hull. The coefficient-lift
and transport arguments are private proved helpers, adapted from the already proved
finite-coefficient theorem in `TorsionCdTopologicalSerreTransfer`; importing that parent
would create an import cycle.

For the remaining four topological coefficients, the proof uses the actual short exact
sequence `0 -> kernel f -> M -> Abelian.coimage f -> 0`. Two separate geometric
comparison statements remain: strict high-degree coimage vanishing and surjectivity
of the source-to-coimage map in degree d+2. Exactness proves the kernel bound above
d+3 from the first. At q=d+3 the second makes the connecting map zero by epimorphism
cancellation; the other map has zero target by the input source bound. These are
separate degree ranges and different conclusions, not a renamed kernel theorem.

New proof imports are the two substep modules, the derived homology sequence API,
finite discrete comparison, coefficient-isomorphism constructibility, derived
composition, kernel closure, and module pullback coherence. All are private proof
imports. No existing public declaration, definition, target, or public import changes.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_kernel` (one original hole).
The finite discrete coefficient branch is fully proved from existing declarations.
The topological branches are a decomposition, not a completed geometric proof.

Added two holes, each the whole proof of one named public theorem in its own module:

- `AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_coimage`, node
  `lem-sfb-torsion-cd-bounded-serre-coimage`.
- `AlgebraicGeometry.ProEtale.torsionCd_critical_coimage_surjectivity`, node
  `lem-sfb-torsion-cd-critical-coimage-surjectivity`.

The item module has zero remaining direct holes. The delivery has two direct holes
in total: one hole closed, two added (net minus one). All three delivered modules compile within the single-file limit. The item proof
uses no additional axioms beyond its imported statements. No hole is placed in a definition
or private helper. The new statements exclude finite discrete coefficients, for which
no residual obligation is needed. They retain both input bounds and the actual maps.

## No longer needed

No existing public imports are removed. The item's former direct planned dependency
on `lem-sfb-condensed-sections-ind-vanishing` is delegated to the geometric comparison
substeps; it is not a direct ingredient of the exact-sequence assembly. Its module is
not withdrawn and remains needed by those substeps and other parents. The finite
discrete Serre-heart node remains used, with coefficient-isomorphism transport added.

No module is claimed globally pruned. The unit statement and its route are retained.
The proof does not import the invalid unrestricted finite-heart approximation, the
Noetherian specialization, or a supported-image generation theorem that would not
supply the missing cohomological comparison. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The existing node correctly warns that the kernel step is not a consequence of the
long exact sequence alone. The supplied relation-resolution text is an unresolved
geometric obligation, rather than a fully stated chain of comparison theorems.
HRS Section 8 motivates finite cohomological bounds but does not itself establish this
arbitrary-affine weak Serre hull assertion; the exact full-generality source remains
WANTED, as in the original node.

The degree distinction matters: vanishing for the coimage only above d+2 does not
settle kernel cohomology in degree d+3. The new critical surjectivity node records
exactly that additional obstruction. No stronger image bound was silently assumed.
The zero map has zero coimage; for an isomorphism its coimage quotient is invertible.
Those cases, empty schemes, zero modules, and arbitrary affine non-Noetherian bases
are consistent with both substep statements. No completeness of an arbitrary kernel,
finite-heart presentation, or added Noetherian hypothesis is assumed.

## New nodes

`lem-sfb-torsion-cd-bounded-serre-coimage` states strict upper coimage vanishing for
the four topological coefficient types. It isolates the high-degree part of steps 2
and 3 of the original node; no claim is made in the critical degree d+2.

`lem-sfb-torsion-cd-critical-coimage-surjectivity` states the lifting of coimage
cohomology in the single degree d+2 along the actual source-to-coimage quotient.
It isolates the boundary obstruction in the same relation comparison. It asserts no
upper bound in other degrees. Both nodes have source, proof text, searches and exact
Lean attachments. The original node's proof and proof dependencies now match the
finite comparison and long exact sequence assembly. No change record is required:
existing statements, definitions and public imports are unchanged.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

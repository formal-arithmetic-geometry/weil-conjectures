## What changed

Completed `AlgebraicGeometry.closed_component_stalk_calculus` in
`Sheaf.AlgebraicGeometry.ClosedComponentStalkCalculus`, preserving its entire statement.
Private proved helpers identify the supremum of affine germ ideals with the image from
any fixed affine neighborhood, commute stalk ideals with suprema and finite infima,
and compute the unit ideal outside the support. The canonical ambient localization
equivalence and the existing proved `Scheme.Hom.ker_stalkMap` give the closed-immersion
quotient equivalence, including its formula on section germs.

The reduced component family is the finite set of irreducible components of H, mapped
through the closed embedding and enumerated without repetitions. Reducedness and the
support identify its union with H. For components through x, affine vanishing ideals
are prime and their extensions to the stalk are prime. Contraction and density show
that an inclusion of these stalk ideals reverses inclusion of the global components;
maximality makes their ideals an antichain. A finite intersection of this prime
antichain has exactly these minimal primes. Components missing x contribute unit
ideals and are removed from the intersection.

Updated the node proof, proof dependencies and proof origin to this implementation.
No statement, definition, public import, consumer or upstream source file changed.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.closed_component_stalk_calculus`
(node `lem-sfb-closed-component-stalk-calculus`). Proved 1 of 1 original sorries.
Added zero holes; split off zero statements. Every private helper is fully proved.
The item module has zero remaining sorries.

The proof handles the empty closed subscheme and empty finite families: the empty
sum is zero and the empty intersection is the unit ideal. Off H no component contains
x and the unit stalk ideal has no minimal primes. No regularity or integrality of X
is introduced. Neither theorem signature nor existing docstrings were altered.

## No longer needed

Removed proof import `Mathlib.AlgebraicGeometry.Modules.Tilde`.
The node no longer needs `lem-weil-pbc-spec-tilde-stalk-localization`: affine restriction
compatibility and a common affine refinement directly identify the germ ideals.
The node no longer needs `lem-weil-pbc-localization-at-prime-of-quotient`: the existing
proved closed-immersion stalk kernel formula, surjectivity and the first isomorphism
theorem directly give the canonical quotient equivalence. Their shared Mathlib modules
remain available to other consumers; no module is withdrawn.

The open-subspace, spectrum irreducibility, prime-localization, finite-component,
reduced-induced-structure and integral-scheme dependencies remain used. No unit
statement or unit proof step is bypassed. No additional modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan is valid but longer
than necessary: a tilde-module stalk comparison and a separately constructed localized
quotient are unnecessary given the already proved affine germ and stalk-kernel APIs.
The component bijection is established by the finite prime-antichain intersection
argument after showing that localization reflects inclusions for components through x.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

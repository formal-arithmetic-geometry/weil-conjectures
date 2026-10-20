## What changed

Proved `CategoryTheory.point_family_conservative` in
`Sheaf.CategoryTheory.Sites.PointFamilyConservative`, preserving every existing signature,
definition and public import. The local identity `hnat` follows from
`sheafifyLift_comp` and `uliftYonedaEquiv_symm_comp`. Section separation then proves
joint faithfulness, and `JointlyFaithful.jointlyReflectsIsomorphisms` applies using
`SheafOfTypes.balanced`. Updated the theorem docstring and the item's DAG proof,
proof dependencies and proof origin to describe this shorter argument.

The server compiled the finished module without warnings in 1.3 seconds. A temporary
`#print axioms CategoryTheory.point_family_conservative` check reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; the diagnostic command was then removed.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.point_family_conservative`
(node `lem-trf-point-family-conservative`). Proved 1 of 1 sorries; added 0 holes;
split off 0 statements. No sorry remains in the delivered module or any added module.

## No longer needed

The proof no longer needs `lem-weil-pbc-left-adjoint-preserves-colimits` or
`lem-galois-epi-iff-cokernel-pair`: joint faithfulness reflects epimorphisms directly
by cancellation, so neither a pushout nor preservation of colimits is required.
`def-trf-geometric-morphism` is removed from proof dependencies; its module remains
necessary for the unchanged statement, and only its `inverse` projection is used.
The adjunction and finite-limit-preservation fields are not needed by the proof.
The site-axiom hypothesis `hJ` is also unnecessary for the argument and is preserved
verbatim for interface stability, with an explicit reference suppressing the unused-variable
warning. All five existing public imports are needed for the file's public interface
and its definitions, so no import or module is removed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's pushout/cokernel-pair route was longer than
necessary: section separation already gives joint faithfulness, and Mathlib supplies
the cancellation argument and balancedness criterion. The unit `sk-i-curve-zero`
has no realized statement or step attached to this node, and the unit route is unchanged.
The argument covers empty index families and empty categories: separation still forces
equality of any relevant section values, so joint faithfulness and balancedness apply
without any nonemptiness assumption. No new statements, definition repairs or consumer
adaptations were needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

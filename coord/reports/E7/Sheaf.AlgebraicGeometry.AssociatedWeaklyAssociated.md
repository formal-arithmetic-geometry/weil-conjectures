## What changed

Proved `AlgebraicGeometry.associated_iff_weaklyAssociated_of_fg_stalk` in
`Sheaf.AlgebraicGeometry.AssociatedWeaklyAssociated` by specializing
`Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg` to the local ring
`X.presheaf.stalk x`, its maximal ideal, and the module
`(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F`.
Mathlib supplies primality of the maximal ideal by typeclass inference; the
finite-generation hypothesis is passed unchanged. This implements the existing
DAG proof, with no statement, definition, node, or unit-route changes.
Removed the unused private import of the presheaf-level stalk functor.

Validation: the item compiles through `lcompile.py`. The proof explicitly
references `hF`, since the algebra lemma applies to every module. This avoids an
unused-variable warning while preserving the original quasi-coherence binder
and the entire theorem signature unchanged.

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.associated_iff_weaklyAssociated_of_fg_stalk`
(node `lem-sc-ass-weakass-fg-stalk`).
There are zero remaining holes in the item, zero holes added, and zero split-off
statements. The proof uses the existing, still-unproved declaration
`Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`
(node `lem-sc-ass-weakass-fg-prime`); its proof remains a separate item, as intended
by this stage. This delivery does not claim that dependency is proved.

## No longer needed

Removed direct private import
`WeilConjectures.Topology.PresheafModuleStalkFunctor`: the statement and proof use
the ringed-space stalk functor already provided by the retained public import
`WeilConjectures.Algebra.Homology.ModuleStalkFunctor`.
No DAG dependency is withdrawn: `def-weil-pbc-module-stalk` still identifies the
stalk notion, and `lem-sc-ass-weakass-fg-prime` is used exactly as planned.
No declarations, nodes, or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The stated algebra lemma has exactly the needed hypotheses and conclusion.
The unit record has no realized steps that this specialization bypasses.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

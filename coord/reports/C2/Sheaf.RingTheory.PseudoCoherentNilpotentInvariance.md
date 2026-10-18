## What changed

Proved `DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel` in
`Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`, keeping its signature and visibility
identical. All added helpers are private and fully proved; no other Lean module changed.
Their additional namespaces and tensor notation are opened only for each private helper.

The forward direction computes the universal counit on a bounded-above free complex.
Because the existing monoidal/K-flat API has equal ring and module universes, the proof
raises both rings with `ULift`, transports ordinary scalar extension by uniqueness of left
adjoints, transports universal derived functors through equivalences, applies the existing
K-flat counit theorem, and reflects the resulting isomorphism back. Termwise tensoring
preserves the upper bound, freeness, and finiteness.

The reverse direction transports the given universal pair and reduced finite-free model
along `A/ker φ ≃ B`, then applies the declared nilpotent projective-complex lifting theorem.
In each degree a lifted finite basis and nilpotent Nakayama prove finite generation.
`ModuleCat.free_of_free_extendScalars_mod_ideal` then proves freeness, since units lift
modulo the nilpotent ideal. This includes empty bases and zero rings.

Updated the existing node's proof, proof dependencies, and proof origin to match this
implementation. Removed its obsolete top-level derived-change-of-rings tool-use approval.
No definitions, public statements, target signatures, or consumers changed.

Validation: the complete module compiled through `lcompile.py`, both before and after
import pruning (7.5 s and 8.9 s respectively), with no warnings. The dry run initially flagged global `open` commands as an interface
change; these were localized to the private helpers. A literal comparison with
the repository confirms the theorem signature is unchanged. All lines have at most 100
characters and the delivered module has zero `sorry` tokens.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel`
(node `lem-weil-pbc-pseudo-coherent-nilpotent-invariance`). Added 0 holes; split off 0
statements; 0 holes remain in the delivered module. This is a proof from existing declared
dependencies, not a decomposition into new obligations.

The proof intentionally uses the previously declared
`CochainComplex.exists_projective_lift_of_nilpotent`
(node `lem-weil-pbc-nilpotent-projective-complex-lift`), whose proof remains an existing
upstream obligation. Its statement is used unchanged, with the full universal derived
functor and prescribed reduced-complex identification supplied by the proof here.

## No longer needed

Removed direct imports:
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`;
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`;
- `Sheaf.RingTheory.NakayamaNilpotent` (retired wrapper, replaced by its source-library module).

Also removed the exploratory `Mathlib.CategoryTheory.Functor.KanExtension.Preserves` import;
the proof uses the elementary right-extension equivalence API already available from the
original derived-functor imports.

Removed `lem-pur-derived-change-of-rings` from this node's proof dependencies and top-level
`tool_uses`: the forward computation uses the existing module theorem
`lem-pc-kflat-scalar-extension-counit` instead of constructing a one-object-site bridge.
Its statement-dependency entry is retained, and its module is still reached transitively
through the projective-complex lifting dependency, so this delivery does not claim that
node or its module is globally unreachable. No other original proof dependency is pruned.

Added existing proved tools `lem-pc-kflat-scalar-extension-counit` and
`lem-sc-finite-projective-free-mod-ideal` to the proof dependency list. Both are generic
module lemmas; the proper-base-change unit's realized statement and proof steps are kept.
No new tool-use approvals are written by this worker.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed or changed. The proposed forward proof required a
one-object-site/module equivalence that was not a supplied declaration, and the existing
module K-flat API has the ring universe equal to the module universe, whereas this theorem
allows modules in `max u v`. The proof supplies an actual `ULift` transport rather than
changing the signature or identifying independent universes. The reverse quotient lift
also needed transport of the universal counit, which is supplied explicitly.

The explicit split-kernel calculation in the DAG is unnecessary after finite generation:
the already proved finite-projective freeness criterion applies. There are no forced
adaptations and no new nodes.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

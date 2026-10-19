## What changed

Proved four of the five original theorem holes in
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`, retaining every existing declaration
signature, definition, and public import. No new public declarations or holes.

`finiteCoefficientModulePullback_additive` uses additivity of sectionwise pushforward
and its left adjoint, then composes the small-model transports and restriction of scalars.
`finiteCoefficientModulePullback_exact` constructs the ring-unit presentation over the
AsSmall model, applies the existing module inverse-image action adjunction comparison,
and transports its underlying abelian comparison back. The faithful exact forgetful
functor reflects short exactness; the additive exactness criterion supplies finite limits
and colimits. Private proved helpers adapt the existing commutative model-ring and
underlying-module comparison arguments to RingCat, so no commutativity is assumed.

`finiteCoefficientCommRing_preservesSheafification` preserves the locally bijective
characterization of sheafification equivalences. `finiteCoefficientCommRingMap_isIso`
identifies the specified canonical map with uniqueness of left adjoints for the two
constant-sheaf adjunctions. This argument does not require finiteness or discreteness;
the original hypotheses are retained, with the unused-section-variable linter disabled
only for this theorem.

Added proof-only imports for the generic module action adjunction, the unit-compatible
forgetful comparison, flat left Kan extension, exact module forgetful functor, ring
limits, and reflection of short exact sequences. Updated the existing node proof and
proof dependencies to describe this route. No definition repair or consumer adaptation.

Preflight requires the scope-command change record
`coord/changes/F4-proetale-constant-exact-private-scopes.md`; it documents the
unchanged public signatures and all direct importers.

## Proved and sorry left

Original holes: 5. Closed: 4. Added: 0. Split off: 0.

Closed, in namespace `AlgebraicGeometry.ProEtale`:
- `finiteCoefficientModulePullback_additive`.
- `finiteCoefficientModulePullback_exact`.
- `finiteCoefficientCommRing_preservesSheafification`.
- `finiteCoefficientCommRingMap_isIso`.

The only remaining hole is
`AlgebraicGeometry.ProEtale.finiteCoefficientModulePullback_tensor`, attached to
`prop-weil-pbc-proetale-constant-exact`. Its original complete proof docstring and
statement are retained. It still needs the natural comparison of RingCat and
CommRingCat module inverse images with the canonical coefficient maps, followed by
tensor cancellation along the coefficient isomorphism. No new lemmas with sorry.

## No longer needed

Removed the proof-only imports `Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, and
`Sheaf.CategoryTheory.RingedSiteModules`. The last three remain available through
existing public imports, so their redundant direct proof imports are unnecessary. The first
two imports correspond to the nodes
`lem-weil-pbc-site-pullback-abelian-exact` and
`def-weil-pbc-sites-and-cohomology` are not needed by the implemented proofs:
Mathlib supplies left exactness of flat abelian inverse image directly, while the
existing ring presentation and module-action adjunction handle its scalar structure.
The separate precoverage exactness theorem is therefore unnecessary here. Removed
these two entries from this node's top-level tool approvals; their use elsewhere is
unaffected. No blueprint unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The declared abelian exactness result alone does not
provide a comparison with the module Kan extension chosen in this file. The existing
generic action-adjunction and unit-compatible forgetful comparison supply this glue.
The existing ProEtaleModelRingPresentation and ProEtaleModuleInverseImageComparison
proofs specialize to CommRingCat; this item needs RingCat for noncommutative rings,
so their transport arguments were adapted as private proved helpers.

An initial direct use of generic sheafification-preservation instance search was slow;
the locally bijective argument avoids that search. An initial generic module comparison
triggered expensive definitional equality; specializing its statement to the actual
finite-coefficient definitions makes the current proof compile within the file gate.
The zero ring and empty scheme are included: no nontriviality, nonemptiness, or
flatness of the scheme morphism has been added. Terminal preservation is a property
of site base change for every scheme morphism.

Validation (2026-10-19): checked the retained module against the current repository.
The latest resumed dry run passed: commit `a74d0cb662` compiles and passes preflight,
including the axiom probe. Its review class is CODEX because the delivery includes
an updated node, a scope-command change record, and private helper scope commands.
The current direct importers were rechecked; no consumer adaptation is required.

Resumed verification: reread the worker/stage rules, the original and sandbox module,
the node and unit realization, the generic action-adjunction dependency, and Stacks
labels lemma-pullback-module, lemma-adjoint-push-pull-modules, and
lemma-flat-pullback-exact. The current direct-importer list agrees with the change
record. The remaining tensor comparison was checked against the existing ordinary
module operations: uniqueness of left adjoints offers an alternative to constructing
the tensor cancellation maps, but still requires compatibility of the canonical
RingCat and CommRingCat coefficient maps. The existing finite module adjunction
imports this item, so importing it here would create a cycle. No proof of that last
compatibility or tensor comparison is claimed. No delivery was pushed before this
resumption; the completed dry run above pushed nothing.

Final resumption check: compared the entire retained module with the current source,
rechecked the RingCat and abelian private transports against the existing comparison
modules, confirmed the generic dependency is acyclic, and reran the downstream query.
All 57 direct importers agree with the change record; their interfaces are unchanged.
The current dry run passed compilation and preflight as CODEX. This delivery retains
the four completed proofs, the original tensor hole, and zero added holes.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

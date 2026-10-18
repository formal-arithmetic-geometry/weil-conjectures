## What changed

Proved `CategoryTheory.constant_ring_module_sheaves` in
`Sheaf.CategoryTheory.ConstantRingModuleSheaves`. Constructed the extended module action
on the original abelian sheaf using `PresheafOfModules.sheafify` with its identity abelian
unit. Used `restrictHomEquivOfIsLocallySurjective` to establish linearity of every original
linear map and uniqueness of the extended action. Constructed the inverse functor and both
natural isomorphisms with identity maps on sections, proved additivity, and proved the
required equality of underlying abelian-sheaf functors by reflexivity.

All existing signatures and definitions are unchanged. The new helpers are private and
fully proved. Updated the existing node's proof and proof_origin to record the identity-unit
specialization of the same module-sheafification argument. Its dependencies remain unchanged.

## Proved and sorry left

Closed the single original hole: `CategoryTheory.constant_ring_module_sheaves`
(node `lem-cbc-constant-ring-module-sheaves`). Proved 1 of 1 original sorries; added 0 holes;
0 sorries remain in the delivered module. No decomposition or new modules.

The retained proof compiled cleanly through `lcompile.py` in 6.9 seconds before final cleanup.
The delivery gates provide the final compilation and axiom checks.

## No longer needed

Removed the redundant proof-only import
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: the needed construction and
restriction Hom equivalence are already available through
`Sheaf.CategoryTheory.RingedSiteModules`, which imports Mathlib's module-sheaf abelian API.
No DAG dependency or project module is pruned: `lem-cbc-sieve-module-sheafification` and
`def-weil-pbc-sheafification` are still used. The separate construction of an inverse to the
usual abelian sheafification unit and transport along that inverse are unnecessary, because
Mathlib accepts the identity map to the already-sheaf underlying abelian presheaf directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The original proof plan did more work than required
by constructing and transporting along a sheafification isomorphism. The identity-unit
specialization supplies the same action directly on the original sections. The arbitrary
covering-sieve scope and the unit route are preserved. Empty sites, zero coefficient rings,
and empty covering sieves require no extra hypothesis: all constructions and uniqueness
arguments use the general Mathlib sheafification and local-surjectivity APIs.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

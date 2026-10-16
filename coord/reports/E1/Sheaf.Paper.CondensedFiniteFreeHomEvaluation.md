## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_finite_free_hom_evaluation` with its
original signature. The proof derives the ordinary internal-Hom evaluation
isomorphism, uses the composition theorem for total right derived functors, and
identifies the right derived internal-Hom functor with its termwise construction.

Added three fully proved helper modules:

- `Sheaf.CategoryTheory.DerivedCoyonedaEvaluation`: the unbounded derived additive
  coyoneda evaluation isomorphism in every integer degree. It reuses the existing
  proved abstract Hom-complex, homotopy, and K-injective helpers in
  `Sheaf.Algebra.Homology.LocallyFreeDerivedHom` through `import all`.
- `Sheaf.Paper.CondensedInternalHomSections`: ordinary internal-module evaluation,
  proved directly using the free-module and tensor-Hom adjunctions and evaluation
  at the terminal pro-etale object.
- `Sheaf.Paper.CondensedFiniteFreeTensorExact`: tensor preserves finite limits,
  first by uniqueness of left adjoints in the finite free case, then by pullback
  compatibility and conservativity along a trivializing cover. It reuses proved
  finite-free and covering helpers in `CondensedFiniteFreeInternalHomColimits`.

Updated the item's node to describe this route. No existing statement, definition,
visibility, target, unit, or chapter was changed. All new imports in the existing
item are proof imports. The new generic lemma treats arbitrary unbounded complexes;
the tensor argument includes rank zero and the empty scheme.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.condensed_finite_free_hom_evaluation`.

The new public lemmas are also completely proved:
`CategoryTheory.derived_coyoneda_evaluation`,
`AlgebraicGeometry.ProEtale.condensed_internal_hom_sections`, and
`AlgebraicGeometry.ProEtale.condensed_locally_free_tensor_preservesFiniteLimits`.
Every private helper is proved. No holes were added and no `sorry` remains in any
delivered Lean file. This is a proof, not a decomposition.

The item and the three helper modules compile. Direct `#print axioms` checks for
all four public theorems reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. The required delivery dry run supplies the final compilation and
axiom checks.

## No longer needed

Removed the item's direct proof import
`Sheaf.Algebra.Homology.LocallyFreeDerivedHom`. The public ringed-site theorem
`CategoryTheory.locallyFree_derivedHom` and its node
`lem-weil-pbc-ringed-site-locally-free-derived-hom` are no longer proof dependencies
of this evaluation statement. In particular, the proof needs no transport of
internal module objects to external ringed-site modules and no bounded-below
reduction.

The `LocallyFreeDerivedHom` module itself remains imported transitively because
its already proved generic helpers are reused. No whole existing module is made
unreachable by this delivery. All remaining imports are used; no other planned
dependency of this item's original node was removed.

## Where the brief, the DAG or earlier work was wrong

The old plan proposed transporting the ringed-site evaluation theorem, whose
public interface is bounded below and in degree zero, to this unbounded internal
module statement. That interface does not directly supply the required result.
Its existing generic private helpers do supply the Hom-complex calculation,
allowing the unbounded comparison to be proved directly without changing it.

The published compiled library initially lacked
`Sheaf.Paper.CondensedFiniteFreeInternalHomColimits`, although its fully proved
source was present. An unchanged copy of that existing source was compiled as a
local dependency for verification and then removed from the delivery; it was not
rewritten or adapted. Its compiled local artifact is used by the sandbox.

The unit's finite locally free calculation and evaluation route is preserved.
There are no statement disputes and no forced adaptations.

## New nodes

`lem-weil-pbc-derived-coyoneda-evaluation` records the proved generic unbounded
comparison between derived additive coyoneda and maps from a single object.

`lem-weil-pbc-condensed-internal-hom-sections` records the proved ordinary
internal-module evaluation isomorphism, without freeness assumptions.

`lem-weil-pbc-condensed-finite-free-tensor-exact` records the proved local-to-global
finite-limit preservation of the tensor functor.

All three nodes are in `dag/nodes/sec-proper-base-change/`, with complete proofs,
Lean signatures, source references, and three kinds of Mathlib searches. LeanSearch
was unavailable and is recorded as such; semantic searches and source searches
found ingredients, which the proofs reuse, but no exact existing statements.
There are no change records because no existing interface changed.

## Second reading by E1

1. Compared every delivered existing module with the repository version. The target
   theorem signature is byte-for-byte unchanged; the only existing-module changes
   are proof imports and the proof body. The three added helper modules and three
   added DAG nodes are explicitly declared in this report.
2. Compiled all four delivered Lean modules with `lcompile.py`; each succeeds with
   no errors, and no delivered file contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. Direct axiom checks report only `propext`,
   `Classical.choice`, and `Quot.sound` for the public declarations.
3. Checked each split-off statement against the existing library and Mathlib by
   searching the declaration names and their semantic formulations. The three
   statements are true, strictly simpler than the item, and required by its proof;
   none duplicates an existing declaration. Their DAG nodes contain matching Lean
   signatures, proof steps, dependencies, source, and blueprint metadata.
4. Read the proofs from the target downward. The target uses the ordinary internal
   Hom evaluation, the unbounded derived coyoneda comparison, and the finite-free
   tensor exactness result. All imports used by the proofs remain, while the old
   direct `LocallyFreeDerivedHom` proof dependency was removed from the item. The
   finite locally free unit route is preserved.
5. Checked that each node's `proof`, `proof_deps`, and `proof_origin` match the Lean
   proof and that the unit and chapter fields are unchanged. No statement or
   definition was changed, no forced adaptation is present, and no old proof
   dependency remains unused except the one documented under `No longer needed`.

Changed after this reading: added this required second-reading record to the report;
no Lean declarations or DAG statements required repair.

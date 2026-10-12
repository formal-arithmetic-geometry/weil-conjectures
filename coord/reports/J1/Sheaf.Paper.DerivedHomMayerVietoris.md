## What changed

In `lean/Sheaf/Paper/DerivedHomMayerVietoris.lean`, proved the four remaining
finite-limit and finite-colimit preservation theorems without changing their
signatures, definitions, instances, or imports. Added the proved private helper
`modulePushforward_limits`: the forgetful functor to presheaves of abelian groups
reflects finite limits, and the composite of module pushforward with that functor
is precomposition on the underlying presheaves. Precomposition and the source
forgetful functor preserve finite limits. This proves preservation for any
continuous module pushforward in the universes used here, then specializes to
`overFunctor` and `overMap`.

For finite colimits, unfold `overFunctor` to expose Mathlib's left-adjoint
pushforward instance. The `overMap` left-adjoint instance is already available
directly. Mathlib's preservation instances finish both proofs. These arguments
also apply to empty opens and identity inclusions; no nonemptiness, cover,
separation, or finiteness hypothesis is used.

## Proved and sorry left

Proved four of the five original sorries:

- `AlgebraicGeometry.moduleOverFunctor_limits_proof`.
- `AlgebraicGeometry.moduleOverFunctor_colimits_proof`.
- `AlgebraicGeometry.moduleOverMap_limits_proof`.
- `AlgebraicGeometry.moduleOverMap_colimits_proof`.

The private helper `AlgebraicGeometry.modulePushforward_limits` is completely
proved. The previously proved additive lemmas are unchanged.

The sole remaining sorry is `AlgebraicGeometry.derived_hom_mayer_vietoris`,
node `lem-sc-derived-hom-mayer-vietoris`. Its original signature and its complete
source proof docstring remain unchanged. No new sorries were introduced.

## No longer needed

None. No imports were added or removed. The main Hom sequence is still open,
so its planned triangle, contravariant Hom exactness, and derived adjunction
nodes remain needed. The preservation lemmas are now independent of the
project's unproved stalk-exactness and open-restriction-adjunction results;
Mathlib suffices, but those nodes remain needed elsewhere in the main route.

## Where the brief, the DAG or earlier work was wrong

The planned triangle and derived adjunction cannot currently be imported into
this item: `import_direction.py may` rejects the triangle import because
`Sheaf.Algebra.Homology.DerivedMayerVietorisTriangle` reaches this module through
`DerivedOpenShriekAdjunction` and `OpenRestrictionAdjunctionExact`. The latter
publicly imports this item for `moduleRings` and the restriction instances.
Its proof dependencies, including `ModuleStalkExact`, also import this item.
Thus proving the Hom sequence by the existing plan requires separating the
foundational definitions and restriction instances from the Hom theorem,
then adapting the affected imports together. This delivery makes no such
interface change and proves the four foundational preservation obligations
in place. The DAG proof for the main Hom theorem is unchanged.

## Second reading by J1

1. Compared the entire delivered module with the repository using `diff -u`.
   All existing declaration signatures, definitions, instances, docstrings and
   imports are byte for byte unchanged. Only four theorem proof bodies changed,
   and one fully proved private helper was added. No change record is required.
   Verdict: pass.
2. Compiled the module locally with `lcompile.py`: no errors or warnings.
   Scanned for forbidden declarations and attributes: none. The only `sorry`
   is the original named theorem `derived_hom_mayer_vietoris`, listed above
   with its node and complete source proof docstring; no definition has a sorry.
   In a scratch copy, `#print axioms` for all four newly proved theorems and
   `derivedOpenHomRestriction` reports only `propext`, `Classical.choice`,
   and `Quot.sound`. The main theorem additionally reports `sorryAx`, exactly
   as expected for its unchanged open proof. Verdict: pass.
3. No statements were split off, and no new sorry or public statement was
   introduced. Checked the private helper against Mathlib's definitions of
   module pushforward, limit-preserving forgetful functors, and reflection:
   its underlying composite is definitionally precomposition, so the reduction
   is valid for arbitrary continuous functors in the stated universes. Empty
   opens and identity inclusions need no extra hypothesis. Searched Mathlib,
   upstream, and `lean/Sheaf` for pushforward preservation and equivalent
   formulations; no existing general module-pushforward limit instance replaces
   this helper. The colimit proofs already take the direct Mathlib route via
   `overFunctor`'s left adjoint and `overMapPushforwardAdj`. Verdict: pass.
4. Reviewed from the main theorem down. Its planned triangle and derived
   adjunction import this module transitively through
   `OpenRestrictionAdjunctionExact`; the report's cyclic-import obstruction is
   real. No new reduction simply restates the item. The four preservation
   obligations use Mathlib only. Existing imports provide the public statements,
   module structures, abelian instances (including `Grp.FilteredColimits`),
   and the derived restriction definition; no proof-only public import was added.
   All three old `proof_deps` remain part of the still-open main proof, so
   `## No longer needed` is complete. Inspected the unit's `realized` record:
   this delivery changes neither its entries nor its route. Verdict: pass.
5. Read `lem-sc-derived-hom-mayer-vietoris.json`, including its `lean` record,
   `proof`, `proof_deps`, and `proof_origin`. They describe the main theorem,
   whose statement and planned source proof remain unchanged. Its foundational
   preservation declarations are listed in the same node's `lean.declarations`;
   proving their obligations does not replace the main proof's dependencies.
   No new node is needed for an internal, completely proved proof helper.
   Verdict: pass.

Second reading changed only this report: added the independent review and
local compilation/axiom-check evidence. No Lean repair was necessary.

## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affinePushoutSection_products` with its
signature and existing docstring unchanged. The proof identifies the pullback
of the quasi-coherent regular pushforward module with the regular B-module,
uses the affine section comparison to obtain a tensor preimage, and applies
tensor induction. Zero uses the empty list, a pure tensor uses a singleton,
and addition uses concatenation.

Added the proved general comparison
`SheafOfModules.inverseImageRegularExtension` in
`Sheaf.Topology.InverseImageRegularExtension`. Its natural Hom equivalence
constructs the regular-module isomorphism, and the two adjunction formulas
prove its normalization on the canonical unit. The helper has no affineness,
scheme, pushout, surjectivity or finite-list hypotheses/conclusions: it is a
strict part of step 2 of the original argument, not a restatement of the item.
Its construction uses adjunctions determining their left adjoints up to unique
isomorphism, rather than an arbitrary witness of mere existence.

Proof-only imports added to the item: the new helper,
`Sheaf.AlgebraicGeometry.AffineModuleTensorBaseChange`,
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`,
`Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
The existing public imports remain to preserve its public interface.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.affinePushoutSection_products`
(node `stage3-affine-pushout-ring-section-products`).

Added and proved `SheafOfModules.inverseImageRegularExtension`
(node `stage3-inverse-image-regular-extension`). No holes were added or split
off. Neither delivered module contains `sorry`. Imported statements retain
their own proof obligations; no claim of closing their transitive axioms is made.

## No longer needed

No existing import was removed: both original public imports form the public
interface, and each added import provides a construction, theorem or instance
used by the proof. All original mathematical steps are retained.

The proof does not use `stage3-affine-pushout-ring-section-map` or its module
`Sheaf.AlgebraicGeometry.AffinePushoutRingSectionMap`: it proves finite product
generation directly from the linear section comparison and needs only the
definition `stage3-affine-pushout-ring-section-delta`. The item's proof dependency
on the section-map node was replaced by the delta node. This is local pruning;
other consumers may still need the section-map module. The section commutativity
theorem is not used by the proof, but its original public import remains.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt could not compile because the shared cache lacked the
existing section-leg imports. Those imports are now available. Its main draft
also needed the regular-module quasi-coherence import with explicit universes,
the same `appLE` algebra structure as the affine comparison, an explicitly
qualified categorical `Functor.map_id`, and a carrier annotation when converting
restricted scalar multiplication to ring multiplication. These were repaired
without changing any statement, definition, or module held by another group.

Step 2 of the original DAG gave the normalized regular-module identification
only in words. The new proved helper realizes that step by the two existing
module adjunctions and the regular-module Hom/sections equivalence. Zero rings
and empty opens require no exceptional assumptions in either delivered proof.
The original unit route is retained. The module adjunctions are generic tools
from another unit, not replacements for a step of the projective-line route.

Searches of Mathlib and both library roots found no public normalized comparison
for the explicit inverse-image/scalar-extension constructions. LeanFinder for
affine pushout section generation returned affine localization and limit results,
not this theorem. Loogle found `SheafOfModules.unitHomEquiv` and its composition
formulas, used by the helper. The earlier LeanSearch request was unavailable.

## New nodes

`stage3-inverse-image-regular-extension`, in the item's chapter and unit, records
the normalized regular-module isomorphism, its proof from the two existing
module adjunctions, and its source (Stacks Project Tags 008A, 008X and 008Y).
Its module is `lean/Sheaf/Topology/InverseImageRegularExtension.lean`.
The item node records its use in step 2 and the actual proof dependencies.
No statement or definition changes, change records, or forced adaptations.

## Second reading by D2

1. Compared the delivered affine products module with the repository version. The theorem signature and existing docstring are byte for byte unchanged; the helper is a new module and node as declared. Verdict: pass.

2. Compiled both delivered modules individually and together in import order with `lcompile.py`; no errors, warnings, sorries, forbidden declarations, or hollow definitions were found. Explicit scratch-copy `#print axioms` probes of both `SheafOfModules.inverseImageRegularExtension` and `AlgebraicGeometry.Scheme.Modules.affinePushoutSection_products` showed exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.

3. Checked the helper statement and proof against its node, searched the library and Mathlib for duplicates, and checked zero and empty-open cases described in the proof. The helper is a strict normalized comparison needed by step 2 and is not a restatement of the target. Verdict: pass.

4. The proof follows the affine module base-change, normalized regular-module comparison, affine section surjection, and tensor-induction route. Imports added are proof-only; the original public interface imports remain. The section-map dependency is pruned from the item node in favor of the delta declaration, as recorded above. Verdict: pass.

5. Compared node proof steps, dependencies, origin, Lean declarations, and the unit record. The item and helper nodes agree with the delivered code, and no unit statement or realized route is changed. Verdict: pass.

Changed the helper proof only: introduced a local equivalence identity `heqv` and used it in the naturality calculation instead of repeatedly unfolding and rewriting the composed equivalences. This reduced the helper compile from the 60-second delivery timeout to 17.1 seconds, with its statement unchanged. Also appended this second-reading report. The initial dry runs failed on that timeout; the repaired delivery is checked below.

The repaired dry run printed OK (commit `665fddb3cc`); both modules compiled and passed preflight. The final delivery includes the explicit axiom-probe results above.

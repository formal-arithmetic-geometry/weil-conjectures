## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.FieldShriekSystem.field_shriek_system_comparison`
with an assembly of the existing comparison laws. The statement, all existing
structures, and the definition of the comparison and its natural isomorphism
are unchanged.

The new private `comparison_invertible` proves step 4: a normalized input has
bounded constructible finite-Tor levels in its recorded strict-tower coordinates.
The realization counit and `SpTowerCalculus.levelComparison` identify these levels
with system evaluation. The proved `reductionDirectImage_isIso` applies to the
actual quotient homomorphisms; a private `ell_torsion` supplies their annihilation
by a power of ell. The evaluation equation and cancellation of its isomorphisms
prove invertibility after evaluation. The recorded semilinear calculus detects
isomorphisms, proving invertibility of the original system map.

The remaining glue is split into three new modules: simultaneous realization
and finite evaluation; the whole-system coefficient composition and identity
laws; and mixed quotient compatibility extending the given evaluation law.
Each is a strictly smaller group of the original argument's steps, with a
source, complete proof in words, and node. The parent node now follows this Lean
assembly. All new imports in the item are private proof imports.

## Proved and sorry left

Original holes: 1. The hole closed is
`AlgebraicGeometry.ProEtale.FieldShriekSystem.field_shriek_system_comparison`
(node `lem-sp-field-shriek-system-comparison`). The item now has zero direct
`sorry` proofs. Its invertibility argument is complete in Lean, conditional
on the finite evaluation law. This delivery is a decomposition, not a complete
axiom-free proof of the whole comparison assertion.

Holes added: 3, each the entire proof of a public theorem in a separate module:

- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_shriek_system_realization`
  (`lem-sp-field-shriek-system-realization`), original steps 1--3.
- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_shriek_system_cocycle`
  (`lem-sp-field-shriek-system-cocycle`), original steps 5--7.
- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_shriek_system_mixed`
  (`lem-sp-field-shriek-system-mixed-compatibility`), original step 8.

No other holes are left or introduced in the delivered modules. The direct
hole balance of this decomposition is 1 closed minus 3 added, namely -2.
No data definition uses a new existence theorem or contains a hole.

## No longer needed

Removed the item's private imports of `Sheaf.SixFunctors.OpenTensorNormalization`,
`Sheaf.CategoryTheory.RingedSliceTensorGenerators`,
`Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`, and
`Mathlib.CategoryTheory.Adjunction.Mates`. The assembly and finite-invertibility
proof do not directly use them. Their corresponding generic nodes remain needed
by the realization and cocycle subarguments; this is not a claim that those
modules have left the targets' closure.

The original node no longer directly cites `det-sp-tower-shriek-levels`,
`lem-pur-system-scalar-coherence`, `lem-sf-open-tensor-normalization`,
`lem-sf-ringed-open-total-tensor-kflat`, `lem-sf-ringed-slice-tensor-generators`,
or `lem-weil-pbc-mate-pasting` as proof dependencies. Those edges are replaced
by the three new intermediate statements, which retain the dependencies where
needed. Removed the original node's obsolete direct tool approvals for the
open tensor, slice generators, total tensor, tower levels and scalar coherence
nodes; kept its semilinear calculus approval.

No module or node is withdrawn. The unit route is preserved in full.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The generic declared
operations provide the ingredients, but do not directly provide the specialized
simultaneous `Models`/`EvaluationLaw`, the scalar-normalized cocycle of this
proper/open word, or the displayed mixed transition words. Those instantiation
and normalization arguments are now explicit outstanding items rather than
being hidden inside the original proof.

Edge cases checked for the new statements: equal coefficient fields, equal
quotient indices, exponent index zero (positive level one), zero objects and
empty schemes, identity morphisms, and ramified field extensions. Realization
and coefficient cocycles require no geometric finite-type hypotheses; mixed
compatibility retains the separated finite-type hypotheses needed for the
finite coefficient cocycle. No flatness of quotient maps is assumed.

## New nodes

`lem-sp-field-shriek-system-realization`, in
`lean/Sheaf/Paper/FieldShriekSystemRealization.lean`, states only the existence
of simultaneous normalized models and their specified finite evaluation law.
It asserts none of invertibility, mixed compatibility, or coefficient cocycles.

`lem-sp-field-shriek-system-cocycle`, in
`lean/Sheaf/Paper/FieldShriekSystemCocycle.lean`, states composition and identity
for a given normalized model, before evaluation. It asserts neither evaluation
nor invertibility nor mixed compatibility.

`lem-sp-field-shriek-system-mixed-compatibility`, in
`lean/Sheaf/Paper/FieldShriekSystemMixedCompatibility.lean`, extends a supplied
evaluation law to the actual mixed quotient square with exactly those same
coordinates. It asserts neither invertibility nor the whole-system cocycle.

All three inherit chapter `sec-smooth-purity` and unit
`sk-lem-sp-field-extension`. No existing public interface changed, so no
interface change record or consumer adaptation is required.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

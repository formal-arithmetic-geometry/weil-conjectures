## What changed

Replaced the hole in `AlgebraicGeometry.exists_schemeGlobalSectionsDirectImageIso`
with a complete Lean proof of the canonical Leray construction and its stated
right-derived-unit equation. Every existing public signature and definition body
is unchanged. Added the private, proved generic helper `lerayCore` in
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso`; its proof uses the K-injective
localizer criterion, exact scalar restriction, right-derived uniqueness and
`Functor.rightDerived_fac_app`.

The underived comparison is `Iso.refl`, with the identity-on-sections condition
proved by `rfl`. The composite derived functor and the derived global-sections
functor followed by exact scalar restriction are shown to be right derived from
the same underived functor, with their respective explicit units. Their unique
comparison is invertible; precomposing its factorization equation by the
underived composition isomorphism proves precisely the equation in the original
statement.

Added `Sheaf.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic` for
one strictly smaller missing step: acyclicity for global sections of the direct
image of a K-injective complex. This asserts invertibility of a particular unit
on particular complexes, not the existence of a Leray comparison or a global Hom
adjunction. Added its proof-only import. The generic proof assembles both units directly;
it requires no import of the composition module.

Both delivered modules compiled without warnings through `lcompile.py --all`,
including writing their compiled objects: the item in 52.7 seconds and the new
module in 4.6 seconds. Both are checked again by the dry run.
The new statement covers arbitrary unbounded complexes and arbitrary morphisms.
For the identity morphism it reduces to the standard K-injective computation of
global sections; for the zero complex it is an isomorphism of zero objects.
There is no assertion that direct image preserves K-injectivity.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_schemeGlobalSectionsDirectImageIso`, node
`lem-pc-global-hom-adjunction`, one of the two original holes.

Added: `AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective`,
node `lem-pc-direct-image-global-sections-kinjective-acyclic`.
This is a decomposition: one upper hole closed and one lower hole added, net zero
holes, with the derived construction and its unit compatibility proved in Lean.

Left unchanged in the item: `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`,
node `lem-pc-global-hom-adjunction`. There are no other holes in the delivered
modules, and no holes in any definition or private helper.

## No longer needed

Removed the proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`, and removed
`lem-pc-ringed-spaces-derived-direct-image-composition` from the item's direct
proof dependencies. The proof now uses global-sections acyclicity and the generic
right-derived universal property directly. The new acyclicity node still needs
the existing, finer successive-direct-image acyclicity statement, rather than
the full composition-isomorphism statement. Whether the removed module leaves
the whole target closure depends on its other users.

The earlier tensor candidate's added imports
`Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.Algebra.Homology.KFlatTensorProduct`, and
`Sheaf.Algebra.Homology.KFlatPullback`, and its additional direct DAG dependencies
`def-pc-scheme-derived-tensor-structure`, `lem-pc-kflat-resolution`,
`lem-pc-kflat-pullback-preservation`, and `lem-pc-kflat-tensor-product` are not
part of this delivery. The base tensor hole is unchanged, so these are not
claimed as pruning of its eventual proof. No blueprint unit or unit step was
bypassed; the item's unit has no realized node binding requiring the removed
composition node.

## Where the brief, the DAG or earlier work was wrong

The saved tensor proof had `DerivedCategory.Q` where its separately checked
scratch version used `DerivedCategory.Qh` on homotopy-category objects. Correcting
that mismatch did not make the complete tensor candidate compile within the
60-second limit. Profiling located roughly 29 seconds of kernel checking in its
concrete localization tensor-map helper. Attempts to abstract the calculation
also failed to make the complete candidate pass the required limit. That proof
is retained only in scratch files, not split into delivery modules to circumvent
the limit. This delivery instead completes the separate Leray construction hole
from the original node's plan; the tensor hole is untouched.

The missing published dependency from the earliest retries no longer blocks the
baseline compile. The base module and the delivered Leray construction compile.
The generic helper does not need K-injective resolutions in the scalar module
category: its K-injective tests all lie in the source sheaf category.

The cited source files are not present in this machine's read-only literature
checkout. The Stacks statements and proofs were read from their authoritative
pages: https://stacks.math.columbia.edu/tag/0D5T and
https://stacks.math.columbia.edu/tag/0B6I. They identify derived composition by
adjunction and use the resulting global Leray identity in the global Hom proof.
The new node makes explicit the acyclicity and unit transport needed to implement
that identity with the project's chosen right-derived functors.

## New nodes

`lem-pc-direct-image-global-sections-kinjective-acyclic`, in
`dag/nodes/sec-picard-framework/`, isolates the global-sections acyclicity step
of the Leray argument. Its docstring and node give the proof: apply the existing
successive ringed-space direct-image acyclicity theorem to the morphism to the
global-sections point, then transport its unit through the exact equivalence
between modules on that point and modules over its ring. This is strictly weaker
than constructing the natural derived Leray isomorphism with its equation.
Three kinds of Mathlib search are recorded; LeanSearch was unavailable, and the
other searches supplied no matching theorem. No change records are needed:
existing public interfaces are unchanged, and the added helper is private.

## Second reading by H1

1. I compared the delivered item module with the repository version. Existing
   declarations and signatures are unchanged; the only item changes are the
   proof import, the private helper, and the proof of the named Leray theorem.
   Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. There are no
   unnamed `sorry`s, forbidden declarations, or warnings. The remaining
   `sorry` is the explicitly split theorem and has a matching node and
   docstring. Verdict: pass.
3. I checked the split statement against the direct-image/global-sections unit:
   it is a true, strictly smaller acyclicity assertion and does not restate the
   parent target. Its edge cases include arbitrary morphisms and zero complexes.
   Verdict: pass.
4. I checked the proof route and pruning. The proof uses the acyclicity node and
   the generic right-derived universal property; the old composition import and
   dependency are no longer used. The unit route is preserved. Verdict: pass.
5. I checked the DAG records against the Lean declarations, including proof
   dependencies, origin, module, and statement text. Verdict: pass.

Changed after this reading: only this report section was added; no Lean code,
node, or public interface was altered.

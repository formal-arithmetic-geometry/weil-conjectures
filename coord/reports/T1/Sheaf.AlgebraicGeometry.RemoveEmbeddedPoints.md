## What changed

Proved the existing statement
`AlgebraicGeometry.Scheme.Modules.exists_maximal_nowhereDense_support_cokernel`
in `Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints`, without changing its signature or
public imports. The proof uses affine embedded-prime removal, constructs the global
maximality argument from affine section ranges, identifies cokernel sections with
module quotients, and transfers their support and associated-prime statements.
It constructs the dense open as the complement of the kernel's closed support.
For dimension drop it realizes the original closed support as a closed subscheme
and applies the already proved `Scheme.topologicalKrullDim_lt_of_isNowhereDense`.

Added `Sheaf.AlgebraicGeometry.CanonicalEmbeddedPointsGluing` for the specific
canonical affine-gluing step needed by this proof. Its conclusion gives only a
coherent subobject with prescribed affine section ranges. Nowhere density, global
maximality, quotient properties, the dense-open isomorphism and dimension drop are
proved by the consumer, rather than included in this new obligation. The new
statement is the affine gluing portion of Stacks Tag 02OL, using Tag 02M7.
The original gluing module, held by V7 when checked, is untouched. No source-library
module, definition, target statement, attribute or public import is changed.

The private proved helpers construct an affine support homeomorphism, transfer
nowhere density in both directions, identify support with the range of a section
inclusion, compare subobjects from their affine ranges, compare stalk supports, and
transfer the existing scheme dimension bound to a closed support subspace.
Both delivered modules compile via `lcompile.py`; the final combined compile is
recorded by delivery preflight as well. Only private proof imports changed in the
existing module; no change record is required for an existing public interface.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.exists_maximal_nowhereDense_support_cokernel`
(node `lem-sc-hilbert-embedded-points`). There is no `sorry` in the assigned module.

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.exists_coherent_subobject_of_affine_maxima`
(node `lem-sc-canonical-embedded-points-gluing`). Its module and node contain a
complete natural-language argument. This is an actual affine gluing result with
chosen local submodules as inputs, strictly a part of the original argument; it
asserts none of the original quotient, global maximality, density or dimension
conclusions. The complete Lean proof of all those conclusions is in the assigned
module. This delivery is a decomposition: one upper hole closed, one gluing hole
added, net zero before pruning. It is not a claim of an axiom-free proof of the
original theorem or of the gluing result. No other holes are added and no hole is
hidden in any definition or private declaration.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.HilbertEmbeddedPointsGluing` and
`Sheaf.RingTheory.LocalizationEmbeddedPoints` from the assigned module.
The former is replaced by the canonical affine-gluing step; its old general
statement cannot be applied because it supplies no restriction law and no global
maximality. The latter is still needed by the new gluing step and remains imported
there, so this is not a global pruning claim for localization.

The assigned node no longer directly cites
`lem-sc-hilbert-embedded-points-gluing` or
`lem-sc-hilbert-embedded-points-affine-localization`. Localization remains a
dependency through the new node. No Lean module or declaration is withdrawn or
deleted, including the gluing module held by V7. No globally pruned module is
claimed. The blueprint unit route through embedded-point removal is preserved.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old Lean declaration
`AlgebraicGeometry.Scheme.Modules.existsUnique_coherent_submodule_of_affine_cover`
in `Sheaf.AlgebraicGeometry.HilbertEmbeddedPointsGluing` allows arbitrary
`Nloc i V` with no compatibility with restriction maps. For a one-member cover
by the affine scheme `Spec(k × k)`, take F to be the structure sheaf and N on the
whole affine to be zero. Prescribe Nloc to be the full section module on one
nonempty clopen component. The stated overlap hypothesis is tautological with
one index, and N is finite, but no coherent subobject can have these section
images: its global affine image zero forces it to be the zero subobject, whereas
the prescribed component image is nonzero. The conclusion also quantifies over
opens outside the corresponding cover member. Thus the old Lean statement does
not express the localized submodules in the mathematical node.

The existing module was held by V7, so its statement could not be repaired here.
The added node makes the canonical local construction precise without adapting
that held module. Its edge cases include the zero sheaf, empty scheme and empty
affine opens; all have zero submodules. For a module already without embedded
points, the chosen maximal nowhere-dense submodule is zero. No separatedness,
quasi-compactness or global Noetherianity is assumed: overlaps are covered by
opens principal in both affines, and coherence is local.

The original dimension plan needlessly reproved a strict dimension bound using
components. An existing proved theorem handles it after passing to the closed
support subscheme. The dense-open construction also works directly with the
actual kernel support, without forming the closure of the embedded points.

Several generic source-library tools belong to `sk-thm-p1`, including coherence
criteria, affine cokernel sections, support closedness, stalk exactness and open
restriction preserving colimits. They are used as their stated module-theoretic
APIs, not as replacements for a blueprint unit's route. No maintainer tool-use
approval was added or altered.

## New nodes

`lem-sc-canonical-embedded-points-gluing` records the existence of a coherent
subobject with the prescribed canonical maximal affine section ranges. The local
inputs determine the gluing problem; the conclusion does not include any quotient
consequence. Its proof plan uses affine tilde/global sections, compatibility of the
canonical quotient under localization, a basis principal in two affine opens,
module gluing, and the locally Noetherian coherence criterion. The source is
Stacks Divisors Tag 02OL together with Algebra Tag 02M7. Searches were run with
LeanSearch, LeanFinder, Loogle and grep and recorded in `searches.jsonl`; they found
only ideal-sheaf and local-finiteness APIs, not this statement. The new module is
`lean/Sheaf/AlgebraicGeometry/CanonicalEmbeddedPointsGluing.lean`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

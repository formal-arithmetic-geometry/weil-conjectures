## What changed

Proved `AlgebraicGeometry.singleComplexOpenComparison_union_ses_core` without changing
its signature or any public import. The proof uses the existing concrete short exact
restriction sequence on an arbitrary union, applies the triangulated functors to its
SES triangle, and extracts cone models with `DerivedCategory.mem_distTriang_iff`.
It builds the two rows independently and takes both vertical maps to be zero.
The final commuting-square proof is the zero-composition law.

Added proof-only imports of OpenUnionImageComplexExact, OpenImageComplexComparisonIso,
RelativeMVMaps, the source KInjectiveResolutionInjective and RightDerivedFunctor.Triangulated,
and Mathlib Triangulated.Adjunction and Adjunction.FullyFaithful. Four proved private
helpers construct the exact-open adjunction, the invertible isomorphism-pullback unit,
the open-isomorphism transport, and the three-vertex cone model. No new public data
or definitions were introduced. Updated the item's node proof, dependencies, and origin.

Validation: the module compiles cleanly with lcompile.py (19 seconds).
The delivery dry run prints OK: compilation and preflight pass, except for the
second reading which the tool explicitly reserves for the second reader.
Nothing has been pushed.
The empty-open, repeated-open, disjoint-open and zero-complex cases use the same
existing SES theorem and general cone characterization; no case is excluded.
The inverse-image union and intersection are transported using preimage_sup/inf.
The localized representative is chosen using Q.objPreimage and the functorial resolution;
no object is extracted from an unproved existence theorem.

Source reading: the local Stacks .tex files are absent on this machine; read the
actual source at https://stacks.math.columbia.edu/tag/08BV (K-injective SES construction),
https://stacks.math.columbia.edu/tag/079W (derived adjunction), and
https://stacks.math.columbia.edu/tag/01JR (open fibre-product identification).
Mathlib Basic.lean lines 198–212 provides the exact cone characterization;
Triangulated/Adjunction.lean provides isTriangulated_leftAdjoint.

Searches run: msearch leanfinder for distinguished triangles as mapping cones found
DerivedCategory.mem_distTriang_iff; msearch loogle of that name found the signature;
msearch grep of the two geometric API names returned zero hits. Direct rg across both
Lean roots found the concrete arbitrary-union SES and object-comparison constructions.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.singleComplexOpenComparison_union_ses_core`
(node `new-single-complex-open-union-ses-core`). Zero holes remain in this module;
zero holes were added, and zero statements were split off. Existing imported
statements retain their own proof status; this delivery claims no proof of them.

## No longer needed

No original imports were removed: they supply the unchanged public interface and
SES construction. The plan's lifting of the coefficient morphism, a simultaneous
strictification of the two rows, and functorial compatibility of the cone maps are
not needed for this object's existential statement. No exclusive existing node or
module can be claimed as pruned: the old resolution proposition remains reachable
elsewhere, and the source resolution construction is still needed. The direct
proof dependency on prop-pur-kinjective-resolutions-exist is replaced by its
source-library degreewise resolution result, lem-pur-kinjective-degreewise-existence.

The candidate RelativeMVExactOpenComparison and RelativeMVInverseOpenIso imports
were removed during development: they create a cycle through
DerivedBaseChangeMayerVietorisMaps → AffineGlobalHomBaseChangeMap → the perfect-complex
and proper-flat base-change chain → SingleComplexOpenUnionTriangles → this module.
Their naturality theorems are not used. Only their short object-level adjunction
constructions are reproduced as proved private helpers, avoiding those imports.

## Where the brief, the DAG or earlier work was wrong

The original plan and docstring describe a strict coefficient-map lift, but the Lean
statement never identifies α, β or the induced cone map with that coefficient map.
It only asks for object isomorphisms and some commuting square. Consequently zero
vertical maps satisfy its full unchanged statement. This does not establish any
unrequested comparison-map compatibility, which belongs to the separate compatibility
item. The node now records the precise route actually proved. No statement is weakened.
The unit realized arrays are empty, so no prescribed unit step is bypassed.

## Second reading by Q4

1. **Repository comparison.** Compared the delivered module with the repository version. The
   theorem signature and all existing declarations are byte-for-byte unchanged; only proof
   code and proof-only imports changed. The node update records the revised proof route.

2. **Compilation and proof hygiene.** Compiled the module with `lcompile.py`; it succeeds
   without errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`, and no definition contains a placeholder proof. The
   closed theorem uses only the allowed imported foundations.

3. **Statements and split-offs.** No statements were split off and no new public declarations
   were added. The private helper lemmas are implementation details, and the unchanged target
   statement is exactly the requested existential statement. The zero choices for the two
   vertical maps satisfy the displayed commuting equation by the zero-composition laws.

4. **Pruning and route.** The proof uses the concrete arbitrary-union short exact sequence,
   its distinguished triangle, and the cone characterization, followed by object-level
   transport. The imports added are proof-only and all are used. No old proof dependency or
   reachable module can be pruned; the unit record has no realized steps, so no unit route is
   bypassed.

5. **DAG agreement.** The node proof, dependencies, origin, and Lean declaration agree with
   the compiled proof. The source and search records identify the Mathlib and library facts
   used. No target or definition was changed.

Changed only this report section; no further code or statements required repair.

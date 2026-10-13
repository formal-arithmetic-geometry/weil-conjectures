## What changed

Proved `AlgebraicGeometry.Scheme.injective_tilde_isFlasque` without changing its
statement or public imports. Added the proof-only import
`Sheaf.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension` and the proved
private helper `affine_section_ideal_presentation` in the same module.

The helper converts the existing ideal-sheaf section extension into an ideal
of R and a linear map to M using global sections and `ΓSpecIso`. The main
proof extends that map by module injectivity, proves the resulting section
agrees locally by cancelling an invertible scalar on a basic open, and then
extends sections across any inclusion of opens. Empty opens, exponent zero,
and zero rings are covered by the support argument and sheaf separation.

Updated the item's DAG proof, proof dependencies, and proof origin to match
these Lean steps. No new public signature, module, node, axiom, or definition
with postponed data was introduced. Only proof-local witnesses of existential
statements are used; there is no definition choosing arbitrary unproved data.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.injective_tilde_isFlasque`.
The private helper `affine_section_ideal_presentation` is also proved.
No `sorry` remains in this module and none was added: 0 split off.
The proof uses the existing theorem
`AlgebraicGeometry.Scheme.Modules.quasicoherent_open_section_ideal_extension`
(node `lem-pc-quasicoherent-open-section-ideal-extension`); its existing
transitive proof obligations are unchanged.

Single-file compilation through lcompile.py succeeded without warnings.
The required deliver3.py dry run checks the declaration and axiom probes.

## No longer needed

No imports were removed and no existing module was pruned.
The original proof-dependency edges to
`def-weil-pbc-noetherian-ring` and `def-weil-pbc-scheme-conventions` were replaced
by the actual section-extension dependency; both remain statement dependencies
and are not claimed as pruned nodes. No affine equivalence preserving
injectivity or injectivity in the category of all sheaves is needed.
`CoherentHomsOverOpen` and `CoherentHomIdealPowerExtension` are unnecessary for
this proof and were not imported; the structure-module section extension
already gives exactly the map required.

## Where the brief, the DAG or earlier work was wrong

The original node's first proof step cited only definitions for the substantive
ideal-power section extension. The existing declaration of Tag 01YB fills that
gap, and its node is now recorded as the proof dependency.
The upstream sheaf-flasqueness theorem needs injectivity among all sheaves of
modules, which cannot be inferred from module injectivity via the affine QCoh
equivalence. This proof instead applies module injectivity directly to J -> R.

`lem-pc-quasicoherent-open-section-ideal-extension` is used as a generic tool
from another unit, exactly for the section-extension step already prescribed
by Tag 09T2. It has no injectivity assumption and does not replace the unit's
route. The item's unit record has no realized step attached to this node;
its statement and route were not changed. Please record this generic tool use
at review if the unit checker requires it.

## Second reading by T2

1. Compared the delivered module with the repository version. The target theorem
   signature and all existing declarations are byte-for-byte unchanged; the only
   module change is a proof-only import and proof body.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses only ordinary constructions and existing
   declarations; no hollow definition or arbitrary data chosen from an unproved
   existence theorem was introduced.
3. The only helper is private and fully proved. No statement was split off and no
   new public theorem or node was added. The target proof uses the existing ideal
   section-extension theorem, injective factorization, support computation, and
   sheaf separation, each with the stated hypotheses and conclusion.
4. The route is shorter than the original affine-equivalence plan while retaining
   the unit's section-extension route: the existing quasicoherent ideal-extension
   declaration supplies the power and extension, then the proof works directly in
   module coordinates. No unused proof import was found, and the DAG proof and
   dependency list match the Lean proof.
5. Checked the DAG node against the implementation. Its proof steps, dependency,
   origin, and source agree with the code, and the target statement remains exactly
   the prescribed Stacks statement. The unit route is unchanged; this node still
   realizes the flasqueness conclusion using the generic section-extension step.

Changed only the report by adding this review record; no Lean or DAG repair was
needed after the checks above.

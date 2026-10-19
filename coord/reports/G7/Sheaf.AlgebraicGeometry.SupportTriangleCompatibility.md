## What changed

Proved `AlgebraicGeometry.ProEtale.supportOpenBaseChangeApp_naturality` in
`Sheaf.AlgebraicGeometry.SupportTriangleCompatibility`.

The retained direct proof caused expensive kernel conversion of the base-change
mate and inverse-image comparison. The repair packages their existing whiskered
composite as the explicit natural transformation `supportOpenBaseChange` and
makes `supportOpenBaseChangeApp` its component. Naturality is then the naturality
field of that transformation. Componentwise, whiskering and vertical composition
give exactly the previous formula, with the same maps and directions. No data is
chosen from an existence theorem. All existing signatures, visibility and imports
are preserved, including the unused instance binders of the naturality theorem;
the unused-section-variable linter is scoped off only for that theorem.

The definition node's Lean declaration list now includes the packaged natural
transformation. Its definition and unit route are unchanged; there are no new
proof-dependency nodes. The change record is
`coord/changes/G7-support-open-base-change-naturality.md`.

Validation: the final module compiled without warnings in 5.0 seconds. A second
compile produced its sandbox artifacts in 4.8 seconds and compiled the unchanged
sole direct importer `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle` against
them in 6.7 seconds. No consumer adaptation is needed. The required axiom probe and dry run passed (review class CODEX for the
definition change, change record and updated node attachment). A scratch attempt to check the
old expanded expression with `rfl` itself reached the 60-second limit, consistent
with the conversion issue; this is not reported as a successful equality test.

Searches retained from the earlier attempt: LeanFinder for naturality of composite
base change and whiskered inverse-image comparisons found general categorical
naturality results; Loogle for `CategoryTheory.NatTrans.naturality` found the exact
generic law; the grep service and local searches found the existing natural
transformations. The node has no numbered proof steps or proof dependencies.
The proof implements the two naturality squares in the existing docstring by
composing the natural transformations that already supply them.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.supportOpenBaseChangeApp_naturality`
(blueprint: `def-pur-triangle-meaning`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The additional definition `AlgebraicGeometry.ProEtale.supportOpenBaseChange`
is an explicit composite of already specified natural transformations.

## No longer needed

None. No imports added or removed, no dependency nodes bypassed, no modules
withdrawn. The unsuccessful private generic helper from the retained sandbox was
removed; it had never been part of the shared library. All five existing public
imports remain needed by the definition interfaces or their instances.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained a mathematically appropriate direct proof, but its
conversion check exceeded the single-file limit. Packaging the specified map as
a natural transformation fixes that definition-level performance problem without
changing any existing statement. Intermittent compile-server unavailability also
occurred during resumption, then cleared: the imports-only control compiled in
3.1 seconds and the unchanged source in 6.3 seconds. No launcher scripts, limits
or shared-repository files were edited.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

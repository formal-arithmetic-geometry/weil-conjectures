## What changed

Proved `CategoryTheory.ringFamilyGlobalExtension_oplax_normalized` without changing its
statement. Constructed the constant-functor monoidal structure using bottom-topology
sheafification and reindexing, composed it with normalized presheaf scalar extension and
monoidal module sheafification, and checked the fixed unit map by both adjunctions.

Added the proved theorem `PresheafOfModules.exists_pullback_monoidal_normalized` in
`Sheaf.Algebra.Category.ModuleCat.Presheaf.ScalarExtensionMonoidal`. Its construction uses
the source library's actual `changeOfRingsPresheaf`, the sectionwise scalar adjunction and
Mathlib's strong monoidal `ModuleCat.extendScalars`. The presheaf unit and tensor
naturality checks are on generators. Coherence is the ordinary module coherence on each
object. Uniqueness of left adjoints transports the resulting structure to the chosen
presheaf pullback while preserving its unit transpose.

Both constructions apply to empty categories and zero rings. The bottom topology imposes
no extra sheaf conditions; neither flatness nor any nonemptiness hypothesis is used.
All new instances in the assigned module are local, and all auxiliary data are explicit
constructions or the existing comparison between adjoints.

Updated the assigned node's proof route and added the node for the proved presheaf theorem.
Change record: `coord/changes/p2-presheaf-scalar-extension-monoidal.md`.

Validation: both modules compiled through `lcompile.py`; the complete assigned module
compiled in 32.9 seconds even with the temporary profiler and axiom-print commands.
`#print axioms` for both public theorems reported only `propext`, `Classical.choice`, and
`Quot.sound`. All diagnostic commands and profiler options were removed before delivery.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ringFamilyGlobalExtension_oplax_normalized`
(`lem-weil-pbc-global-section-module-monoidal-oplax`).

Also proved `PresheafOfModules.exists_pullback_monoidal_normalized`
(`lem-weil-pbc-presheaf-scalar-extension-monoidal`).

One original hole closed, zero holes added, zero holes left in either delivered module.
No obligation is split off with `sorry`.

## No longer needed

Removed the assigned module's proof imports
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits` and
`Mathlib.CategoryTheory.Adjunction.Limits`: the proof uses tensor structure and adjunction
identities, not colimit-preservation arguments. Replaced them with the proved presheaf
scalar-extension comparison and the strong monoidal reindexing API.

All three original mathematical dependencies remain needed. No existing module or DAG node
is withdrawn. No source-library declaration is removed or modified.

## Where the brief, the DAG or earlier work was wrong

The node's sectionwise tensor plan was correct. Its implementation can use the existing
source-library sectionwise change-of-rings construction and the Mathlib monoidal scalar
extension; it requires no further unproved tensor comparison. The earlier inherited
blueprint ancestry stops at a module name; the new node records its precise place in the
assigned node's proof rather than inventing a blueprint ancestor.

## New nodes

`lem-weil-pbc-presheaf-scalar-extension-monoidal`: normalized strong monoidal coefficient
extension for module presheaves on one small category. This is proved in the delivery and
is strictly the presheaf coefficient-change step, independent of the global-section ring,
one-point module category and final sheafification. The associated public API addition is
recorded in `coord/changes/p2-presheaf-scalar-extension-monoidal.md`.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

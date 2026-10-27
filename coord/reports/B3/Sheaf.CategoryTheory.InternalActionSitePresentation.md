## What changed

Proved the internal-action site presentation from the existing module-presheaf/sheaf
equivalence and equivariant module-sheafification reflector. Equality transports give
sectionwise linear equivalences and the normalized inverse formulas. The invertible
mate of the inclusion square gives the canonical site sheafification comparison and
its unit equation. Evaluation jointly reflects limits/colimits, so forgetting action
preserves them on presheaves. The reflection adjunction transports this preservation
to sheaves. Forgetting reflects isomorphisms, hence creates kernels and cokernels;
faithfulness and additivity detect zero objects.

Extracted the existing foundational declarations to InternalActionSiteBasic and
publicly re-exported them from the original module. This breaks the source import
cycle between the presentation and its two proof dependencies. Every existing public
signature and data definition is preserved. The ten foundational theorem holes are
proved directly. Retargeted the public import in TwistedSiteSieveGeometry and
EquivariantModuleSheafificationReflector. Preserved the complete equivalence and
reflector proofs that landed while this session was interrupted. The sandbox copy of
TwistedModulePresheafEquivalence is unchanged from the shared source.

The repaired five-module packet compiles individually in dependency order through
lcompile.py: Basic 7.0 s, reflector 16.2 s, sieve geometry 5.1 s, equivalence 13.2 s,
and Presentation 16.6 s. All five have zero textual sorry and no overlong Lean lines.

The returned packet duplicated the private `arrow_ext` and `labeled_pullback`
lemmas already proved in TwistedSiteSieveGeometry. Repaired this by relocating those
existing proofs into Basic as public shared lemmas and deleting their private copies
from geometry. Geometry imports Basic and uses these exact lemmas. The moved pullback
proof replaces its use of the private `comp_label` helper by the identical displayed
composition formula; the lift construction and universality proof are retained.
There is now one declaration and one proof of each result in the packet.

## Proved and sorry left

Closed 11 of the original 11 holes, with no holes added and no split-off holes:

- CategoryTheory.InternalActionSite.category_laws
- CategoryTheory.InternalActionSite.hasIsos
- CategoryTheory.InternalActionSite.covering_pullbacks
- CategoryTheory.InternalActionSite.labelOne_downward
- CategoryTheory.InternalActionSite.topology_mem_iff
- CategoryTheory.InternalActionSite.coefficient_isSheaf
- CategoryTheory.InternalActionSite.equivariant_add_laws
- CategoryTheory.InternalActionSite.equivariant_comp_laws
- CategoryTheory.InternalActionSite.equivariant_category_laws
- CategoryTheory.InternalActionSite.equivariant_distributivity
- CategoryTheory.InternalActionSite.presentation

The first ten now live in the extracted Basic module. Presentation and Basic have
zero textual sorry. During delivery preflight the completed sieve_geometry proof landed.
The first attempt correctly refused the stale sandbox dependency and pushed nothing;
that file was refreshed preserving its complete argument. The present repair then
consolidates its two helper proofs into Basic, as described above.
All five packet modules now have zero textual sorry, including
CategoryTheory.InternalActionSite.sieve_geometry,
module_presheaf_equivalence and equivariantModuleSheafification_reflector.
Those three dependencies were proved by their own workers and are not counted among
B3's 11 holes closed.

All thirteen direct consumers compiled individually against the delivered overlay.
The compilation service reported success for every one, including the two mathematical
consumers using the presentation data and the existing action/category consumers.

## No longer needed

No mathematical module is withdrawn. The ten foundational proofs need neither the
presentation theorem nor the general sieve_geometry theorem. Their pullback argument
now shares the original geometry helper rather than reproving it. The presentation
assembly still needs the latter indirectly through the sheaf equivalence, so its
module and node remain needed. The obsolete direct use of sieve_geometry in step 1
is replaced by the directly proved Basic construction in the node record.

The foundational public imports move intact to Basic and remain publicly re-exported
through Presentation. The two dependent modules no longer import Presentation;
they import Basic. Removed unused experimental proof imports
Mathlib.CategoryTheory.Adjunction.Unique and
Mathlib.CategoryTheory.Adjunction.CompositionIso; the proof uses the narrower
Mathlib.CategoryTheory.Adjunction.Mates. Removed the unused private
cast_inverse_apply helper. No unit statement or realized unit proof step is bypassed.

Removed the two duplicate private helper declarations from TwistedSiteSieveGeometry;
their original proofs now live in the common foundation and are reused by geometry.
No node or mathematical dependency is withdrawn by this repair.

## Where the brief, the DAG or earlier work was wrong

The declared proof plan had a Lean import cycle: its equivalence and reflector
modules themselves imported InternalActionSitePresentation, which held both the
foundation and the theorem being proved. This prevented importing them back to
assemble presentation. Extracting the existing foundation resolves the cycle
without changing a mathematical statement or constructing a second copy.
The new module is required by that cycle, not by a per-file timeout.

The source library acquired completed proofs of the equivalence and reflector
while the session was interrupted; stale sandbox dependency copies were refreshed
before delivery, preserving those proofs instead of reintroducing their holes.
The original brief and budget were retained on all provider-error resumptions.

The return correctly identified two duplicate helper proofs in the earlier packet.
The common foundation must expose the existing results to their original geometry
consumer; merely keeping separate private copies would violate one proof per fact.
The geometry node now records this shared foundation dependency.

## Forced adaptations

Sheaf.CategoryTheory.TwistedSiteSieveGeometry is unclaimed at this repair. Besides
retargeting its public import to Basic to break the cycle, remove its private
`arrow_ext` and `labeled_pullback` declarations: they are now shared public declarations
in Basic. All uses retain their existing names and signatures. This is the requested
consolidation of duplicate lemmas, rather than a forced edit of another held item.
The remaining geometry proof and public theorem signature are preserved.
EquivariantModuleSheafificationReflector is unclaimed and retains the one-line
import migration. TwistedModulePresheafEquivalence matches the current shared source.

## New nodes

 `def-sfb-internal-action-site-basic` attaches the extracted, fully constructed
foundation and its proved laws. This is an extraction node, with no new sorry or
new mathematical assumption; existing definition attachments now identify Basic.
The presentation node's proof and dependencies describe the actual categorical
assembly. Change record: coord/changes/B3-internal-action-site-foundation.md.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

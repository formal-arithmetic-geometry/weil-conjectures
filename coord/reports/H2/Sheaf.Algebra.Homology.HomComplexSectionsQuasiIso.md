## What changed

Replaced the proposed degreewise restatement by a real reduction of
`CategoryTheory.homComplex_sections_quasiIso`. For each degree, the proof obtains natural
comparison equivalences, sends the restricted quasi-isomorphisms to isomorphisms in the
derived category, proves that pre/postcomposition is bijective using the inverse maps,
and transfers bijectivity to the section homology map. Mathlib converts bijectivity in
`AddCommGrpCat` to `IsIso` and assembles the degreewise conclusions into `QuasiIso`.
The existing theorem signature is byte for byte unchanged.

Added two modules, each with one named unresolved intermediate theorem:
`HomComplexSectionsDerivedNaturality` and `LocalizedModuleRestrictionQuasiIso`.
The first treats arbitrary chain maps, with no quasi-isomorphism assumptions; the second
treats arbitrary module complexes, with no Hom complex or K-injectivity assumption.
All new imports in the item's module are proof-only `import`, not `public import`.
No definition was added or changed. Updated the existing item's DAG proof and dependencies.

## Proved and sorry left

Hole closed: `CategoryTheory.homComplex_sections_quasiIso` (one of one original holes),
by reduction to the following two new holes:

- `CategoryTheory.homComplex_sections_derived_naturality`, node
  `lem-pur-hom-complex-sections-derived-naturality`.
- `CategoryTheory.localizedModule_restriction_quasiIso`, node
  `lem-pur-localized-module-restriction-quasi-iso`.

This is a decomposition, not a completed proof: one hole closed and two added, so the
local hole delta is minus one. Existing dependencies still include unproved theorems.
The target's axiom closure contains `sorryAx`; the delivery does not claim axiom-free
completion. The rejected `CategoryTheory.homComplex_sections_quasiIso_at` and its new
node were removed from the delivery. Each remaining new hole has a complete proof in
words and a matching node. There is no `sorry` inside a definition.

## No longer needed

Removed the item's direct import of
`Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`; its node
`lem-pur-site-restriction-module-adjunction-exact` is no longer a direct proof dependency.
This module remains transitively reachable through the local K-injectivity comparison,
so no globally pruned module is claimed. The direct import of
`RhomIntoKInjectiveLocal` is redundant with the public imports required by the new
naturality statement and was removed; its node stays a proof dependency because the
proof uses `module_overFunctor_preservesZero`.

`def-weil-abstract-derived-category`, `def-pc-quasi-iso-modules`,
`def-pur-hom-complex`, and `lem-pur-rhom-into-kinjective-local` remain used. These account
for every old proof dependency. Removed the undelivered degreewise restatement module
`HomComplexSectionsQuasiIsoAt` and its node; earlier exploratory modules were already
absent when this reading started. No unit statement or realized step was pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's `QuasiIsoAt` statement retained both original quasi-isomorphism
hypotheses and the full sectionwise conclusion in an arbitrary degree. Constructing
`QuasiIso` from it simply unpacked the definition and left the whole mathematical
argument inside a new `sorry`. Its docstring omitted the shifted comparison and
naturality calculations, and the original target node had not been updated.
This reading rejects that reduction rather than counting it as proof progress.

The old exact-adjunction declaration only covers small categories with a precoverage
and additional stability assumptions. The item's statement is for arbitrary categories
and Grothendieck topologies, so it cannot supply restriction exactness here by direct
application. The new restriction lemma isolates exactly that missing arbitrary-site
argument without changing the target.

The sources were checked directly at Stacks tags
[0A8Y](https://stacks.math.columbia.edu/tag/0A8Y),
[0A94](https://stacks.math.columbia.edu/tag/0A94), and
[03DH](https://stacks.math.columbia.edu/tag/03DH).
Mathlib provides the homotopy/derived comparison and preservation of quasi-isomorphisms
by functors preserving homology, but not the sheaf-section comparison or this exactness
instance. The recorded new searches use different terms from the first worker's searches.
LeanSearch returned Internal Server Error; Loogle, LeanFinder, and source grep ran.

## New nodes

`lem-pur-hom-complex-sections-derived-naturality` states the shifted comparison and
its naturality for arbitrary maps. Its proof spells out cycles, boundaries, the shift
sign, local K-injectivity, localization, and equality on representatives. It is a
comparison theorem, not an invariance theorem or a restatement of the item.

`lem-pur-localized-module-restriction-quasi-iso` states preservation of
quasi-isomorphisms by restriction on an arbitrary ringed site. Its proof uses sectionwise
kernels and local cokernel representatives, then preservation of homology by exact
functors. It applies to noncommutative rings as well and contains no K-injectivity
or internal-Hom hypothesis. No change record is needed: no existing interface changed.

## Second reading by H2

1. **Existing interface:** PASS after repair. I compared the delivered item against the
   repository version, including a declaration-parser signature comparison. The entire
   original theorem signature and its docstring are unchanged. There are no other old
   declarations to alter and no forced adaptations or target-statement changes.
2. **Proof and trust:** PASS as a decomposition. All three files compile through
   `lcompile.py`. Only the two explicitly named new theorems retain `sorry`.
   No `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, hollow definition, or
   arbitrary data witness was introduced. The axiom probe allows only the standard
   axioms and `sorryAx` from the documented holes. Explicit scratch-copy
   `#print axioms` on all three declarations returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. It does not certify completion.
3. **Split statements:** the original split FAILS and was removed. The replacements
   are true and strictly separate parts of the argument. The comparison works for
   arbitrary maps; the restriction lemma has no Hom-complex assumption. I checked
   zero complexes, identity maps, degree zero, shift signs in arbitrary integer
   degrees, and trivial/maximal topologies. In particular the zero-complex derived
   Hom sets are singleton and restriction carries zero homology to zero homology.
   Loogle, LeanFinder, and grep identify generic Mathlib tools but no exact duplicate;
   repository/upstream searches find the unshifted local comparison and the narrower
   precoverage exact-adjunction statement, neither of which states these new results.
4. **Route and pruning:** PASS after replacing the definitional wrapper with the
   naturality/invertible-composition argument. No shorter matching Mathlib result
   was found. Proof-only imports are private. Every old proof dependency is accounted
   for above. The unit `sk-def-sf-operations` has empty realized statement/step arrays;
   these remain unchanged and the existing target node remains the unit's node.
5. **DAG agreement:** PASS after repair. The existing target node now names the two
   actual intermediate declarations, the zero-preservation helper, and the Hom-complex,
   derived-category, and quasi-isomorphism definitions it uses. The new nodes record
   exact Lean signatures, sources, complete proof steps, dependency unions, creation
   metadata, blueprint lineage, and actual search records.

I removed the degreewise restatement, wrote and compiled the real reduction, added
its two precise intermediate statements and nodes, repaired the original DAG proof,
removed redundant direct imports, and rewrote the report to identify the decomposition
and its negative hole delta accurately. My initial review text mistakenly described
an already-private import as public and accepted the degreewise wrapper; that provisional
text has been corrected here. No existing statement was changed.

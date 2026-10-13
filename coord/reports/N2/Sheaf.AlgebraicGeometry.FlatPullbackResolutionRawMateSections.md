## What changed

Repaired the returned duplicate-statement finding. The main module now has a proof-only
`import all Sheaf.AlgebraicGeometry.HigherDirectImageResolutionNaturality`, which makes
its existing private naturality theorem available. Deleted the duplicate private
`AlgebraicGeometry.Scheme.Modules.adjoint_homology_naturality` and
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyTheta_naturality` declarations.
`rawSectionClass_naturality` uses the existing
`AlgebraicGeometry.sectionCohomologyTheta_naturality` directly. The original public
resolution theorem's signature and docstring are unchanged, as is its combining proof.
The parent node now records the existing naturality dependency. Updated the proof-settings
change record; removed the deleted helpers' local sheafification/transparency controls.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolution_rawMate_sections` by reduction.
One hole is split off:
`AlgebraicGeometry.Scheme.Modules.flatUnit_raw_sections`, node
`lem-weil-pbc-flat-unit-raw-sections`, in `FlatUnitRawSections.lean`.
This is a decomposition: one original hole closed, one strictly smaller unit-case hole
added, zero net holes closed. The private raw-section naturality helper and the combining
proof contain no sorry. The unit statement removes the arbitrary target complex and map;
it is compatible with degree zero, the zero complex and the empty open, and assumes no
acyclicity or invertibility of theta. No new holes were added by this repair.

## No longer needed

No original import removed and no existing module globally pruned. Deleted both duplicate
private naturality helpers and their special elaboration controls. The existing library
naturality theorem supplies their needed specialization through a proof-only import.
The invalid earlier sandbox-only node
`lem-weil-pbc-flat-pullback-resolution-raw-mate-sections-cycle` and its trivial-premise
alias remain absent. Removed
`lem-weil-pbc-flat-module-pullback-exact-pushforward-injective` from the parent node's direct
proof dependencies; flat exactness remains a dependency of the unit-case node.
No resolution transport lemmas are imported. Construction, adjunction and theta definitions
remain needed by the combining proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the existing private adjoint homology naturality lemma.
An ordinary import does not expose it, but Lean's `import all` exposes both that theorem
and its theta specialization without changing the source module or its visibility.
The repair reuses the specialization and deletes both local duplicates; it does not rename
the same statements or change their binders to avoid the checker. No forced adaptation is
needed. The previous second-reader section was removed so the new reader can inspect this
repair independently. Rebase and verification are performed by deliver3.py --no-push;
no worker git commands or pushes are performed.

## New nodes

`lem-weil-pbc-flat-unit-raw-sections`, in
`lean/Sheaf/AlgebraicGeometry/FlatUnitRawSections.lean`, is the unchanged unit compatibility
reduction from the returned delivery. It states no resolution, target complex, comparison
lift or arbitrary map from the pulled-back complex. Its module and node document the
cycle proof, source and searches. The parent combines this with existing theta naturality,
evaluation homology-comparison naturality and adjunction composition. No additional nodes
were created for the repair. The proof-settings record is
`coord/changes/raw-mate-sections-proof-settings.md`.


## Second reading by N2

1. **Interfaces: pass.** Compared the complete main module with the read-only repository
   version and checked the existing theorem signature byte for byte. Its signature,
   visibility and docstring are unchanged. The new unit module has no repository version.
   The added imports in the main module are proof-only, including `import all` for the
   existing private theta naturality theorem. There are no changes to target definitions.
2. **Proof and trust: pass.** Compiled both delivered modules with lcompile.py. The main
   module contains no sorry, and the new module has exactly the reported named theorem
   `flatUnit_raw_sections` with `:= by sorry`. There are no forbidden declarations or
   hollow definitions. The rawSectionClass definition is an explicit composite.
   The chosen adjunction is existing library data; this delivery introduces no arbitrary
   witness construction. The axiom probes are recorded below.
3. **Split statement: pass as a decomposition.** Read the unit formula and its cycle proof.
   It asserts compatibility for the unit alone, before an arbitrary target map; the parent
   separately proves the composition step using naturality and the adjunction triangle.
   Thus it removes a genuine part of the argument, rather than aliasing the parent.
   At degree zero the cycle/kernel and quotient argument still applies; the zero complex
   and empty open give zero morphisms. Nothing requires exact sections or invertible theta:
   only evaluation on presheaves is exact. Flatness supplies exact tensor pullback.
   Independent leanfinder search for homology/adjunction-unit/forgetful-section compatibility
   returned derived-adjunction and localization ingredients; loogle found
   ShortComplex.homologyMap_mapNatTrans. Targeted rg searches in Sheaf, WeilConjectures and
   upstream found the private sheafification cycle identity and theta naturality, but no
   flat-unit section identity. Those ingredients do not close this remaining hole in a
   few minutes. Its new module, docstring and node match.
4. **Route and pruning: pass.** Checked the proof from the original target down: specialize
   the unit formula, use the existing theta naturality plus Mathlib evaluation comparison,
   then use homEquiv_naturality_right and the complex adjunction identity. Every direct
   import is needed. The old direct flat-exactness dependency is listed as no longer needed
   by the parent and retained by the unit node. No module is globally pruned. Read
   dag/units/sk-thm-p1.json: neither edited node realizes a protected unit step; its realized
   statement and steps are unchanged. The decomposition has zero net holes closed.
5. **DAG: pass.** The parent proof steps and proof_deps describe the unit reduction,
   existing naturality and adjunction composition actually used. The new node's proof_deps
   are the union of its steps' uses; its statement and verbatim Lean signature agree.
   Source, proof_origin, searches, status, created, blueprint, chapter and unit fields are
   present. The source tex is not installed in this read-only clone; the mathematical
   verdict above follows from the explicit cycle argument and the library definitions,
   not a claim that the cited Stacks tags state the displayed Lean formula verbatim.

Changes by this second reader: appended this independent review and validation evidence;
no Lean proof or statement repair was needed in the repaired packet.

Axiom validation: scratch-copy `#print axioms` probes compiled successfully for both
public theorems and rawSectionClass_naturality. The public theorems list exactly
`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, consistent with the remaining
unit/exactness dependencies. The proved private naturality helper lists only
`propext`, `Classical.choice`, `Quot.sound`. No extra axiom was introduced.

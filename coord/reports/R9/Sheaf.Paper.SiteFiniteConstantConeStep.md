## What changed

Implemented `CategoryTheory.exists_site_finite_constant_cone_step` in
`Sheaf.Paper.SiteFiniteConstantConeStep`, preserving its statement and all original
public imports. The original named forall hypotheses cause unused-binder
warnings once the proof is filled; disabled only that linter for this declaration
to retain its original statement verbatim. Added private proof imports for the source-library exact derived
functor API, its proved homology-property closure theorem, constant restriction,
local surjectivity, finite free generators, and the new weak Serre bridge.

The proof constructs a finite free epimorphism onto the locally constant top
cohomology. On an arbitrary cochain representative it lifts the finitely many
basis sections through cycles-to-homology on a common covering sieve, extracts a
precoverage cover, and uses the constant-sheaf adjunction to obtain an actual
chain map on each flat slice. It proves the induced top cohomology map epic,
localizes the chain map, completes it to a distinguished triangle, and proves the
smaller interval using the long exact sequence. The finite locally constant
property of the cone follows from the existing generic homology-property theorem
and the new sheaf-only weak Serre bridge. The unit's finite-generator and cone
route is retained.

Added `Sheaf.Paper.SiteFiniteLocallyConstantWeakSerre` and its node to isolate the
conversion of the already-stated ringed-module weak Serre theorem to the exact
module-valued flat-slice predicate. Updated only the assigned node's proof,
proof dependencies and proof origin. No existing interface was changed, and no
other existing Lean module was adapted. The new bridge compiled in 1.9 seconds;
the assigned module compiled in 44.5 seconds through `lcompile.py`.

## Proved and sorry left

Closed the original body hole of
`CategoryTheory.exists_site_finite_constant_cone_step`
(node `lem-weil-pbc-site-finite-constant-cone-step`). The assigned module now has
zero `sorry` tokens. All private helpers, including `single_map_of_cycles`,
`epi_homology_Q_map`, `local_free_lift`, `local_top_epi`, and the restriction and
single-object locally finite lemmas, have complete proofs.

Added one named theorem with exactly `:= by sorry`:
`CategoryTheory.site_finiteLocallyConstant_weakSerre`
(node `lem-weil-pbc-site-finite-locally-constant-weak-serre`), in its own new
module. Its docstring contains the source and complete transport argument. It is
an assertion in the abelian category of sheaves, with no derived object, cone,
generator morphism, existential derived construction, or cohomological bound.
It is strictly the weak Serre part of the argument, not a restatement of the
assigned existence theorem.

Counts: one original hole closed, one lower hole added; one decomposition, net
zero holes. The local generator construction and cohomological bound reduction
are proved in Lean. The mathematical proof still depends on the displayed
weak Serre bridge.

## No longer needed

No original public import was removed and no library module was withdrawn.
The assigned proof no longer needs the following original direct dependencies:

- `lem-weil-pbc-truncation-descends` / `Sheaf.CategoryTheory.TruncationDescends`:
  an arbitrary cochain representative suffices; the map is constructed into its
  cycles, so no upper truncation or truncation descent is used.
- `lem-weil-pbc-local-finite-free-epi-lift` /
  `Sheaf.Paper.LocalFiniteEpiLifts`: its image-sieve argument is proved directly
  in the private flat-slice helper, avoiding iterated-slice transport. This
  module itself is neither changed nor withdrawn.
- `lem-pur-site-restriction-module-adjunction-exact` /
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: the exactness required
  here follows directly from the Mathlib over-pullback functor and its sheaf
  adjunction, without passing to the ringed-module system encoding.

The ringed-module finite locally constant Serre theorem
(`lem-weil-pbc-locally-constant-derived-serre`,
`Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`) and the constant-ring
comparison (`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`,
`Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`) are removed from
the assigned node's direct proof dependencies but remain dependencies of the
new bridge. They are not globally pruned. Constant restriction and the long
exact cohomology sequence remain used.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The planned upper-truncation step is
unnecessary: finite generators of cohomology lift locally to cycles of any
representative. A genuine remaining interface issue is that the proved finite
locally constant weak Serre theorem is stated for sheaves of modules on a ringed
site, while this item uses module-valued sheaves on flat slices with explicit
precoverage covers. The new node states only that encoding/cover transport;
it does not postpone the cone construction again.

Edge cases considered: the zero ring, a zero finite module (rank zero free
presentation), empty covers admitted by the precoverage, and the adjacent
interval `b = a + 1`. Finite intersections of image sieves include the empty
intersection. No nonempty cover or nonzero ring is assumed. The long exact
sequence proof treats the top degree separately and uses arithmetic only to
check degrees outside the interval.

## New nodes

`lem-weil-pbc-site-finite-locally-constant-weak-serre`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-site-finite-locally-constant-weak-serre.json`,
is attached to `CategoryTheory.site_finiteLocallyConstant_weakSerre` in
`lean/Sheaf/Paper/SiteFiniteLocallyConstantWeakSerre.lean`. It records the
constant-ring and iterated-slice equivalence argument and the source Tag 093U (3),
including the covering-sieve/precoverage comparison. Its exact Lean statement,
proof dependencies and search results are recorded. No change record is needed:
existing statements, definitions and public imports are unchanged.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.FilteredComplexPositivePages` by a
compiling construction of Mathlib's spectral-sequence structure from concrete
cycle/boundary quotient pages and their successor homology isomorphisms. The existing
signature and public imports are unchanged. The page comparison is `Iso.refl`.

Added three modules, each with its own node:

- `FilteredComplexBoundariesLECycles`: proves
  `CategoryTheory.filteredComplex_boundaries_le_cycles` directly from Mathlib's
  image/pullback adjunction and `K.d_comp_d`, without a sorry. The proof first shows
  that the image under one differential lies in every pullback under the next,
  then applies intersection, sum, pullback and graded image monotonically.
- `FilteredComplexPageDifferential`: constructs the actual cokernel objects and
  their projections, defines differential data by an explicit equation on
  representatives, and constructs the page complex from that data. Leaves its
  unique-existence theorem for the single-page differential to another worker.
- `FilteredComplexPageHomology`: states the successor homology calculation for
  any differential satisfying that representative equation. This theorem needs
  no successor differential and constructs no spectral sequence.

The existence theorem specifies a unique differential on fixed, already constructed
cokernel objects. No definition chooses an arbitrary object from a mere existence
statement. The main proof selects these uniquely specified differential data and
isomorphisms between the fixed homology and quotient objects.

Read the source at [Stacks Tag 012K](https://stacks.math.columbia.edu/tag/012K),
including the displayed cycle, boundary and differential formulas and the general
abelian-category proof of `lemma-spectral-sequence-filtered-complex`. The local
literature checkout has only the reference lists. The construction uses finite
limits and cokernels componentwise, with no countable-sums assumption.

All four delivered modules compile through `lcompile.py --all`, without warnings.

## Proved and sorry left

Closed the original hole:

- `CategoryTheory.filteredComplex_positive_spectralSequence`
  (`lem-sp-filtered-complex-positive-pages`). Its proof contains no sorry.

Added two holes:

- `CategoryTheory.filteredComplex_page_differential_exists_unique`
  (`lem-sp-filtered-complex-page-differential`): existence and uniqueness of the
  representative differential on one fixed quotient page, including square zero.
- `CategoryTheory.filteredComplex_page_homology`
  (`lem-sp-filtered-complex-page-homology`): homology of that differential is the
  next fixed quotient.

These are a decomposition of the original construction, not a complete proof of
its mathematical content: one original hole closed, two added. Both remaining
proofs are exactly `by sorry`, with complete source-based proof descriptions in
their docstrings and nodes. There are no other sorries in the delivered files.

Also fully proved `CategoryTheory.filteredComplex_boundaries_le_cycles`
(`lem-sp-filtered-complex-boundaries-le-cycles`) and its private adjunction helper.
The inequality works for every integer r, including nonpositive r.

Checked the new statements on the zero complex, the zero and constant filtrations
(all quotient objects vanish), and a two-step filtration at r=1 (the representative
equation gives the usual connecting differential). For a general r, a change of
representative in F^(p+1) contributes a target r-boundary, since its target incoming
filtration degree is (p+r)-r+1=p+1. Related bidegrees always have total degrees n and
n+1, even for negative p or q. The homology argument uses epimorphic local lifts,
so it assumes neither projectivity nor a concrete category.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.ExactCouple`; the proof and the
three new modules use no `BigradedExactCouple`, derived maps, iterated couples, or
exact-couple coordinate conversion. Removed `def-sp-exact-couple` from the item's
proof dependencies. This prunes the exact-couple route from this item, without
claiming that other target branches cease to need the module.

The old direct proof dependencies `def-sp-abelian`,
`def-sp-filtered-complex-subquotients`, and `def-sp-filtration` are also absent
from the revised item's `proof_deps`: they are supplied through the new page
lemmas and remain needed transitively and in the existing signature. Their
modules are not claimed pruned.

Removed the redundant public import
`Mathlib.Algebra.Homology.SpectralSequence.Basic` from the new
`FilteredComplexPageDifferential` module during the second reading. This module
uses only the already imported complex shapes and homological-complex machinery;
the homology module now directly publicly imports
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` and
`Mathlib.Algebra.Homology.ShortComplex.Abelian` for its homology statement.
The positive-pages module still needs and publicly imports Basic.

Removed the direct proof-only import `Sheaf.CategoryTheory.Filtration`, which is
redundant with the existing public subquotient import. The filtration definition
and module remain needed transitively and as statement dependencies.

Removed an experimental direct import of the new page-differential module from
the item's module: the page-homology module already provides it. Both new remaining
statements are needed. No realized statement or proof step of the blueprint unit
is bypassed; `sk-prop-av-pqf-finite` has empty `realized.statement` and step entries
for this imported auxiliary material.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface change was found. The original proof-dependency
modules provide the subquotient definitions and exact-couple data, but contain no
filtered-complex-to-exact-couple construction or spectral-sequence conversion that
can simply be applied here. The direct representative formula in the cited source
allows the smaller componentwise route recorded in the updated node.

`blueprint_refs.py ancestor` does not resolve this created item's id because its
`created.item` is a module name. The existing node already records the correct
ancestor `thm-sp-spectral-object-yields`; the new nodes extend that recorded path
through `lem-sp-filtered-complex-positive-pages`. Blueprint searches for filtered
complexes, page differentials and page homology found no duplicate of the new
individual statements. Existing finite-filtration spectral-sequence results both
have stronger hypotheses and depend on this item, so were not imported.

## New nodes

`lem-sp-filtered-complex-boundaries-le-cycles` records the fully proved containment,
including all integer pages. Its source is the displayed inclusion in Tag 012K.

`lem-sp-filtered-complex-page-differential` records the unique differential on one
concrete quotient page, with its equation on arbitrary generalized representatives.
Its proof explains both quotient descents, square zero, and uniqueness via an epic
representative projection. It contains no homology-successor assertion.

`lem-sp-filtered-complex-page-homology` records the successor homology calculation,
with a proof computing the kernel as Z_(r+1)/B_r, the incoming image as
B_(r+1)/B_r, and then taking the quotient of quotients. It assumes the differential
data supplied by the preceding node, without assuming any spectral sequence.

All three nodes have actual logged LeanSearch, LeanFinder and grep searches.
LeanSearch returned an Internal Server Error and is recorded as unavailable;
LeanFinder returned general homological-complex results without a filtered-page
match; grep found no Mathlib declarations for these filtered subobject names.
No change record is needed: no existing signature, definition or visibility changed.

## Second reading by B2

1. **Visible interface: pass.** Compared every delivered module with the repository.
   Only PositivePages already exists. Its theorem signature, universes, category
   hypotheses, namespace, visibility, and two public imports are byte-for-byte
   unchanged. Its proof, proof-only imports, and proof description change. The
   three other modules are new. No change record or forced adaptation is needed.
2. **Proof and data: pass as decomposition.** All four files compile through
   `lcompile.py --all` without warnings. Scratch-copy `#print axioms` checks cover
   the original theorem, the three new public theorems, page objects, projections,
   and the page assembly definition. The boundary containment and all definitions
   have only propext, Classical.choice, and Quot.sound. Exactly the two reported
   open theorems and the original theorem depending on them additionally use
   sorryAx. No forbidden declaration mechanism or definition hole occurs. Page
   objects are actual cokernels, not witnesses chosen from an open existence
   theorem. The differential record is uniquely determined by the representative
   equation and epic representative projections. Choosing homology isomorphisms
   occurs only inside the proof of the original existential theorem; no public
   definition selects an arbitrary object or isomorphism from mere existence.
3. **Split statements: pass.** Read both statements and proofs against Stacks
   Tag 012K's Z/B and differential formulas. For the universal representative
   object R, dz factors through the target cycles because d squared vanishes;
   its epic map onto the page ensures the representative equation really forces
   uniqueness. A change of representative in F^(p+1) contributes a target
   r-boundary because (p+r)-r+1=p+1. Kernel and image calculations are valid
   after epic pullbacks, not by assuming projective objects. Zero and constant
   filtrations give zero graded pieces. As a nonzero test, put k in degrees 0
   and 1 with differential the identity, source of filtration weight 0 and target
   of weight 1. At r=1 the two nonzero page terms are connected by the identity;
   their homology and the r=2 quotients both vanish. A weight gap of 2 instead
   gives d1=0 and the identity d2, testing the successor indexing. Negative p,q
   change neither calculation. Neither hole restates the original existential
   spectral-sequence theorem: one concerns a single differential, the other
   its homology without a next-page differential. A fresh LeanFinder search
   using induced maps on subquotients and kernel modulo image, Mathlib grep for
   spectralSequence/filtered homology/differential, and rg over both source roots
   found no ready-made filtered quotient theorem. Mathlib's spectral-object
   construction requires extra spectral-object and page-identification data;
   it does not close either hole directly in a few minutes.
4. **Route and pruning: pass after correction.** The original construction
   assembles the actual page complexes, transports the homology isomorphisms
   along r+1=rprime, and uses identity page comparisons. There is no shorter
   existing declaration applicable to these subquotients in the checked imports.
   Inspected `dag/units/sk-prop-av-pqf-finite.json`: its realized statement and
   proof-step lists are empty, so this auxiliary replacement bypasses no realized
   unit step. The pruning report now accounts for every old proof dependency
   absent from the new direct list, distinguishing exact-couple removal from
   definitions still required transitively. Replaced the spectral-sequence import of the new differential module by
   the two precise homology imports in the new homology module; the existing interface is
   unaffected. All remaining imports support signatures or the construction.
5. **Nodes: pass.** Checked the four JSON nodes against the declarations and
   their actual/proposed proofs. Existing-node changes are restricted to proof,
   proof_deps and proof_origin. Each new node has source, self-contained statement,
   dependencies, proof steps whose uses union is proof_deps, source-based origin,
   search records, split status, created record, blueprint ancestry, chapter/unit,
   and the verbatim Lean theorem signature. The containment node is fully proved;
   the other two are exactly the named, documented holes listed in this report.

Second-reading changes: removed the redundant public SpectralSequence.Basic
import from FilteredComplexPageDifferential and added the precise homology
imports to FilteredComplexPageHomology; completed the pruning inventory and
added this review. No statement or proof body changed. This remains one original
hole closed and two holes added (net -1), with one additional containment theorem
proved outright; it is a decomposition, not a fully proved original theorem.

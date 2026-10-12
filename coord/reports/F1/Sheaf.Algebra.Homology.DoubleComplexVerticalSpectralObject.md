## What changed

The signature and public imports of
`HomologicalComplex₂.exists_verticalSpectralObject` are unchanged. Its proof now constructs
an actual smart-cutoff tower, precomposes Mathlib's mapping-cone spectral object with it,
and applies the homology functor. Mathlib supplies the connecting maps and exactness.
Private, proved helpers establish the extension-restriction isomorphism, zero-source cone
isomorphism, zero cutoffs and strict lower support of totalized windows.

Two new modules are added:

- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps` constructs cutoff objects and
  inclusions explicitly, proves monicity and nested factorization, and constructs the tower.
  Its choice of transition map uses a fully proved factorization theorem; monicity determines
  this map uniquely. No construction chooses data from an unproved existence theorem.
- `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparison` defines the extended-upper-bound
  smart interval explicitly and states the remaining cone-to-window homology comparison.

The item's new imports are proof-only: the comparison module, Mathlib's homotopy-category
spectral object, homology functor, and the source library's triangulated
spectral-object API. All three modules compile together without errors or non-sorry warnings.
There are no forced adaptations and no changes to existing statements or definitions.

## Proved and sorry left

Closed the original hole:
`HomologicalComplex₂.exists_verticalSpectralObject`
(node `lem-sp-double-complex-vertical-spectral-object`). Its Lean proof constructs Y and
proves both support conditions, all finite interval comparisons and the whole interval
comparison from the theorem below. The whole interval comparison and the upper-zero support
condition are proved directly, without using that remaining theorem.

Added exactly one hole:
`HomologicalComplex₂.verticalTower_interval_homology_iso`
(node `lem-sp-double-complex-vertical-tower-comparison`). This is an isomorphism of homology
objects for a concrete mapping cone and a concrete smart interval, in all integer degrees,
with finite lower bound and finite or top upper bound. It asserts neither a spectral object,
connecting morphisms, exactness, first-quadrant conditions nor the whole interval comparison.
It is strictly part of the original argument. Its docstring and node describe the columnwise
quasi-isomorphism and finite-diagonal totalization chase still to formalize.

`HomologicalComplex₂.verticalTower_inclusion_mono_and_factors` is fully proved; its module
contains no sorry. The original item now contains no sorry. This delivery is a decomposition:
one original hole closed and one lower hole added, net zero, not an axiom-free proof of the
original theorem. Every new definition has explicit data and no sorry. The only remaining
sorry in the delivered Lean files is the named comparison theorem above.

Edge cases checked in the construction and mathematical comparison: bottom cutoff is zero;
nonpositive finite cutoffs vanish; top is the reextended original total; equal finite bounds
have acyclic cone and acyclic smart window; negative bounds use extension by zero; negative
homology degrees are included; a finite lower bound cannot lie below bottom; top-to-top
vanishes by the spectral-object isomorphism axiom. The top comparison does not require K to
be bounded above or its truncations to stabilize. The unfinished comparison must keep
column cones integer-indexed, including vertical degree -1; restricting those cones
to nonnegative degrees would incorrectly remove terms. Their lower bound -1 still
makes the totalization chase finite.

## No longer needed

No existing imports, named dependency nodes or modules were removed: the original smart-window
node remains needed. The second reader removed redundant newly added direct proof imports
`Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence` from the item and
`Mathlib.CategoryTheory.Preadditive.Biproducts` from the new tower-maps module; their APIs
remain available through the retained imports, so these are not globally pruned modules. The revised proof avoids the original plan's construction of a descended
triangulated totalization functor on the bounded-below derived category. That work had no
separate dependency node in this item's plan, so no global module-pruning claim is made.
The cone-totalization comparison still contains the necessary finite-diagonal chase, but
spectral-object exactness comes directly from Mathlib. Pruned named modules: none.

## Where the brief, the DAG or earlier work was wrong

The original node marked the triangulated descent and finite-diagonal quasi-isomorphism chase
as elementary steps with no named dependencies. These are the substantial unfinished pieces.
The cone construction avoids the descent, and the concrete homology comparison is now a named
work item. The original docstring is retained; the revised node and this report describe the
implemented cone route.

Searches found Mathlib's mapping-cone spectral object, canonical smart-truncation inclusions
and homological-functor factorization, but no ready-made totalized smart-window comparison.
The source library's BicomplexColumns total quasi-isomorphism results have different support
hypotheses and do not directly close this comparison. Leansearch was unavailable; its recorded
failures are not absence claims. The blueprint source path named by the existing node was not
present locally. The inherited proof and Stacks Homology Section 12.25 (tag 012X) supplied the
mathematical construction; the new smart-window comparison is the explicit elaboration of the
inherited proof's interval identification and finite-diagonal chase, not a verbatim theorem
from Stacks. No existing DAG statement was disputed or weakened. The inherited unit's realized
lists are empty, and no unit statement or realized proof step is bypassed.

## New nodes

`lem-sp-double-complex-vertical-tower-maps`, in
`dag/nodes/sec-abelian-varieties/lem-sp-double-complex-vertical-tower-maps.json`, records the
fully proved monicity and nested factorization of the explicit totalized cutoff inclusions.
Its module also gives the explicit tower objects and the uniquely determined transition maps.

`lem-sp-double-complex-vertical-tower-comparison`, in
`dag/nodes/sec-abelian-varieties/lem-sp-double-complex-vertical-tower-comparison.json`, records
the sole remaining homology comparison and its full natural-language proof. Both new nodes
inherit the original chapter and unit, cite the parent blueprint step, carry genuine search
records, and have signatures extracted from the compiled Lean declarations.

The existing spectral-object node's proof, proof dependencies and proof origin are updated to
match the Lean route. No interface change record is needed.


## Second reading by F1

1. **Existing interface: PASS.** Diffed the original module against the repository version.
   The existing theorem signature is byte for byte unchanged, as are its public imports,
   universe parameters and hypotheses. All added helpers there are private. There are
   no adapted existing modules or changes to existing definitions or target statements.
2. **Proof and data: PASS as a decomposition.** Compiled all three delivered modules in
   import order using lcompile.py. Independently printed axioms in scratch copies for
   the monicity/factorization theorem, tower map, tower, interval definition, comparison
   theorem and original theorem. The constructed data and proved tower theorem use only
   propext, Classical.choice and Quot.sound; the comparison and original theorem additionally
   use sorryAx. The sole textual sorry is the named public comparison theorem. There is
   no axiom, unsafe, opaque, implemented_by, extern or hollow definition. The only chosen
   transition maps come from a fully proved existence result and are uniquely determined
   by composition with the monomorphic top inclusion.
3. **Split-off statement: PASS.** Read its signature, docstring, node and concrete definitions.
   Checked equal bounds, negative bounds, negative degrees, top endpoint, bottom exclusion,
   a complex in one vertical degree, and a two-term column with nonzero differential.
   The quotient retains an extra boundary term, which the quasi-isomorphism to the smart
   lower truncation eliminates; keeping integer-indexed cones is essential. Finite-diagonal
   totalization applies with horizontal lower bound zero and uniform vertical lower bounds
   (the cone of a comparison may require bound -2). The claim is strictly the interval
   homology identification, not another existence-of-spectral-object statement.
   Fresh leanfinder search for preservation of column quasi-isomorphisms, loogle search
   for cone homology, msearch grep for totalization/truncation comparisons, and rg of
   lean/ found no ready-made theorem with this conclusion. Inspected upstream
   BicomplexColumns.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE: it assumes upper
   support in both directions, whereas this construction has lower support. Mathlib's
   complementary-truncation quotient comparison covers the column step, not totalization.
   The remaining theorem cannot be closed by one immediate application of those results.
4. **Route and pruning: PASS after import cleanup.** Read the full proof from the original
   target downward. Mapping-cone spectral objects supply the connecting maps and exactness;
   whole-interval comparison and upper-zero support are proved directly. The lower-support
   and finite-interval clauses use precisely the remaining comparison. Removed the two
   redundant direct proof imports named above and compiled the corresponding scratch copies.
   Removing each remaining new spectral-object API import failed with the expected missing
   declaration or homological-functor instance. The old proof_deps contained only the smart
   window node, which remains used. No old dependency is omitted from No longer needed.
   Inspected dag/units/sk-prop-av-pqf-finite.json: its realized statement and step lists are
   empty, and this delivery changes no unit record or realized route.
5. **DAG agreement: PASS.** Diffed the existing node: only proof, proof_deps and proof_origin
   change. Read both new nodes in full; their declaration signatures agree with the Lean,
   and their source, proof, search records, creation, blueprint, chapter, unit and Lean
   records are present. Their proof steps describe the explicit tower and remaining
   finite-diagonal comparison. The dependency unions match the listed uses.

Changes by the second reader: removed two redundant direct proof imports and updated this
report. No statement, definition, proof term or DAG route required repair. One original
hole is closed and one genuinely narrower hole is added; net zero holes closed.

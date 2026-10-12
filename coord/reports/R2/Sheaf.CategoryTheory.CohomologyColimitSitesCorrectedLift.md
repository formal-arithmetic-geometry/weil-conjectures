## What changed

Proved `CategoryTheory.cohomology_colimit_sites_corrected_lift` without changing its
statement. Added proof-only imports of `CohomologyColimitSitesExactLadder` and the
existing `CohomologyColimitSitesClassDescent`, plus
`Mathlib.CategoryTheory.Filtered.Final` for filteredness of `Under i`. The new exact-ladder theorem supplies
the compatible systems and exact cohomology squares, not a corrected lift. A fully
proved private helper performs the group calculation: lift a class, descend its
correction in the middle system, transport both to a common successor and subtract.
Updated the item's DAG proof to match this reduction. The exact-ladder module
imports the modules of its stated construction and exactness dependencies.
The ladder supplies witnesses in continuation form to avoid repeated dependent
existential elimination of large site expressions; no definition is changed.

## Proved and sorry left

`CategoryTheory.cohomology_colimit_sites_corrected_lift` is proved from the named
exact ladder and existing class descent. Its module has no remaining sorry.
The new module leaves exactly one sorry:
`CategoryTheory.cohomology_colimit_sites_exact_ladder`, node
`lem-weil-pbc-colimit-sites-exact-ladder`. Its docstring gives the complete
compatible injective embedding, cokernel, long exact sequence and naturality proof.
The private `corrected_lift_of_exact_ladder` helper is fully proved.

Holes closed: `CategoryTheory.cohomology_colimit_sites_corrected_lift` (1).
Holes added: `CategoryTheory.cohomology_colimit_sites_exact_ladder` (1).
This is a decomposition, with net zero holes removed; the corrected-lift theorem
still depends on `sorryAx` through its exact-ladder premise. No complete
sorry-free proof of the site theorem is claimed.

## No longer needed

Removed the direct proof import `Sheaf.Paper.ColimitSitesInjectiveSystem` from
the corrected-lift module; it is now a proof-plan import of the new exact-ladder
module. No original dependency is globally pruned:
the injective-system embedding, exact inverse images, exact filtered colimits,
stage injective vanishing and connecting compatibility are used inside the new
exact-ladder node. Class descent remains an explicit dependency of this proof.
The old direct proof dependencies removed from the corrected-lift node are
`lem-weil-pbc-colimit-of-sites-injective-system`,
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`,
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-derived-functor-injective-vanishing`, and
`lem-weil-pbc-site-cohomology-pullback`. All five remain dependencies of the
new exact-ladder node; no module leaves the target import closure.
The correction itself needs no target injective-colimit acyclicity, Cech complex
comparison or Cech vanishing criterion; those are not introduced as direct
requirements of the new ladder. They remain on the separate class-descent route,
so this delivery claims no global pruning of those modules.

## Where the brief, the DAG or earlier work was wrong

The existing connecting-ladder interface gives target surjectivity and a square,
but does not supply stage surjectivity, a natural stage boundary or the middle
system correction maps. Its statement cannot be used to reconstruct its hidden
injective embedding. The new theorem states precisely these missing parts of the
original plan. No statement is changed or disputed. Identity actions need
normalization, as already documented by the existing connecting ladder; the new
ladder retains that normalization in its proof rather than silently imposing an
identity-transition hypothesis.

The source .tex is absent on this machine; Stacks Tags 09YP, 0739 and 0EXZ were
read from their official web pages. The new statement was checked at n=0,
at a singleton index category, with zero coefficients, and with idempotent
identity actions: stage acyclicity applies to n+1, target exactness is used only
at the cokernel term, and no acyclicity of the colimit middle sheaf is asserted.

## New nodes

`lem-weil-pbc-colimit-sites-exact-ladder` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-sites-exact-ladder.json`
states the compatible middle/cokernel systems and their exact cohomology ladder.
It is strictly the construction and exactness portion of the argument, with no
finite-stage descent and no corrected-lift conclusion. Mathlib searches found
Ext exactness ingredients but no whole site-system ladder; LeanSearch returned
Internal Server Error, recorded as unavailable. Blueprint searches
for corrected lift and colimit cohomology found no matching imported node.
No change records: existing public signatures and definitions are unchanged.


## Second reading by R2

1. Compared the delivered corrected-lift module against the repository with
   `diff`, and separately compared the full theorem signature byte for byte:
   identical. No existing definition or public signature is changed, and no
   change record is required. The only new data binders are in the new theorem;
   there is no data-valued definition choosing an arbitrary unproved witness.
2. Compiled both modules in import order with `lcompile.py`, without errors or
   non-sorry warnings. The corrected-lift module has zero sorry tokens, and the
   exact-ladder module has one, in its documented named theorem. Scratch-copy
   `#print axioms` checks cover the private algebra helper, the corrected-lift
   theorem and the new ladder. The helper uses only propext, Classical.choice
   and Quot.sound; both site theorems also use sorryAx, as expected.
   No forbidden declaration or escape hatch is
   present. The site theorem remains conditional on the open ladder.
3. Read the full new signature, its node and its natural-language proof. The
   ladder supplies only the exact-row construction, not representatives or the
   corrected-lift conclusion. Checked n=0 (only positive-degree middle
   cohomology must vanish), the singleton index category, zero coefficients,
   and idempotent identity transitions. Splitting the latter preserves S and
   the specified positive-degree D, so no identity-law hypothesis is added.
   Continuation form is the propositional encoding of existence, not a hollow
   data construction. Independently read Stacks Tags 09YP, 0739 and 0EXZ.
   Repeated leanfinder and loogle searches with compatible short exact sequences
   and `covariantSequence_exact`, and grep searches with injective Ext vanishing,
   found the component Mathlib lemmas but no whole varying-site ladder. Searches
   of both source roots likewise found only the weaker connecting-ladder
   interface. Closing the new construction theorem is not a few-minute task.
4. Read the proof from the corrected-lift target down to the group chase.
   Verified each naturality and cocone equation, the correction sign, and the
   common-successor construction. The actual calculation is fully proved;
   class descent is applied to the middle system in degree n. All added proof
   imports are plain `import`. The report now lists every old direct dependency
   removed from the corrected-lift node and explains where it remains. Checked
   `dag/units/sk-thm-p1.json` realized statement and steps: this item is below
   those unit realizations and none is bypassed or changed.
5. Checked both node proof-dependency sets against the union of step uses, the
   new Lean signature against its verbatim node record, the source, creation,
   blueprint, chapter, unit and search fields, and the existing-node diff:
   only proof, proof_deps and proof_origin change. The DAG follows the Lean
   reduction and records the construction dependencies of the new open lemma.

Second reading changed the exact-ladder proof-plan imports, corrected the
report's claim that no direct import was removed, explicitly recorded one hole
closed and one added as a decomposition, listed all moved dependencies, fixed
the new module's source header (0EXZ belongs to Cohomology on Sites), and removed
excess blank lines. The mathematical proof and existing signature were retained.

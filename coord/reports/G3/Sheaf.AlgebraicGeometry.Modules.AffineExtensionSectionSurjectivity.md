## What changed

Proved `AlgebraicGeometry.Scheme.Modules.epi_globalSections_of_shortExact` with
its exact original signature and visibility. The source library already proves
the shorter Cech argument: a quasi-coherent kernel is Cech-acyclic on affine
opens, giving section surjectivity at the affine open top. Map the sequence by
the exact forgetful functor to abelian sheaves, then use
`ModuleCat.epi_iff_surjective`. No middle-term quasi-coherence is assumed.

Added proof imports of
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
Updated the DAG proof and attached a missing generic topological lifting node
to its already proved source declaration. No new Lean declarations or modules.

The local compiler passes. `#print axioms` for the theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`. The generic lifting source and
its cochain proof were read. Empty spectrum (zero ring), empty open/cover, and
zero terms cause no exception. The unit record `sk-thm-picard-duality` has no
realized node in this argument that is bypassed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.epi_globalSections_of_shortExact`,
node `lem-pc-affine-extension-section-surjectivity`, the only sorry in the item.
Added holes: none. Sorries left in delivered Lean: none. This is a proof, not a
decomposition; its complete axiom check has only the three permitted axioms.

## No longer needed

Removed the unused proof import `Sheaf.AlgebraicGeometry.Coherent`. Also removed the redundant first-worker proof import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`: it is supplied by the
sheafification proof import. Mathlib's
quasi-coherence in the statement is supplied by unchanged public imports.

Replaced the parent's direct proof dependencies `def-pc-scheme`,
`def-weil-sheaf-of-modules-category`, `pqf-def-coherent`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-spec-module-tilde-sections` by exact forgetting, affine Cech
exactness, and the closed topological lifting criterion. The first three
remain statement dependencies; affine localization and tilde facts remain
used inside the existing affine Cech theory. These nodes and Mathlib Tilde
are not claimed to be globally unreachable. No new denominator-clearing or
gluing items are needed. Public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The ideal/principal-open plan is valid, but the proved source Cech lifting
criterion gives a much shorter complete proof. Its wrappers are in
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic`.
The local clone lacks `literature/stacks-project/cohomology.tex` and
`schemes.tex`; source text was read on official Stacks pages for 01EU and 01IE.
LeanSearch returned Internal Server Error, recorded as unavailable.

## New nodes

`lem-pc-topological-ses-cech-sections-surjective` records the generic
topological finite-cover Cech lifting criterion (Stacks 01EU, integer-module
specialization), already proved by
`TopCat.Sheaf.surjective_app_of_exactAt_cechComplex` in
`WeilConjectures.Topology.Sheaves.CechCriterion`. It adds no module or hole.
The existing etale/site lifting nodes have different statements. Blueprint
searches for Cech and surjective found no identical topological statement.
The three logged Mathlib searches returned unavailable/zero hits; direct
source reading found the attached proof. No statement changes, change records,
or forced adaptations.

## Second reading by G3

1. Compared the complete delivered module and existing node with the repository
   using diff. The theorem signature, universes, visibility, docstrings, public
   imports, and mathematical statement are byte-for-byte unchanged. Only the
   proof and private proof imports change; no definition or target changes.
2. Compiled the item locally without errors or warnings. A scratch copy with
   `#print axioms` for `AlgebraicGeometry.Scheme.Modules.epi_globalSections_of_shortExact`
   and `TopCat.Sheaf.surjective_app_of_exactAt_cechComplex` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Delivered Lean has no sorry,
   prohibited declaration, or witness chosen from an unproved existence theorem.
3. No statement or hole was split off. Read the new node's already proved source
   declaration and its cochain lifting proof: local lifts, kernel-valued cocycle,
   degree-one exactness, correction, and gluing prove the stated criterion.
   Empty opens and empty covers give unique sections; zero terms and the zero
   ring need no extra assumption. Independent Loogle search for `"cechComplex"`
   found only the generic Mathlib Cech functor, and grep search for
   `exactAt.*cech|cech.*surject|shortExact.*sections` found no Mathlib replacement.
   Repository searches found the existing source wrapper already used here and
   no duplicate topological DAG node requiring replacement.
4. The proof uses the proved affine Cech wrapper directly, with an exact
   forgetful functor; it neither reproduces the original obligation as a new
   lemma nor introduces a lower hole. Checked every old proof dependency against
   the report's pruning list. All five are listed, with the three remaining
   statement dependencies distinguished. The unit's `realized` statement and
   step lists are empty, so no realized unit step is bypassed. Tested removal
   of the explicit `Sheaf.Limits` proof import: compilation still succeeds.
5. The existing node changes only its proof, proof dependencies, and origin.
   The proof dependency list equals the union of its step uses and names the
   exact forgetting, affine Cech exactness, and existing topological lifting
   argument actually used. The new node records the complete source proof,
   searches, provenance, chapter, unit, and exact Lean statement. It attaches
   existing proved code and adds no module; `lean.file` is correctly absent
   because preflight requires existing-source attachments to deliver no file.

Changed in this second reading: removed the redundant proof import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` and updated this report.
A trial addition of `lean.file` to the existing-source node was rejected by
preflight and reverted; the node is unchanged from the first worker. No mathematical proof repair was needed.

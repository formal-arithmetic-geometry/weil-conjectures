## What changed

Closed the proof body of
`AlgebraicGeometry.Etale.etale_limit_cohomology_eventual_vanishing` without changing
its signature or its public import. The proof supplies affine continuity to a
universally quantified qcqs gluing reduction, obtains a colimit structure on the
specified cocone B, and uses Mathlib's `Concrete.isColimit_exists_of_rep_eq` on
x and zero. The resulting later transition sends x to zero by additivity.

Added two intermediate modules, each with one public theorem: affine-stage
continuity and the reduction from affine-stage continuity to the qcqs case.
Their docstrings give the complete arguments, source tags and edge cases.
Updated the assigned node's proof, proof_deps and proof_origin to match the Lean.
The new modules retain the relevant proof-plan imports, so the geometric work
remains in the target closure rather than being silently pruned.

Local compilation of the three modules succeeds without warnings. The final
delivery check additionally performs the server compilation and axiom probes.

## Proved and sorry left

Hole closed:
`AlgebraicGeometry.Etale.etale_limit_cohomology_eventual_vanishing`
(lem-weil-pbc-etale-limit-cohomology-eventual-vanishing).
No sorry remains in the assigned module.

Holes added, both public named theorems in separate modules:

- `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_comparison`
  (lem-weil-pbc-etale-limit-cohomology-affine-comparison).
- `AlgebraicGeometry.Etale.etale_limit_cohomology_qcqs_gluing`
  (lem-weil-pbc-etale-limit-cohomology-qcqs-gluing).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
It does not claim an axiom-free proof of geometric continuity. The affine lemma
has the strictly restricted affine-stage hypothesis. The gluing lemma assumes
affine continuity universally and isolates the finite-cover reduction; it does
not simply restate eventual vanishing or the whole unconditional continuity
claim. The final common-stage equality argument is complete Lean.

## No longer needed

Removed these direct proof imports from the assigned module:
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`,
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
`Sheaf.AlgebraicGeometry.EtaleMayerVietoris`,
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`,
`Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`,
`Sheaf.AlgebraicGeometry.LimitAffineTransition`,
`Sheaf.CategoryTheory.CohomologyColimitSites`, and
`Sheaf.CategoryTheory.ColimitSites`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
The Sheaf modules remain reachable through the new intermediate modules where
the corresponding geometric argument needs them. The two WeilConjectures imports
are redundant with the unchanged public TopologicalInvariance import.
The second reading also removed redundant direct imports of FullAffineEtaleTopos
and LimitAffineTransition from AffineComparison (both publicly imported by
AffineEtaleSiteColimit), and ColimitSites (publicly imported by
CohomologyColimitSites). Consequently no original node or module is
claimed to be pruned from the target closure. No unit statement or realized
unit proof step has been bypassed.

The old direct proof dependencies replaced by the two helper nodes are:

- `lem-weil-pbc-inverse-image-composition`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-cohomology-pullback`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-affine-etale-site-topos`
- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-colimit-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-cohomology-colimit-of-sites`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-mayer-vietoris`
- `lem-weil-pbc-etale-mayer-vietoris-pullback`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-separated-affine-open-intersection`

These remain facts of the helper route; none is claimed pruned globally.

## Where the brief, the DAG or earlier work was wrong

The current site theorem is an object-cohomology theorem, so applying it at the
identity of a nonaffine scheme is not supported by its affine-site interface.
The parent docstring already identifies this issue. The delivery keeps the
affine case and the two finite-cover inductions distinct rather than invoking
the parent continuity theorem (which would create an import cycle).

The script `blueprint_refs.py ancestor` follows created.item as a node id, but
this stage's created.item is a module name; it returned None for this item.
The new nodes therefore use the existing item's recorded blueprint ancestor,
lemma-weil-pbc-injective-restriction-acyclicity, with the precise continuity
step and intervening nodes stated explicitly.

The LeanSearch endpoint returned Internal Server Error. This is recorded as
unavailable, with the actual other searches retained. LeanFinder returned only
structure-sheaf limit statements and unrelated condensed results; Loogle found
the filtered-colimit equality witness used by the final proof. Grep found
local cohomology and nonabelian H1, neither a geometric replacement.

The first shell heredoc failed because /tmp had exhausted its inodes. The
sandbox filesystem had free space and inodes; edits through apply_patch and
the mandated compiler worked. No shared files were removed.

## New nodes

`lem-weil-pbc-etale-limit-cohomology-affine-comparison`, in
Sheaf.AlgebraicGeometry.EtaleLimitCohomologyAffineComparison: the affine-stage
comparison, with all supplied identifications and legs preserved. It realizes
parent steps 2-4 through affine-site equivalence, strictification, site
cohomology continuity and cofinality. Empty schemes, degree zero and the
one-object system were checked in the statement and proof in words.

`lem-weil-pbc-etale-limit-cohomology-qcqs-gluing`, in
Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing: the conditional gluing
reduction, universally quantified over affine systems in the same universe.
It realizes parent steps 5-8 by restriction to opens, Mayer-Vietoris, exact
filtered group colimits, and separated then general finite-cover induction.
The degree-zero row starts at zero, and separatedness is only required in
the first induction and for an open of an affine in the second induction.
No existing declaration, definition, target statement or change record is
modified or added by this delivery.

## Second reading by S1

1. Compared the delivered existing module with the repository using diff. Its
   complete theorem signature is byte-for-byte unchanged, as is its existing
   docstring and public import. No definition or target changes. Only the three
   permitted proof fields differ in the existing node. The two other modules and
   nodes are new. Verdict: interface preserved.
2. Compiled all three modules in import order through lcompile.py: clean. Scanned
   the full files: exactly two sorry bodies, in the two reported public theorems;
   no definitions, axioms, unsafe/opaque declarations or foreign implementation
   attributes. Read the element proof: the equality witness supplies f and g to
   a common stage; the discarded g is harmless because its image of zero is zero.
   The universe-lifted forgetful functor preservation instance is explicit.
   The scratch #print axioms probes for all three declarations report exactly
   propext, Classical.choice, Quot.sound and sorryAx.
   Verdict: valid assembly, conditional on the two named geometric holes.
3. Read Stacks 09YQ, 0EYL, 09YP and 0A50 online, and the full new signatures and
   nodes. AffineComparison adds precisely affine stages, preserving all coefficient
   coherence equations, object identifications and canonical legs. QcqsGluing
   assumes that affine assertion for every index/system/degree in the same universe;
   cofinal tails are subtypes in that universe. This permits both inductions and
   does not assume continuity of its own nonaffine system. Checked empty schemes,
   zero coefficients, singleton indices and p=0: the last uses the initial exact
   row, with no negative cohomology. In the separated induction each intersection
   has at most n-1 affine opens; in the general induction the intersection is a
   quasi-compact separated open of the singled-out affine. The proofs in words
   specify these reductions and the preservation of the canonical comparison.
   Repeated searches with different wording using msearch LeanFinder, Loogle and
   grep, and rg in lean/Sheaf and the upstream checkout. Hits concern structure
   sheaf sections or fixed-base continuity, not these lemmas. The general
   EtaleCohomologyLimitOfSchemes theorem imports this item and cannot be used here.
   Neither geometric hole can be closed by the available results in a few minutes.
   Verdict: true, smaller argument components; decomposition, not net progress.
4. Read the actual statements in AffineEtaleSiteColimit, FullAffineEtaleTopos,
   CohomologyColimitSites, LimitAffineTransition, EtaleMayerVietoris and its pullback
   module. Site continuity concerns objects, so the final affine object route is
   justified only in the affine case; the second helper retains the required
   gluing route. Reviewed dag/units/sk-thm-p1.json realized: no realized unit node
   is removed or bypassed. All old proof dependencies leave the item's direct
   proof_deps, but their geometric route remains represented in the helper nodes;
   no original module is claimed pruned from the target closure. Removed three
   redundant helper imports, whose public transitive imports retain their modules.
   Corrected No longer needed to include the two additional imports present in
   the current repository baseline. Verdict: no shorter available geometric
   proof; direct imports pruned without changing the unit route.
5. Compared the two new natural-language statements with their Lean hypotheses,
   coherence equations and conclusions. Checked their required node fields,
   source/proof records, blueprint ancestry, and exact normalized Lean signatures.
   Existing node proof_deps is exactly the two helpers actually applied; its final
   elementary step accurately records the Mathlib equality witness and additivity.
   New node dependency unions match their proof steps. Verdict: DAG matches Lean.

Second-reading changes: removed redundant FullAffineEtaleTopos,
LimitAffineTransition and ColimitSites direct imports from AffineComparison;
completed the removed-import report against the current baseline; added this
independent review. No theorem statement, proof body or node statement changed.

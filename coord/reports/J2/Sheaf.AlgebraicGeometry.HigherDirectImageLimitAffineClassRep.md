## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep` with a complete Lean
combination of raw affine class descent and a natural sheafification comparison.
The original theorem statement and public imports are unchanged. The stage raw
class t is sent through the stage sheafification comparison to define y;
comparison naturality and rawPullback(t) = z give the required canonical-map equation.
All three delivered modules compile with the launcher compiler and no warnings.

Added `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`:
the raw presheaf abbreviation and raw pullback map are explicit constructions,
using composition, single-functor and shift isomorphisms. Its theorem isolates the
natural comparison independently of any inverse system or affineness hypothesis.
Added `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep`: its theorem
asserts descent in derived Hom before sheafification, with the same geometric
and coefficient assumptions. Neither theorem repeats the delivered theorem:
one is solely a functorial comparison without continuity, the other solely
continuity without a higher-image section or a sheafification isomorphism.
Updated the existing node's proof route and added nodes for both remaining statements.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_affine_class_rep`
(node `lem-sbc-higher-direct-image-limit-affine-class-rep`). No sorry remains in
the item's module.

Added two holes, both public theorems with source, complete proof in words and node:

- `AlgebraicGeometry.Etale.exists_abelianHigherDirectImage_natural_comparison`
  in `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`,
  node `lem-sbc-abelian-higher-direct-image-natural-comparison`.
- `AlgebraicGeometry.Etale.exists_higherDirectImage_raw_affine_class_rep`
  in `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep`,
  node `lem-sbc-higher-direct-image-raw-affine-class-rep`.

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The final theorem is proved from named intermediate statements; no claim of
sorry-free axiom closure is made. The definitions contain no sorry and select
no data from an unproved existence theorem.

## No longer needed

Removed direct proof imports of
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` and
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit` from the item's module.
Their nodes `sbc-lem-higher-direct-image-presheaf` and
`lem-weil-pbc-etale-cohomology-limit-complex-systems` are now dependencies of the
separate comparison and raw-descent modules, respectively. They remain required
transitively; no module or node is claimed pruned from the targets' closure.
No unused public import was removed. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is mathematically sound but the public abelian
higher-image-presheaf theorem exposes only a Nonempty isomorphism. Its canonical
construction is private and its public interface has no compatibility with
abelianHigherDirectImageMap. An arbitrary isomorphism chosen from that Nonempty
result would not justify the naturality equation. The first new statement
supplies the required uniform natural comparison.

The complex continuity statement is about global unbounded-derived cohomology
of complexes on qcqs schemes. Applying it to the displayed bounded-below raw
Hom classes requires base change of the scheme limit, restriction of coefficients,
the single-complex construction, and the free-sheaf/etale-restriction comparison.
The second statement isolates exactly that bridge before sheafification.
The original theorem remains unchanged and no false statement was identified.

Edge cases checked mathematically: empty U has zero raw and sheaf sections;
p = 0 gives ordinary sections and the usual adjunction comparison; zero
coefficients give zero classes; for a singleton system raw descent is through
an invertible projection and the coefficient colimit isomorphism. The comparison
assertion also allows a zero coefficient map, when both sides are zero. No
restriction of injectives along a general non-etale map is assumed: the raw
cohomology identification only restricts along the etale map U times_S X_i → X_i.

LeanFinder, Loogle and source grep found no existing statement matching either
bridge. LeanSearch returned Internal Server Error, recorded without a verdict.
The full blueprint search found only the broader Tag 03Q8 and Tag 09Z1 statements.

## New nodes

`lem-sbc-abelian-higher-direct-image-natural-comparison` records the uniform
natural sheafification isomorphisms and their compatibility with the explicitly
constructed raw pullback and canonical higher-image map. Source: Stacks 03Q8
and the comparison maps in 09Z1. Its proof spells out local cycles/boundaries,
derived adjunction naturality, and triangle cancellation.

`lem-sbc-higher-direct-image-raw-affine-class-rep` records affine raw derived-Hom
stage representatives. Source: the restricted-cohomology colimit in 09Z1 and
0EZM with lower bound zero. Its proof specifies base change, qcqs hypotheses,
coefficient colimit preservation, and the cohomology-to-derived-Hom transport.

No existing statement or definition changed; no change record is needed.

## Second reading by J2

1. PASS: diffed the sole existing module against the repository. Its theorem
   signature and docstring are byte-for-byte unchanged; only proof imports and
   the proof changed. Both other modules and nodes are new. No target, existing
   definition, hypothesis, or conclusion changed, so no change record is needed.
2. PASS with the two reported holes: compiled all three files in dependency
   order using lcompile.py (6.4, 11.6, 23.4 seconds), without warnings.
   A scratch copy with #print axioms for all five delivered declarations showed
   only propext, Classical.choice and Quot.sound for the raw-presheaf abbreviation
   and raw pullback definition; the two new theorems and original theorem also
   have sorryAx. The only textual holes are the entire proofs of the two new
   public named theorems. No forbidden declaration or hollow definition occurs.
   The existential comparison is eliminated inside a theorem, not used to
   construct public data from arbitrary unproved existence.
3. PASS as a decomposition, not a sorry-free proof: read both new signatures,
   their docstrings and nodes against Stacks 03Q8, 09Z1 and 0EZM. Comparison
   naturality involves no limit; raw descent involves no higher-image section
   or comparison isomorphism. Their combination is a genuine two-step reduction.
   Checked p=0, zero coefficients, empty affine U, singleton and constant
   systems, and identity/zero coefficient maps. Qcqs structure maps over affine
   U give qcqs stage schemes; affine transitions survive base change. Etale
   restriction, not general inverse image, preserves injectives in the Hom
   identification. The upperStarComp and single/shift factors have the correct
   direction. Independently searched LeanFinder twice, Loogle and Mathlib grep,
   and rg on both library roots using Ext, free representables and comparison
   naturality. Inspected the Mathlib sheaf-cohomology definitions and upstream
   module-coefficient naturality: neither states these varying-site abelian
   bridges. Neither hole can be closed by a brief application of those APIs.
4. PASS: the original proof chooses a coherent comparison family, obtains t
   from raw descent, defines y via the stage comparison, and rewrites by its
   naturality and rawPullback(t)=z. All imports support public types/constructions
   or the stated proof routes; proof-only dependencies remain plain imports.
   No longer needed lists both old dependencies removed from the direct route;
   the canonical-map node remains used. Neither old dependency is pruned from
   the transitive closure. Read dag/units/sk-lem-failure-field.json: realized has
   empty statement and step lists, and the higher-image continuity route is
   retained through the same comparison and complex-continuity dependencies.
5. PASS: checked all three nodes. Each proof_deps is exactly the union of the
   steps' uses; the original node describes the actual Lean reduction, and the
   new nodes carry source, full proof, searches, split status, creation record,
   blueprint ancestry, chapter/unit and matching Lean declaration/signature.
   The original statement and statement dependencies stay unchanged.

Second reading changed only review documentation and search evidence: appended
this section and added independent search results to the two new nodes.
No Lean proof or statement repair was necessary. One original hole is closed,
two lower holes are added; net -1, with no module pruned from the target closure.

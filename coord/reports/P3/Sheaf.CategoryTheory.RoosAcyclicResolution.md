## What changed

Completed `CategoryTheory.exists_roos_acyclic_resolution` without changing its signature,
its existing docstring, or either existing product definition. The proof constructs the
resolution from explicit finite-prefix functors, proves natural product-limit isomorphisms,
and computes the induced differential coordinatewise as `1 - shift`.

Added three modules: `Sheaf.CategoryTheory.RoosFinitePrefixes` (explicit construction,
short exactness, and transition surjectivity), `Sheaf.CategoryTheory.RoosFinitePrefixLimits`
(the explicit product limit cone), and `Sheaf.CategoryTheory.RoosPrefixAcyclic` (the single
remaining derived-limit vanishing statement). The item imports the last two privately;
their public imports expose the finite-prefix definitions needed in their own signatures.
All definitions are genuine constructions; no witness is chosen from an unproved existence
statement. `prefixLimitIso` is constructed from the proved cone universal property.

Repaired the inherited node metadata: exact Lean signatures, correct module ownership,
self-contained helper statements, complete dependency lists, genuine recorded searches,
and blueprint ancestry. Removed copied maintainer review fields from new nodes. Updated
the parent proof and dependencies to match the Lean assembly. The interface record is
`coord/changes/roos-prefix-interface.md`.

## Proved and sorry left

Closed the item's sole hole, `CategoryTheory.exists_roos_acyclic_resolution`
(node `lem-pc-roos-functorial-acyclic-resolution`). Its proof depends on the smaller
acyclicity theorem below: this is a decomposition, with one hole closed and one added,
not an unconditional proof or a net reduction in holes.

Proved `CategoryTheory.roosPrefixInclusion_projection`,
`CategoryTheory.roosPrefix_shortExact`, `CategoryTheory.roosPrefix_transition_surjective`,
`CategoryTheory.roosPrefixCone_coordinate`, and the complete construction
`CategoryTheory.roosPrefixConeIsLimit`. The item's private helpers prove the natural
limit comparison and differential compatibility. These use no new holes.

Exactly one `sorry` remains in the delivered files:
`CategoryTheory.roosPrefixAcyclic`, in `Sheaf.CategoryTheory.RoosPrefixAcyclic`,
node `lem-pc-roos-prefix-acyclic`. It asserts only positive derived-limit vanishing for
explicit restriction towers; it does not assert the resolution, exactness, product-limit
identifications, naturality, or differential formula. Its docstring and node give the
surjective-tower dimension-shifting argument. Its source is Stacks Tag 07KW (3).

All four modules compile with `lcompile.py --all`. The zero-index edge cases are explicit:
`T_0(A)_0` is an empty product, the difference map onto it is surjective, and the limit
cone still extracts coordinate i from prefix i+1. Transition surjectivity also covers
empty prefixes. No declaration excludes arbitrary universes or arbitrary abelian towers.

## No longer needed

No existing item import was removed, and no globally unreachable module is claimed pruned.
Removed the redundant `Mathlib.CategoryTheory.Limits.Shapes.Products` import from the
new limit helper. Made `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` a private
proof import in the construction helper, retaining only `ShortComplex.ShortExact` publicly.
The original proof's direct use of `lem-pc-tower-surjective-lim-acyclic`, module
`Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic`, is replaced by the finite-prefix
acyclicity item. It is not imported. Its generic dimension-shifting dependencies remain
in the new node's plan and may be imported by its future worker without a cycle.

The parent no longer directly lists `def-weil-inverse-system` or `lem-pc-tower-abelian`
as proof dependencies: the construction node uses them instead. These nodes remain
needed for the statements and construction, so they are not globally pruned.
The product transition definition remains needed for the differential calculation.
The unit's `realized` record has no bound nodes here; the existing finite-prefix route
under its first-step derived-limit computation is preserved.

## Where the brief, the DAG or earlier work was wrong

The prior BLOCKED diagnosis was not a delivery-tool failure. Preflight correctly rejected
missing LeanSearch records, placeholder signatures, a wrong module name, and an unnamed
change record. The helper nodes had copied the entire parent statement instead of their
own smaller claims and retained unrelated review records. These errors are repaired.
The report had duplicate New nodes headings and a second-reader section written by the
worker; both were removed. This report deliberately leaves that section to the reader.

The existing generic surjective-tower theorem is mathematically sufficient, but unusable
as an import at this position: `import_direction.py may` confirms it already reaches
`RoosAcyclicResolution` through `DerivedLimitRoosAbelianGroups`, so importing it would
close a Lean import cycle. Changing that other module's public imports is not forced by
our interface and is therefore outside this delivery. The restricted acyclicity item
retains the independent dimension-shifting proof rather than the circular Roos route.
The four underlying modules for injective embeddings, split-tower injectivity, limit
exactness with surjective kernels, and horseshoe connecting morphisms all pass the
import-direction check against this item.

A read-only DAG traversal also found an existing two-node statement/proof dependency cycle between
`lem-weil-pbc-horseshoe-delta-functor` and `lem-weil-pbc-derived-functor-long-exact`.
Both edges exist in the base repository; none of the new nodes occurs in this cycle.
This is reported for the maintainer rather than edited outside the item. All references
in the delivered nodes resolve, and the delivery tool verifies the Lean imports are acyclic.

Read Stacks Tag 07KW at https://stacks.math.columbia.edu/tag/07KW: its B and C towers
are exactly the present prefixes after shifting the paper's positive indices to Lean's
zero-based indices. Searches found no categorical finite-prefix resolution or derived
acyclicity theorem in Mathlib. LeanSearch returned an Internal Server Error, recorded as
unavailable; LeanFinder and source searches returned the actual results in searches.jsonl.

## New nodes

`lem-pc-roos-finite-prefix-construction` records the explicit prefix functors, natural
augmentation/difference, short exactness, and surjective restriction transitions in
`Sheaf.CategoryTheory.RoosFinitePrefixes`. All its declarations are proved or constructed.

`lem-pc-roos-finite-prefix-limits` records the full product's limit universal property and
coordinate independence in `Sheaf.CategoryTheory.RoosFinitePrefixLimits`. Both the cone
and its universal property are explicit and proved.

`lem-pc-roos-prefix-acyclic` records the only remaining hole in
`Sheaf.CategoryTheory.RoosPrefixAcyclic`. Its dimension-shifting proof plan cites existing
injective-embedding, split-tower, exact-limit, and derived long-exact-sequence nodes.
It includes all hypotheses of its Lean theorem, including enough injectives and
additivity; the general tower left-exactness theorem supplies left exactness.

Change record: `coord/changes/roos-prefix-interface.md`.

## Second reading by P3

1. Compared the delivered parent module with the repository version. The theorem signatures and existing definitions are byte-for-byte unchanged; only imports, private proof helpers, and the proof body changed. New module declarations are separate nodes and do not alter existing interfaces. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The only remaining `sorry` is the named theorem `CategoryTheory.roosPrefixAcyclic`, with a matching node and docstring. No axioms, unsafe, opaque, extern, or hollow definitions were added. Verdict: pass subject to the documented split theorem.

3. Checked the split statements against their Lean declarations and the finite-prefix construction. The prefix short exactness, limit cone, and acyclicity statements are strictly smaller than the parent target; the acyclicity statement has the required hypotheses and covers q ≥ 1. Searches and source citations are recorded, and no duplicate library theorem was found. Verdict: pass.

4. The proof follows the finite-prefix route: explicit towers, short exact sequence, limit cones, differential comparison, then prefix acyclicity. The generic surjective-tower import is correctly omitted to avoid the documented import cycle. The report's no-longer-needed imports and dependency pruning agree with the proof. Verdict: pass.

5. Node metadata, Lean declarations, proof dependencies, proof origins, and blueprint ancestry were checked. The unit remains `sk-thm-picard-duality`; no unit realized route is bypassed. Verdict: pass.

Changed after reading: no mathematical or interface changes; added this second-reading record only.

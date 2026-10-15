## What changed

Repaired the returned delivery against the current base, preserving all existing
Lean declaration signatures, visibility, and imports. Replaced the finite-cover
separatedness proof in `CartesianHigherImageAffineSectionLocalVanishing` by the
standard sheaf-of-types separatedness argument. This removes the auxiliary map
from the universe-lifted integers and its scalar calculations. The proof applies
`IsSeparatedFor.ext` to the generated covering sieve and uses naturality on each
of its arrows. Both an empty covering family and empty affine objects are covered
by the sheaf condition itself.

Corrected the local-sieve docstring to describe the actual locally bijective
comparison and finite-raw-class proof, and replaced its dangling blueprint id by
the existing item node. Added the missing docstring for the final finite-cover
extraction. Updated the item's proof-dependency record to match the implemented
proof and registered its already existing raw-class dependency as a DAG node.

The returned duplicate declaration is already repaired in the current base:
`LowerShriekCoherence.lean` declares `local_preservesInjectiveObjects_lowerStar`
and registers that name as a local instance. The conflicting global name is
provided by `DerivedPasting.Vertical`. This delivery adds no instance or public
name and changes no importer-facing interface, so it preserves that repair.
It does not include a redundant adaptation of `LowerShriekCoherence`.

Validation: `lcompile.py --all` compiled the repaired item (49.1 seconds) and an
unchanged copy of `LowerShriekCoherence` (8.9 seconds) together, with the consumer
using the sandbox item's compiled output. The temporary consumer source was then
removed from the delivery. The declaration comparison reports no interface,
statement, visibility, public-name or import changes and no new sorry. The import
direction check permits the existing finite-raw-class dependency.

## Proved and sorry left

No new holes closed relative to the current base, which already has zero sorries
in the assigned module. Zero holes added and zero split off. The three existing
public declarations remain proved:

- `AlgebraicGeometry.Etale.cartesianHigherImage_section_eq_zero_of_finite_cover`
  (proof simplified in this repair);
- `AlgebraicGeometry.Etale.cartesianHigherImage_affine_section_local_zero_sieve`;
- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_affine_section_local_zero`.

All existing private helpers remain proved. There is no sorry left in any
delivered Lean file. The existing imported theorem
`AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_classes_eq_zero`
in `CartesianHigherImageFiniteRawClassVanishing` still has its pre-existing sorry;
its newly registered node is
`lem-sc-cartesian-higher-image-finite-raw-class-vanishing`. That module is held by
H3 in the current claim snapshot and is not changed or split by this delivery.
Its remaining work is the affine-chart/raw-class descent and canonical
cohomology-continuity comparison described in its existing theorem docstring.
The new node records that work so it is visible in the DAG.

## No longer needed

No import or module removed. The second reading also removed the provisional
`lem-weil-pbc-colimit-site-raw-abelian-section-evaluation` edge from the new
raw-class node: derived continuity directly descends global hypercohomology
classes, so a separate ordinary-section colimit lemma is unnecessary for that
plan. This is not a claim that its module is globally pruned.

Every direct import remains used: transitions in
the signatures, CohomologyColimit for finite affine cover extraction, the private
comparison API in AbelianHigherDirectImagePresheaf, and finite raw-class vanishing.

Removed these direct proof-dependency edges from the item's node:
`lem-weil-pbc-derived-etale-cohomology-limit`,
`lem-sbc-abelian-higher-direct-image-natural-comparison`, and
`lem-sc-cartesian-derived-image-map-exchange`. The first and third are still needed
below the raw-class dependency and are not claimed as globally pruned. The direct
natural-comparison theorem is replaced by the already proved locally bijective
derived-Hom comparison in `sbc-lem-higher-direct-image-presheaf`.

The returned consumer adaptation is unnecessary on the current base and is not
included. Consequently its unrelated inherited private axiom from
`PicardH1ProductSpanningBypass` does not enter the delivered declarations' axiom
checks. No attempt is made to hide, replace or bypass an axiom used by the assigned
module.

## Where the brief, the DAG or earlier work was wrong

The dispatcher report was stale: the assigned module is already sorry-free.
The previous report incorrectly treated this as preventing a repair delivery;
returned-delivery repairs need not close an already closed hole. The current base
also already contains the consumer helper rename requested by the original
compiler failure. Repeating that consumer adaptation would be redundant and had
caused the unrelated private-axiom rejection reported in the return.

The item's DAG still described a monolithic continuity proof while the Lean uses
local derived-Hom representatives and a finite-raw-class theorem. That existing
theorem had a blueprint tag but no node, and the local-sieve helper referred to
another nonexistent node. This repair corrects the proof record and docstring
reference without introducing another mathematical obligation.

The earlier claim-lock checkout failure is handled by the current delivery tool;
no manual git command, claim edit, or repository edit was used.

## New nodes

`lem-sc-cartesian-higher-image-finite-raw-class-vanishing` registers the existing
`exists_cartesianHigherImage_finite_raw_classes_eq_zero` theorem in its existing
module. It adds no Lean declaration and no sorry. Its statement isolates the
finite raw-derived-class part of the argument, preceding homology-section and
sheaf-separatedness glue. Searches were run through msearch (LeanSearch was
unavailable; LeanFinder, Loogle and grep ran), and Stacks Tags 0EYM, 0EYL and 0GIT
were read. No change record is required: existing signatures, definitions and
public imports are unchanged.


## Second reading by V1

1. **Interface preservation: PASS.** Read the full delivered module and its diff
   against the repository. All seven existing declaration headers are byte for
   byte identical, including private helpers. Only the finite-cover proof body
   and two docstrings differ; imports, visibility, definitions and public names
   are unchanged. There is no target or statement change and no change record
   is needed. The returned consumer name conflict is already repaired in the
   current base by `local_preservesInjectiveObjects_lowerStar` with local-instance
   registration, so no consumer adaptation belongs in this delivery.

2. **Proof and axioms: PASS, relative to the reported existing dependency.**
   Independently compiled the delivered module with `lcompile.py`: exit 0, no
   warnings, 47.3 seconds. Compiled a scratch copy with `#print axioms` for all
   seven declarations: exit 0, 48.4 seconds. The four private helpers and
   `cartesianHigherImage_section_eq_zero_of_finite_cover` use only `propext`,
   `Classical.choice`, `Quot.sound`. The local-sieve and finite-cover-existence
   results additionally use `sorryAx` through the existing finite-raw-class
   theorem. There is no sorry or forbidden declaration in the delivered source;
   no data is chosen from an unproved mere existence theorem. The private
   comparison is the displayed canonical homology map, not an arbitrary iso.

3. **Residual statements: PASS with proof-record repair.** No statement or hole
   is split off. Read the existing finite-raw-class theorem, its docstring, its
   new registration and the declarations of its planned dependencies. It is a
   strict raw-derived-class subproblem, without homology-section lifting or
   sheaf-separatedness glue. Checked the empty family, empty affine object,
   degree zero and identity transition cases. Read Stacks 0EYM, 0EYL and 0GIT.
   The new node's first step needed a global descent justification: after
   descending the affine test object, apply 0GIT with fixed coefficient the
   original stage derived image to descend its raw hypercohomology class.
   Exchange then gives a chart class; a second application of 0GIT with F[0]
   kills it at a finite stage. Rewrote that plan explicitly, retained the
   canonical map identifications, corrected `IsCofiltered.wideSpan` to
   `IsCofiltered.wideCospan`, and dropped the unnecessary ordinary raw-section
   evaluation dependency. This does not close the imported theorem's hole.
   Independent LeanFinder/Loogle searches used global hypercohomology descent
   and sheaf-separatedness queries; rg checked Mathlib and both library roots.
   Hits for structure-sheaf sections and fixed-base higher images have different
   coefficients or interfaces; no duplicate exact theorem was found.

4. **Route, imports and pruning: PASS.** Checked the proof from the final
   finite-cover extraction through the local sieve, canonical derived-Hom
   comparison, and raw-class dependency. The replacement finite-cover proof
   directly uses Mathlib's sheaf-separatedness API and naturality; it handles
   the empty covering family without a nonempty assumption. All four imports
   are used, and only the transition module is public because only it is needed
   in public signatures. The removed original proof-dependency edges are all
   listed under No longer needed; none is claimed as globally pruned.
   `dag/units/sk-thm-vanishing.json` has no realized statement or step pointing
   to these nodes; no unit realization or unit-level argument is bypassed.

5. **DAG agreement: PASS after the repair in point 3.** The item's proof,
   proof_deps and proof_origin describe the actual local-bijection, finite
   raw-class and separatedness argument. Its only changed fields are those
   three permitted proof fields. The added node registers the already landed
   raw-class theorem, adds no Lean declaration and no sorry, has all required
   metadata and a verbatim Lean statement. Checked that all dependencies exist
   and each proof_deps list equals the union of its steps' uses. Its remaining
   proof is a plan, not a claim of a completed Lean proof.

Second-reader changes: the new raw-class node's proof, proof_deps and
proof_origin, the corresponding No longer needed note, and this independent
review. No further Lean edit was needed. Net holes closed: 0; holes added: 0;
new split-offs: 0; modules pruned: none. This is a returned-delivery repair.

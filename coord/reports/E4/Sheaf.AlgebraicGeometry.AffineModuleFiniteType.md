## What changed

Completed the proof of `AlgebraicGeometry.Scheme.Modules.affine_module_finite_type`
in `Sheaf.AlgebraicGeometry.AffineModuleFiniteType`, preserving its signature and
public imports. The proof transports finite type across the given isomorphism,
refines finite generating covers to affine opens, proves the finite-generator
section calculation, and applies the existing affine finite-type criterion in
both directions. Its private helpers are all proved.

Added one proof import and one new module,
`Sheaf.AlgebraicGeometry.AffinePushforwardFreeEvaluation`, for the local
finite-free evaluation criterion used in the section calculation. Added the
proof import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` for
`freeSectionsLinearEquiv`. Updated the item's DAG proof to the argument actually
implemented and wrote the new node's full statement and proof plan.

Repaired the earlier sandbox attempt: its map-identity simplification resolved
`Functor.map_id` to the unrelated root Functor declaration. Qualifying
`CategoryTheory.Functor.map_id` repairs the calculation. The finite-generator
bridge is now a proved private helper of the item instead of a second public
module. A local `PUSH` notation avoids capturing the named `R :=` parameter of
free modules. The finite free calculation has a documented local heartbeat
setting; the affine criterion is elaborated once and reused.

## Proved and sorry left

Closed the sole original hole, in
`AlgebraicGeometry.Scheme.Modules.affine_module_finite_type`
(node `lem-weil-pbc-affine-module-finite-type`). The delivered item has no
`sorry`. The private lemmas `finiteType_of_data`, `finiteType_of_generators`,
`finiteType_of_iso`, `affine_generators_cover`, and
`affine_pushforward_finite_generators` have complete Lean proofs.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushforward_free_evaluation`, in
`Sheaf.AlgebraicGeometry.AffinePushforwardFreeEvaluation`, node
`lem-weil-pbc-affine-pushforward-free-evaluation`. Its proof is exactly
`:= by sorry`. This is a decomposition (one original hole closed, one local
hole added; net zero), not an axiom-free proof of the global result. The
remaining theorem concerns a specified finite free evaluation on one affine
open; it contains no finite-type equivalence or isomorphism to an arbitrary M.
All cover refinement, finite spanning-family construction, surjective-image
finite generation, and local-to-global assembly are proved in Lean.

The two delivered modules compile through `lcompile.py --all`. The item's
statement is unchanged, and no definition or existing public interface changes.

## No longer needed

Second-reader correction: `lem-weil-pbc-spec-tilde-free-module` is also removed
from the item's direct `proof_deps`. The implemented proof uses the generic
upstream `SheafOfModules.freeSectionsLinearEquiv`, not `tildeFinsupp`, `tildeSelf`,
or `isoTop`. The tilde/free node remains in the new local criterion's proof plan,
so this is direct dependency pruning, not global module pruning.


Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`;
- `Sheaf.AlgebraicGeometry.Coherent` (the required declarations are already
  publicly available through the unchanged correspondence import);
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`;
- `Sheaf.AlgebraicGeometry.TensorPullback`.

`lem-weil-pbc-affine-finite-type-generating-sections` is no longer needed by
this proof: finite sections directly give finite direct-image generators via
the proved private spanning-family construction and the local evaluation
criterion. The earlier sandbox's separate
`AffinePushforwardFiniteGenerators` module is not delivered; its argument is
proved privately in the item, so no node or new work item for it is needed.

The item's proof no longer invokes
`lem-weil-pbc-affine-module-correspondence`; its public module import remains
unchanged, as part of the original statement interface. The original direct
proof dependencies `def-pc-module-pullback`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and
`lem-weil-pbc-quasi-coherent-module-cokernel-image` move to the new local
criterion's plan. They are not globally pruned. `TensorPullback` may remain
reachable through the unchanged correspondence import. No claim is made that
other targets cease to need any of these modules. The unit's realized statement
and proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had no report or node records and did not compile its
finite-generator bridge. These omissions and the map-identity error are repaired.
The originally imported declarations do not directly state the needed local
evaluation criterion for an A-valued pushforward over a slice site. That is
precisely the remaining glue of original steps 2 and 3, now one named local
statement with its source and complete proof in words. Its proof should use the
finite-free basis comparison and the existing affine image formula; no new
finite-type theorem is assumed.

No mathematical statement error or unit-route departure was found. The local
criterion was checked on the identity morphism (ordinary affine exactness), the
empty open/empty inverse image (both target section modules are zero), and the
empty finite family (both conditions say the quasi-coherent module on the
inverse image is zero). No surjectivity of f, finite type of its algebra, or
Noetherian hypothesis is needed.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as
unavailable rather than no match. Loogle, LeanFinder, Mathlib/source-library
searches, and whole-blueprint searches found no existing relative evaluation
criterion. The Stacks sources were read at
https://stacks.math.columbia.edu/tag/0897,
https://stacks.math.columbia.edu/tag/01SB,
https://stacks.math.columbia.edu/tag/01IC, and
https://stacks.math.columbia.edu/tag/01PB.

## New nodes

`lem-weil-pbc-affine-pushforward-free-evaluation` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-pushforward-free-evaluation.json`
records the finite-free evaluation criterion on a single affine open. Its source
is the finite-type detail omitted in Tag 0897, worked out using the affine
correspondence of Tag 01SB and affine quasi-coherent image computation of Tag
01IC. The node has three actual search kinds, the inherited chapter/unit and
blueprint ancestry, the exact Lean signature, and a three-step proof explaining
the finite-free comparison, local-image implication, and affine-basis converse.
Change record: `coord/changes/affine-module-finite-type-private-helpers.md`.
The conservative interface checker flags lexical section/local-notation additions;
the record lists the scoped commands and every transitive importer, explaining
that no existing public signature, definition, instance, or public import changes.

## Second reading by E4

1. Interface: PASS. Compared the complete diff against the repository module
   and mechanically compared every existing declaration's statement and visibility.
   The sole public theorem's signature is byte-for-byte identical. Its restored
   local R notation expands to the original pushforward functor. The original
   public import is identical; all changes to the item are proved private helpers,
   proof-only imports, scoped commands documented in the change record, and its
   proof body. No target, definition, instance, or existing public signature changes.
2. Proof and trust: PASS as a decomposition. Both modules compile locally.
   There is precisely one direct sorry, the named public evaluation theorem;
   no definition with sorry and no forbidden declaration or trust escape occurs.
   A scratch copy printed axioms for the original theorem, the new theorem, and
   all five private helpers. Only propext, Classical.choice, Quot.sound, and
   (for the evaluation theorem and declarations using it) sorryAx occur.
   finiteType_of_data, finiteType_of_generators, finiteType_of_iso, and
   affine_generators_cover have only the three allowed axioms. No arbitrary
   data is chosen from an unproved existence theorem.
3. Split statement: PASS. The finite evaluation criterion is true and strictly
   smaller than the finite-type equivalence: it concerns one specified map on one
   affine open, without any finite-type hypothesis or arbitrary module isomorphism.
   Its docstring gives both implications, including finite-free comparison,
   pulling local lifts back, affine image exactness, and the affine-basis converse.
   Checked identity f, empty V, empty inverse image, I empty (epi iff F vanishes
   on the affine inverse image), and zero F. None requires f to be surjective or
   finite, or rings to be Noetherian. Independently read Stacks Tags 01SB, 01IC,
   and 0897. Fresh LeanFinder search for global-section preservation/detection of
   epimorphisms and grep for surjective_app_of/epi_of_surjective/free pushforward
   found generic criteria, not this relative slice-site evaluation statement.
   Read the existing affine generating-sections and quasi-coherent image proofs;
   their ordinary O_U-module lemmas still require the comparison to the A-valued
   slice-site map. Closing that comparison is not a short application available
   in the existing library. No new split statement was added by this reader.
4. Route and pruning: PASS after cleanup. Read the proof from the public theorem
   down through the affine-cover, finite-spanning-family and transport helpers.
   The affine finite-type criterion is used in both directions; the local
   evaluation hole is exactly the remaining original steps 2 and 3. Read
   dag/units/sk-thm-p1.json and its realized statement and steps: no realized node
   is bypassed or changed by this node-level reduction. Removed the unused
   tilde/free node from the item's direct dependencies; the report now names every
   removed old proof dependency, including dependencies retained only in the new
   local plan. No globally unreachable module is asserted without a closure check.
   The new module's Coherent import was replaced by the two Mathlib imports its
   signature needs, avoiding an unnecessary public import of the project's
   coherence/derived-Hom module chain.
5. DAG and records: PASS after cleanup. The existing node changes only proof,
   proof_deps, and proof_origin. The new node has the exact Lean signature,
   complete source/proof/search records, status, creation and ancestry fields,
   and inherited chapter/unit. Its plan dependencies agree with the complete
   natural-language argument. The existing node's implemented proof now cites
   no unused tilde/free comparison. The change record accurately explains the
   conservative command-level interface flag without alleging a statement change.

Second reading changed only the new module's imports, removal of one unused
main-node proof dependency, and this report. One original hole is closed and
one lower hole is added: net zero, still a decomposition, not a completed
axiom-free proof of affine_module_finite_type.

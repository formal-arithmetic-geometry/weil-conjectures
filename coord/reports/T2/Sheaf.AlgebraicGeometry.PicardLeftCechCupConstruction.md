## What changed

Closed `AlgebraicGeometry.Scheme.Modules.picardLeftCechCup_exists` without changing
its signature, its coordinate predicate, or either public import. Added a private
proof import of `Sheaf.AlgebraicGeometry.PicardLeftCechCupNaturality`.

Added three modules, all fully proved:

- `Sheaf.Algebra.Homology.TensorTotalExtensionCoordinates` constructs the comparison
  from the tensor total of extended complexes to the extension of the natural total,
  with the exact pure-tensor summand equation. The construction uses coproduct descent,
  zero maps on negative bidegrees, and separate horizontal/vertical differential checks.
- `Sheaf.AlgebraicGeometry.PicardLeftCechCupComponent` reuses
  `picardExternalCechCupComponent_exists` on the finite affine open families. Compose its
  extension with the proved tensor-total comparison and verify the requested coordinates.
- `Sheaf.AlgebraicGeometry.PicardLeftCechCupNaturality` proves left-coefficient naturality
  of any such components. Negative bidegrees vanish. On nonnegative bidegrees, total,
  tensor and tuple extensionality reduce to adjunction-unit and restriction naturality,
  followed by tensor-section naturality.

The original theorem chooses one component per left coefficient, uses the proved
naturality theorem to construct a natural transformation, and applies the component
coordinate proofs. All four modules compiled together without errors or warnings.
The proof keeps the cube/Kunneth unit route and only replaces the below-unit glue.
No existing definition, theorem statement or visibility changed; no forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.picardLeftCechCup_exists`
(node `lem-sc-picard-left-cech-cup-construction`).

New proved statements:
`HomologicalComplex.tensorTotalExtend_coordinates`
(node `lem-sc-tensor-total-extension-coordinates`),
`AlgebraicGeometry.Scheme.Modules.picardLeftCechCupComponent_exists`
(node `lem-sc-picard-left-cech-cup-component`), and
`AlgebraicGeometry.Scheme.Modules.picardLeftCechCupComponent_naturality`
(node `lem-sc-picard-left-cech-cup-naturality`).

No sorry remains in the item or any added module. Holes closed: 1. Holes added: 0.
This is a proof from an existing stated dependency, not a decomposition into new holes.
The existing dependency
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupComponent_exists`
(node `lem-sc-picard-external-cech-cup-component`) is proved in the current source but still depends on the open differential theorem
`picardExternalCechCupDegreeMaps_comm` (node
`lem-sc-picard-external-cech-cup-differential`). This dependency was already used
by the publicly imported right-coefficient construction.

The edge cases were checked in the proof: negative indices are handled using
`isZero_extend_X` and preservation of zero by either tensor functor; the negative-to-zero
boundary is checked explicitly. Degree zero has the surviving (0,0) summand. Neither
coefficient naturality nor component construction needs quasi-coherence or affine
intersection hypotheses. Empty covers, empty schemes and zero coefficients introduce
no exceptional branch. No arbitrary witness from an unproved mere existence theorem
is stored in a definition: all new comparison data are explicitly constructed, and
chosen cup maps occur only inside existence proofs; their coordinate condition determines
the maps by tensor, coproduct and product extensionality.

## No longer needed

The second reader replaced the new comparison module's broad public import
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` with the smaller
`WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`. The latter supplies
the natural-index total signs; ModuleCat colimits supply the total objects.
The larger module remains reachable through the existing Cech models, so this
is import minimization, not a claim of pruning it from the target closure.

No original import was removed: both public imports remain necessary for the original
statement and its section/face definitions. The three new proof imports in the component
and original module are all used.

The original proof no longer directly uses
`def-sc-cech-refinement-cochain-map` / `Sheaf.Paper.CechRefinementCochainMap`.
Its separate additive refinement-map statement is unnecessary here: the existing scalar
natural-index external cup component already supplies the needed cochain map. Removed
this edge from the item's proof plan. The other two old direct edges, `def-sc-cech-cup-product` and
`lem-pc-module-pullback-adjunction`, are now indirect through the naturality node.
The cup and pullback-adjunction nodes remain used
through the component and naturality arguments and are not pruned.

`Sheaf.Algebra.Homology.FirstQuadrantTotalExtension` /
`lem-sc-total-extension-nat-arrow-iso` was inspected but not imported: its arrow
isomorphism does not state the precise tensor-factor summand coordinate equation.
The new comparison is constructed directly using Mathlib.

## Where the brief, the DAG or earlier work was wrong

The DAG plan correctly describes the geometry, but its refinement lemma is additive
and does not itself give the scalar tensor-total map or its extension coordinates.
The existing natural-index component theorem is the shorter route. The left and right
Cech functor definitions are definitionally equal in natural degrees, but their integer
sources differ: left uses the total of the extensions, right the extension of the total.
The new proved comparison addresses precisely that difference.

LeanSearch returned Internal Server Error; the searches are recorded as unavailable,
without an absence verdict. Loogle, LeanFinder and Mathlib/project source searches ran.
Blueprint searches for `Cech cup`, `extension total` and `012Z` found no equivalent
blueprint node. The existing first-quadrant arrow comparison was read and does not
supply the required tensor-factor coordinate equation.

The local literature/stacks-project TeX files are absent on this machine. The official
Stacks pages for Tags 012Z, 0BED and 07MB were read instead; their URLs are recorded in
the new nodes. WANTED: literature/stacks-project/homology.tex, Tag 012Z;
literature/stacks-project/varieties.tex, Tag 0BED; literature/stacks-project/cohomology.tex,
Tag 07MB. The proofs are marked as agent-written direct verifications from these formulas.

## New nodes

`lem-sc-tensor-total-extension-coordinates` records the proved algebraic reindexing
comparison and its pure-tensor equation, in
`lean/Sheaf/Algebra/Homology/TensorTotalExtensionCoordinates.lean`.

`lem-sc-picard-left-cech-cup-component` records one extended cup cochain map with
coordinates, without coefficient naturality, in
`lean/Sheaf/AlgebraicGeometry/PicardLeftCechCupComponent.lean`.

`lem-sc-picard-left-cech-cup-naturality` records the proved naturality equality for
components already satisfying those coordinates, in
`lean/Sheaf/AlgebraicGeometry/PicardLeftCechCupNaturality.lean`.

All new nodes inherit the original chapter and unit. Each module contains one public
statement; the component predicate and proved private helpers support those statements.
No change record is needed because existing interfaces are unchanged.

## Second reading by T2

1. **Existing interfaces — pass.** Read the original and delivered construction
   modules and their full diff. The sole changes are the private naturality import
   and the body of `picardLeftCechCup_exists`. Its signature and the complete body
   of `IsPicardLeftCechCup` are byte-for-byte unchanged. The three other modules
   are new; there are no forced adaptations or statement changes.
2. **Proofs — pass.** Read all four modules from the top theorem down to the
   coproduct construction. Local compilation and explicit axiom checks are recorded
   below. No delivered theorem contains `sorry`, and there is no hollow definition
   or forbidden declaration. `termIso`, `descNat` and `mapX` construct their data
   explicitly. Choosing components occurs within an existence proof, with their
   coordinates fixed; no arbitrary unproved witness becomes definition data.
3. **New statements — pass.** There are no split-off holes. The three proved
   helpers separate comparison, component existence and coefficient naturality.
   Read the existing natural-index component, right-coefficient naturality and
   `FirstQuadrantTotalExtension`: none already states the required left integer
   tensor-total coordinates. Independent Loogle search for `mapBifunctor, extend`
   found no match; LeanFinder with a coprojection/extension query returned generic
   monoidal tensor maps, not this comparison. Source searches used tensor/extension
   and coefficient/naturality terminology in Mathlib, Sheaf and upstream Lean.
   Read official Stacks Tags [012Z](https://stacks.math.columbia.edu/tag/012Z),
   [0BED](https://stacks.math.columbia.edu/tag/0BED), and
   [07MB](https://stacks.math.columbia.edu/tag/07MB). The comparison verifies the
   total differential formula; the geometric statements isolate the cochain map
   and coefficient functoriality, without asserting a cohomology isomorphism.
   Negative summands, total degree -1 to 0, degree (0,0), zero factors and empty
   tuple families are covered by the zero-source and extensionality arguments.
   No affine-intersection or quasi-coherence property is used in these steps.
4. **Route and pruning — pass.** The top proof assembles components using the
   naturality equality. Component existence extends the existing natural-index
   cup and precomposes the explicit comparison. Naturality uses the coordinate
   hypotheses, adjunction-unit naturality, restriction naturality and
   `whiskerRight_app_tmulSection`. Public imports expose the objects appearing
   in signatures; proof-only component/comparison/naturality imports are private.
   Narrowed the comparison's total-complex import to its signs dependency and
   compiled that module successfully. All old proof-dependency edges are accounted
   for under No longer needed. Read `dag/units/sk-prop-av-cube.json`: its existing
   `realized` arrays are empty; this delivery does not alter them or replace the
   cube unit's step. Only below-unit Cech glue changes.
5. **DAG — pass.** The original node changes only `proof`, `proof_deps` and
   `proof_origin`. Its proof now cites component existence and naturality. The
   component node cites the existing external component and extension comparison;
   the naturality node cites the component predicate, pullback adjunction and cup
   construction; the comparison cites the total-complex definition. Each union
   of step dependencies equals `proof_deps`. The three new nodes have source,
   stepwise proof, searches, creation, blueprint, chapter/unit and verbatim Lean
   statement records. Their hypotheses and conclusions match the actual Lean.

Changes by the second reader: narrowed one new public import; corrected the new
geometry modules' author attribution to T2; corrected the report's stale claim
that the existing component theorem itself is unproved; clarified the old
proof-dependency edges and that import minimization does not prune a reachable
module. No proof body or theorem signature needed repair.

Validation: `lcompile.py --all` compiled all four delivered modules with no errors
or warnings. The independently narrowed comparison also compiled cleanly.
A scratch module with `#print axioms` for all four public theorems and the new
component predicate compiled cleanly: the comparison, predicate and naturality
use only `propext`, `Classical.choice`, `Quot.sound`; component existence and
`picardLeftCechCup_exists` also use inherited `sorryAx` through the already-open
external cup differential dependency. No new hole was added. Thus “proved 1 of 1”
here counts the original local hole closed; it does not assert that the target's
entire import closure is axiom-free.

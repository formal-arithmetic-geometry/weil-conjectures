## What changed

Replaced `CategoryTheory.exists_homologyEvaluation` with a complete ExistsUnique proof
combining cycle-evaluation existence, uniqueness of cycle evaluation, and local perfection.
Each of these steps is stated in a separate new module, using the original numbered plan.
Extracted the five existing interface declarations unchanged into
`Sheaf.Algebra.Homology.HomologyEvaluationDefinitions` to avoid import cycles. The item
publicly re-exports that module and retains its original public API through transitive re-exports. Its three
proof-step imports are private imports. The target theorem signature and the two subsequent
existing declarations remain unchanged.

The interface relocation is recorded at
`coord/changes/homology-evaluation-shared-interfaces.md`. There are no adapted modules.
All five modules compile through the required launcher. The unit's realized statement and
steps are untouched; the work remains within the existing local evaluation argument.

## Proved and sorry left

Closed the original hole in `CategoryTheory.exists_homologyEvaluation`
(node `lem-sc-homology-evaluation-formal-complex`). The item now contains no `sorry`.
This is a decomposition, not an unconditional proof: one hole closed, three holes added,
so the net hole change of this delivery is -2.

The three new holes, all exactly `:= by sorry`, are:

- `CategoryTheory.exists_homologyEvaluation_cycle`, in
  `Sheaf.Algebra.Homology.HomologyEvaluationCycleExistence`,
  node `new-b2-homology-evaluation-cycle-existence`: descent of the bilinear cycle pairing.
- `CategoryTheory.homologyEvaluation_unique_of_cycle`, in
  `Sheaf.Algebra.Homology.HomologyEvaluationUniqueness`,
  node `new-b2-homology-evaluation-uniqueness`: uniqueness from local cycle representatives.
- `CategoryTheory.homologyEvaluation_local_iso_of_cycle`, in
  `Sheaf.Algebra.Homology.HomologyEvaluationLocalIso`,
  node `new-b2-homology-evaluation-local-iso`: restriction, roof comparison, and finite-free
  zero-differential calculation.

The shared definitions module introduces no hole and has no new data construction.
Every new theorem has its source and complete natural-language argument in its docstring.
The edge cases checked in those arguments are empty opens, zero complexes, zero rings,
rank zero, and degrees outside the finite support. Existence and uniqueness are stated
without the local perfection hypotheses. Local perfection assumes both concentration
and the exact roof/K-injectivity hypotheses of the original theorem.

## No longer needed

Removed redundant direct imports of `Sheaf.Algebra.Homology.HomComplexProjections`
and `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` from the item; both
remain publicly reachable through HomologyEvaluationDefinitions. Replaced the
shared definitions module's KInjective import with Mathlib.Algebra.Homology.QuasiIso.
No original node or module is pruned. The original plan's projection,
restriction and K-injective comparison results remain needed by the corresponding new
proof steps, although they are not directly applied by the upper ExistsUnique proof.
The original public API is retained through transitive re-exports. No unit-route node is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the Lean statements. The new shared-definition
node incorrectly imposed cohomology concentration in its prose, although none of
its definitions assumes it; the second reader removed that prose assumption and
the irrelevant K-injectivity statement dependency. The original node lists definitions, projections,
restriction and quasi-isomorphism comparison, but none of their available signatures
constructs the homology evaluation pairing, proves uniqueness, or performs the finite-free
calculation directly. The three new statements expose precisely these gaps rather than
assuming that a restriction isomorphism alone supplies evaluation compatibility.

The semantic-search hits concern the additive-group Hom complex, not the sheaf-valued
internal Hom here. Loogle supplies homology cokernel and epi interfaces but no finished
bilinear descent theorem. LeanSearch returned an Internal Server Error, recorded as
unavailable. A blueprint search for homology evaluation returned no exact existing node.

## New nodes

`new-b2-homology-evaluation-definitions` records the unchanged shared interfaces in
`HomologyEvaluationDefinitions`. This is a relocation, not a replacement definition or
a new existence witness.

`new-b2-homology-evaluation-cycle-existence` states the cycle pairing descent, the first
and existence half of the second original proof steps. Its source is Tag 0A8X's product
Hom differential and the existing argument for evaluation in the item's docstring.

`new-b2-homology-evaluation-uniqueness` states only uniqueness given two cycle-evaluation
morphisms; its proof uses local representatives and separatedness, independently of
local perfection.

`new-b2-homology-evaluation-local-iso` states only perfection of a morphism already
satisfying the cycle characterization. Its proof retains both original steps 3 and 4,
using the existing open restriction and quasi-isomorphism comparison nodes.

All nodes lie below the same finite-duality blueprint ancestor and carry the original
chapter and unit. The parent node now records the actual three-lemma ExistsUnique proof.
The only change record is `coord/changes/homology-evaluation-shared-interfaces.md`.

## Second reading by B2

1. **Visible interface — pass.** Compared the item with the repository by `diff`.
   Compared the raw signatures of all eight existing declarations byte for byte
   across the item and shared module; all match. The five relocated declarations,
   including their complete bodies and docstrings, are unchanged. The relocation
   has its change record; no target statement or mathematical definition changes.
   Repository `rg` confirms that SelfExtTorResolutionModel is the only external
   module mentioning the moved names. Its import continues to expose them.
2. **Proof and trust — pass as a decomposition.** All five files compile locally
   through lcompile.py. The upper ExistsUnique proof correctly combines the three
   strictly partial assertions and reverses uniqueness in the required direction.
   Exactly the three reported public theorem bodies contain `sorry`; no forbidden
   declaration or holed definition occurs. A scratch copy with `#print axioms` for
   all eleven delivered declarations reports only propext, Classical.choice and
   Quot.sound, plus sorryAx for the three split statements and the declarations
   depending on them. The five shared interfaces have no sorryAx dependency.
   The existing homologyEvaluation choice is from an ExistsUnique statement and
   therefore determines the object, rather than choosing an arbitrary witness.
3. **Split statements — pass.** Rechecked the component differential signs,
   annihilation of both sorts of boundaries, local cycle lifts, and separatedness.
   The two cycle lemmas require neither concentration nor perfection; local
   perfection requires both the original concentration and roof/K-injectivity
   assumptions. The zero complex, zero ring, rank zero, empty open, and degree
   outside support cases obey the same formulas. All three have source-bearing
   docstring proofs and corresponding nodes. A fresh leanfinder query about
   bilinear cochain evaluation and local epimorphism lifts returned additive-group
   Hom-complex results only. Fresh grep searches of Mathlib and repository sources
   found homologyMap/cokernel tools, not these sheaf-valued statements. A fresh
   Loogle query for CategoryTheory.SheafOfModules.homObj was uninformative because
   the service does not index that identifier; it is not evidence of absence.
   Read LocalFiniteFreeHomologyNatural and DerivedSingleHomEvaluation: their
   proved comparisons do not supply the cycle-characterized evaluation here.
   Checked Stacks 0A8X's signed differential and 0A95's K-injective comparison.
4. **Route and pruning — pass after import repair.** Existence, uniqueness and
   local perfection are genuine separate parts of the original four-step argument;
   the delivery is one hole closed and three added (net -2), not an unconditional
   proof. No lower hole was closed in this reading. Removed the item's redundant
   HomComplexProjections and Modules.Sheaf direct imports, both still publicly
   re-exported by Definitions. Replaced Definitions' large KInjective import by
   the smaller QuasiIso import needed for its interfaces. LocalIso now publicly
   imports KInjective for its signature and privately imports HomComplexRestrictOpen
   and QuasiIsoHomComplexMap for its recorded proof plan. All six old proof_deps
   remain below the new statements: cochain complexes in their interfaces; Hom
   complex, sheaf Hom and projections in cycle descent/uniqueness; restriction and
   RHom comparison in local perfection. No old dependency node or module is pruned.
   The unit's realized fields are unchanged (its statement and step lists are
   currently empty); the finite-duality subargument follows the same unit route.
5. **Nodes — pass after correction.** The parent proof and proof_deps name exactly
   the three lemmas used by the Lean proof. Each new proof_deps equals the union of
   its proof steps' uses; all new nodes have creation, source, blueprint, chapter,
   unit and Lean records. Removed the shared-definition node's spurious prose
   concentration assumption and irrelevant K-injectivity statement dependency.
   The new Lean statements are otherwise unchanged. The change record now quotes
   the actual old and new declaration text verbatim and describes the final imports.

Second reading changed imports, the shared-definition node's prose/dependency,
change-record quotations, and this report. It did not change any Lean statement,
definition body, theorem proof, or count of holes.

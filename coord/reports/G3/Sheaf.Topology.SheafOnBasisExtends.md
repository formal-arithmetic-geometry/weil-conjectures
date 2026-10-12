## What changed

Proved `TopologicalSpace.Opens.exists_sheaf_extension_of_basis_gluing` in
`Sheaf.Topology.SheafOnBasisExtends`, preserving its signature and visibility.
The proof makes the inclusion of the basis cover dense, proves that the given
presheaf is a sheaf for its induced Grothendieck topology, and applies Mathlib's
comparison equivalence. Its inverse unit supplies the isomorphisms on basic opens;
naturality proves the displayed compatibility with restrictions.

The induced-topology step is proved explicitly: index a covering sieve by all its
arrows, lift that index type into `Type (max u v w)`, verify that their basic domains
cover, restrict sieve compatibility to basic intersections, and apply `hglue`.
Existence and uniqueness of the sieve amalgamation both follow from that same
unique-gluing conclusion. Empty covers are included without a nonemptiness assumption.

Added proof-only imports of `Mathlib.Topology.Sheaves.SheafCondition.Sites`,
`Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology`, and
`Mathlib.Algebra.Category.Grp.Limits`. Separate removal trials confirmed each is
necessary. Updated only `proof`, `proof_deps`, and `proof_origin` in
`lem-weil-pbc-sheaf-on-basis-extends.json` to record the actual Mathlib route.
No definition, statement, target, public import, or other module was changed.
The declaration docstring, updated during the second reading, the node and this
report describe the shorter formal proof.

## Proved and sorry left

Closed the one original hole:
`TopologicalSpace.Opens.exists_sheaf_extension_of_basis_gluing`
(node `lem-weil-pbc-sheaf-on-basis-extends`).

No holes remain in the delivered module; no holes or new declarations were added.
This is a complete proof, not a decomposition. `lcompile.py` compiles without
warnings. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The extension is the comparison equivalence's constructed image of `F`, rather
than arbitrary data chosen from an unproved existence statement.

## No longer needed

Removed the proof import `Sheaf.Topology.BasisSheafSectionsGerms`.
The following three planned dependencies are unnecessary for this proof and were
removed from the node's `proof_deps`:

- `def-weil-pbc-basis-presheaf-stalk` (Mathlib colimit leaf; no dedicated module).
- `lem-weil-pbc-basis-sheaf-sections-germs`
  (`Sheaf.Topology.BasisSheafSectionsGerms`).
- `lem-weil-pbc-local-predicate-sections-sheaf`
  (Mathlib `TopCat.subpresheafToTypes.isSheaf` leaf; no dedicated module).

These are pruned from this node's route; this report does not assert that no other
node needs them. No unit's realized statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The earlier search correctly identified the comparison
lemma as a possible shorter route, but left the induced-topology sheaf-condition
translation unresolved. That translation is now proved directly in Lean and needs
neither pairwise-pullback instances on the basis nor a precoverage presentation.
The basis inclusion's fullness is supplied explicitly, while faithfulness follows
from thinness. The covering index type is lifted to match the exact universe in
`hglue`. The subgroup/stalk construction in the original plan is consequently
unnecessary. The unit `sk-thm-reduction` and its realized route are unchanged.

## Second reading by G3

1. **Interface — pass.** Read the complete module and diffed it against the repository.
   The existing theorem signature is byte for byte unchanged; visibility, universes,
   hypotheses, conclusion, public imports and definitions are unchanged. Only proof
   imports, the theorem proof and its explanatory docstring differ. There are no
   adapted modules, new declarations or statement-change records.
2. **Proof — pass.** Independently compiled the delivered module and a scratch copy
   with `#print axioms TopologicalSpace.Opens.exists_sheaf_extension_of_basis_gluing`.
   The compiler accepts the proof and reports only `propext`, `Classical.choice` and
   `Quot.sound`. Inspected all delivered Lean for forbidden declarations and holes:
   none occur. Reviewed the covering-sieve translation, the fully faithful basis
   inclusion, the direction of the inverse unit and the naturality equation. The
   extension is Mathlib's constructed comparison image, with no unproved witness.
3. **Split statements — pass, none.** No statements or holes were split off. Checked
   the empty-space/empty-basis case, empty covers of a basic empty open, singleton
   covers and repeated opens: no nonemptiness or distinctness assumption enters.
   Empty-cover unique gluing forces the empty-open group to be trivial when present.
4. **Route and pruning — pass.** Read Mathlib's comparison equivalence, induced-topology
   covering criterion, basis density criterion and limit-reflection sheaf criterion.
   Additional `msearch.py` grep/loogle searches and searches of the project/upstream
   topology sources found no direct replacement for the explicit sieve argument.
   The three added imports are proof-only and supply density, comparison and group
   limits, respectively; removal trials were checked independently. All three old
   `proof_deps` are listed under No longer needed. Read `sk-thm-reduction.json`:
   this auxiliary node is not a realized statement or step, and its route is intact.
5. **DAG — pass.** Compared node JSON with the repository: only `proof`, `proof_deps`
   and `proof_origin` differ. The three recorded steps match the proof; their empty
   node-dependency union agrees with `proof_deps = []` because the route uses proved
   Mathlib tools only. Statement, source, Lean record and unit are unchanged. No new
   nodes require validation.

Changed the stale theorem proof docstring to describe the actual comparison proof,
and corrected the corresponding report sentence. No proof repair was needed.
One original hole closed, zero holes added; this is a proof, not a decomposition.

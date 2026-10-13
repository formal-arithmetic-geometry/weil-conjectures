## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.FormalCompletionAffineNaturalComparison` by a complete Lean proof
with the original statement and visibility. The concrete realization is the functor
`formalAffineSectionLimit`: push formal-system levels forward along the open inclusion,
evaluate on U, and take the actual ModuleCat limit. Its data is constructed, not chosen
from an existence theorem.

Added `Sheaf.AlgebraicGeometry.FormalAffineSectionLimit`, with the concrete section,
tower and limit functors and the remaining full-faithfulness lemma. Added
`Sheaf.AlgebraicGeometry.FormalCompletionAffineQuotients`, whose finite-level quotient
comparison is proved. The latter first identifies original and restricted sections using
the restriction/pushforward adjunction unit and hρ. It imports all of
`Sheaf.AlgebraicGeometry.CoherentMapReductionTorsionKernel` proof-only and uses its existing
private theorem `AlgebraicGeometry.quotient_affine` directly. The duplicate local
`positivePowerQuotient_sections` declaration and its proof have been removed.
The quotient equivalences are explicitly built with `quotEquivOfEq` and
`quotKerEquivOfSurjective`. Both naturality equations are proved on quotient representatives.

The main proof uses `adicCompletion_iso_of_stable_ranges` with c=0, proving its kernel
and range hypotheses from those quotient equivalences. This determines the comparison
isomorphisms uniquely by their projection equations. It proves preservation of zero maps
directly by `limit.hom_ext`. Full faithfulness supplies reflection of limits. The final
naturality equation follows from `Concrete.limit_ext`, the limit-map projection equation,
and the proved finite-level coherent-map equation.

Existing public imports are retained; all added imports in the item's module are proof-only.
Transparency options are scoped to the theorem. No existing definitions, signatures,
instances, attributes, or visibility were changed. The DAG records the concrete route.
All three delivered modules compile locally without warnings, within the per-file limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.formalCompletion_affine_natural_comparison`, the original one
hole. Its full Lean combining proof is complete.

Also proved: `AlgebraicGeometry.formalCompletion_affine_quotients`
(node `lem-weil-pbc-formal-completion-affine-quotients`), including all finite-level
transition and coherent-map naturality equations. The previously reported private
`AlgebraicGeometry.positivePowerQuotient_sections` was deleted as a duplicate; its existing
proved replacement is `AlgebraicGeometry.quotient_affine`, with no additional hole.

Added and left: `AlgebraicGeometry.formalAffineSectionLimit_full_faithful`
(node `lem-weil-pbc-formal-affine-section-limit-full`), with whole proof `:= by sorry`.
It is strictly the realization-morphism part of the argument: it takes arbitrary formal
systems, has no coherent input G or restriction functor ρ, and asserts no comparison
with adic completion or its naturality. Its docstring gives the quotient-descent proof.
The three functor definitions contain no holes.

This is a decomposition: one original hole closed and one lower hole added (net zero).
No claim is made that the resulting declaration has no transitive sorry dependency.
The remaining node can be proved independently using the affine equivalence or by
quotient descent and the source library's affine Hom correspondence.

## No longer needed

Current second reading also removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` from the main item module.
A scratch compile without it passed; its declarations are available through retained
imports. This removes a redundant direct import, with no global module pruning.

No original import was removed and no global module pruning is claimed.
The original node no longer directly needs the separately chosen affine equivalence,
isomorphism transport, affine adjunction, or restriction-colimit lemma: those realization
facts are confined to the remaining full-faithfulness node, while the proved quotient
comparison needs only the restriction adjunction and the ideal-product/cokernel formulas.
They remain dependencies of the new nodes where appropriate, so are not claimed obsolete.

Repair of the maintainer's duplicate-statement return: removed the private declaration
`AlgebraicGeometry.positivePowerQuotient_sections` and replaced its sole application with
`AlgebraicGeometry.quotient_affine`. Added the proof-only
`import all Sheaf.AlgebraicGeometry.CoherentMapReductionTorsionKernel` to access the
existing private theorem without changing its visibility. Removed direct proof imports
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: the quotient proof no longer
uses their declarations directly. These modules remain transitive dependencies of the
existing helper, so no global pruning is claimed. The quotient node records the new
edge to the reduction-torsion-kernel module specifically for its proved private helper;
the public reduction-torsion conclusion is not applied.
No change to the unit statement or its realized proof steps is made.

Second reading: removed the redundant proof-only import
`Mathlib.LinearAlgebra.Isomorphisms` from `FormalCompletionAffineQuotients`;
the quotient-equivalence API is already available through its retained imports.
No global module pruning results from this removal.

For completeness, every old proof dependency absent from the new item's `proof_deps`:
- `def-weil-affine-spectrum`: affine presentation belongs to the full-faithfulness node.
- `lem-weil-pbc-affine-tilde-gamma-adjunction`: retained below full faithfulness.
- `lem-weil-pbc-coherent-formal-modules-iso-equivalence`: retained below full faithfulness.
- `lem-weil-pbc-coherent-formal-modules-affine`: retained below full faithfulness.
- `def-weil-pbc-coherent-formal-module`: retained below the quotient node and used in signatures.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`: now transitive through the existing
  quotient helper in the reduction-torsion-kernel module.
- `lem-weil-pbc-module-restriction-open-immersion-colimits`: its recorded restriction
  adjunction is retained below the quotient node.
These are replacements of direct edges, not globally obsolete nodes.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an existing theorem word for word. The earlier choice
to reproduce its private helper was wrong: `import all` provides access to the proved
helper directly. The duplicate declaration has now been removed, its one call replaced,
and its direct imports and quotient-node proof route updated.

No mathematical statement was found false. The original plan is valid but its scheme-
isomorphism equivalence statement does not supply a componentwise section compatibility
for the equivalence. Constructing the section-limit functor directly separates that
realization issue from the quotient identification and allows the latter to be proved.
The source of full faithfulness is the quotient formula of 087W; every A-linear map of
limits descends modulo J powers, so completed-scalar restriction causes no failure of
fullness on these objects. This is not claimed for arbitrary completed-ring modules.

The local literature copy `literature/stacks-project/coherent.tex` is absent on this machine.
The cited Stacks pages were read at https://stacks.math.columbia.edu/tag/087W and
https://stacks.math.columbia.edu/tag/0881. Their equivalence and affine identification agree
with the route used here. LeanFinder, Loogle and Mathlib source searches found no exact
comparison or full-faithfulness theorem. LeanSearch returned Internal Server Error;
its search record says unavailable and has no no-match verdict.

Edge cases were checked against the actual quotient and limit constructions: J=0 gives
constant positive quotients; J=1 gives zero quotients; zero modules and empty opens use
the same equations. The stable-range specialization uses c=0 and no positivity on c,
no properness and no short exact sequence.

## New nodes

`lem-weil-pbc-formal-affine-section-limit-full` records the concrete realization functors
and the remaining morphism reconstruction problem. Its one theorem is in
`lean/Sheaf/AlgebraicGeometry/FormalAffineSectionLimit.lean`; its source is 087W.

`lem-weil-pbc-formal-completion-affine-quotients` records the proved finite-level part,
in `lean/Sheaf/AlgebraicGeometry/FormalCompletionAffineQuotients.lean`, from the affine
identification of 0881. The quotient equivalences and their naturality are constructed
and proved in Lean; this node adds no sorry.

The existing natural-comparison node has its proof, proof_deps and proof_origin updated.
No interface change record is needed: only new modules and an unchanged existing theorem
with additional proof-only imports are delivered. No forced adaptations are present.

## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Compared the item's module with the repository using `diff` and
   compared its entire theorem signature byte for byte: identical. The only existing
   declaration change is its proof, with theorem-scoped transparency options and
   additional proof-only imports. The other two modules are new. No change record or
   forced adaptation is required; no definition or target statement was changed.
2. Kernel and construction: PASS. Compiled all three modules in import order using
   `lcompile.py`; no errors or warnings. Scanned all delivered Lean for prohibited
   declarations and holes: only the reported whole-theorem full-faithfulness `sorry`.
   A scratch module prints axioms of all three functor definitions and public theorems.
   The definitions and finite-level quotient theorem use only `propext`,
   `Classical.choice`, `Quot.sound`; the remaining lemma and main theorem additionally
   use `sorryAx`. The functors use actual pushforward, evaluation and ModuleCat limits.
   The locally chosen quotient and limit equivalences come from proved theorems;
   projection equations uniquely determine the latter isomorphisms.
3. Remaining statement: PASS as a genuine decomposition. Read Stacks 087W and 0881
   and checked the actual formal-object definition: coherent levels, positive-power
   annihilation, and successive quotient transitions. Projection surjectivity and
   ideal-power kernels reconstruct every A-linear map levelwise, so fullness holds
   even after forgetting completed scalars. Faithfulness follows by the same
   surjectivity and affine Hom faithfulness. Zero ideal gives constant systems; unit
   ideal gives zero systems; zero modules and the empty affine open are covered.
   The docstring contains the reconstruction argument and the matching node exists.
   Independent Loogle, LeanFinder and local-source searches with different queries
   found no exact theorem. The affine-equivalence result has projection equations,
   but transporting them to this concrete open-section functor is substantial work,
   not a short existing-lemma application. No new hole was introduced by this reading.
4. Route and pruning: PASS after repair. Read the proof top down: finite-level
   equivalences give the stable-range hypotheses with c=0, and projection equations
   give naturality. The remaining lemma asserts only morphism reconstruction and
   supplies limit reflection, not the original completion-comparison conclusion.
   Removed one redundant proof-only import after a successful scratch compile.
   Listed every old direct dependency replaced by the new route under No longer needed.
   Read `dag/units/sk-thm-p1.json`: neither this item nor its new lower lemmas replace
   a realized unit statement or step; the unit's realized route remains unchanged.
5. DAG: PASS after repair. Checked the existing node and both new nodes against Lean.
   Added the missing coherence bridge, tensor-product and cokernel-image dependencies
   to the quotient node, recomputed `proof_deps` from its steps, and recorded both new
   public theorem signatures verbatim. Source, proof origin, searches, creation,
   blueprint ancestry, chapter and unit records are present. The full-faithfulness
   node records its remaining mathematical proof plan; the main node records the
   concrete section-limit and c=0 comparison proof that is actually written.

Changes by this reader: redundant import removed; quotient-node proof dependencies
completed; new-node Lean signature records made verbatim; independent searches added;
pruning report expanded. Lean proof bodies and mathematical statements were retained.
The result remains one original hole closed, one strictly lower hole added: net zero,
with the finite-level quotient theorem fully proved without transitive sorry.


## Second reading by A2

1. Interface: PASS. Independently diffed the existing main module against the read-only
   repository and compared its whole theorem signature byte for byte: identical. The
   other two delivered modules are new. Existing visibility and public imports are
   unchanged; all added imports of the main module are proof-only. No definition of an
   existing declaration or target statement changed, and no change record is needed.
2. Proof and construction: PASS. Independently compiled all three modules with
   lcompile.py in import order, without errors or warnings. The prohibited-declaration
   scan found only the reported whole-theorem sorry. A scratch module printed axioms
   of all three functor definitions and all three theorems: definitions and quotient
   comparison use only propext, Classical.choice, Quot.sound; full faithfulness and
   the main theorem additionally use sorryAx. Read the quotient construction and the
   stable-range application: neither selects arbitrary data from an unproved mere
   existence claim. The functors are constructed, and the limit isomorphisms are
   determined by their projection equations.
3. Split statement: PASS as decomposition, not net proof progress. Read the actual
   IsCoherentFormalModule conditions and Stacks 087W and 0881. The affine Noetherian
   quotient formula supplies surjective projections with ideal-power kernels; any
   A-linear map preserves those kernels and descends uniquely to the levels. Affine
   Hom correspondence reconstructs the sheaf maps; cancellation proves compatibility
   and faithfulness. This is strictly the morphism-reconstruction part of the original
   statement, with no coherent input G, restriction functor rho, or completion comparison.
   The zero ideal, unit ideal, zero modules, and empty affine open satisfy the same
   argument. Its source, complete proof docstring and matching node are present.
   Ran fresh Loogle, LeanFinder and grep queries with different wording and inspected
   local affine equivalence/transport declarations: no exact existing full-faithfulness
   result, and no short direct application closes the remaining lemma.
4. Route and pruning: PASS after a small repair. Read the main argument top down:
   concrete limit, zero-map preservation, finite quotients, c=0 stable-range comparison,
   and projectionwise naturality. It uses the existing proved private quotient_affine
   through import all, avoiding the duplicate responsible for the previous return.
   Removed redundant proof-only Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
   from the main module after a successful scratch compile without it. It remains
   available through retained imports, so no global module pruning is claimed.
   Every old direct proof dependency absent from the new route is listed above under
   No longer needed. Checked dag/units/sk-thm-p1.json realized: this item and its new
   lower statements are not realized unit statements or steps; the unit route is kept.
5. DAG: PASS. Compared the main node and both new nodes with the written Lean:
   proof steps and proof_deps match the concrete route and existing quotient helper.
   New-node signatures agree with Lean, and source, proof origin, searches, creation,
   blueprint ancestry, chapter and unit fields are present. Added this reader's fresh
   search results to the remaining full-faithfulness node.

Changes by this reading: removed the redundant ConcreteCategory.Basic proof import;
updated the main theorem's obsolete equivalence-based proof docstring to describe its
actual concrete-limit proof; recorded fresh searches and this independent review.
Proof bodies and mathematical statements were retained. Closed one original hole,
added one strictly lower hole, net zero; the finite-level quotient theorem is proved
without transitive sorry. Globally pruned modules: none.

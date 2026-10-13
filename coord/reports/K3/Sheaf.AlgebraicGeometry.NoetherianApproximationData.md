## What changed

Completed AlgebraicGeometry.noetherian_approximation_data with its original signature.
The proof uses the existing finite-presentation spreading-out theorem, descends the
flat complex, refines the model to descend the perfect object, and constructs the
final complex by additive tensor pullback. Naturality proves the differential identities.

Added three helper modules, each with a matching node: FilteredCartesianFlatComplexDescent,
FilteredCartesianPerfectDescent, and TensorPullbackFlatProperSupport. The first two are
proved wrappers around the existing directed-index descent declarations: a final directed
poset in the filtered under-category of the chosen stage handles the original arbitrary
small filtered category, and explicit pullback isomorphisms handle noncanonical models.
The third isolates cartesian base-change preservation for a single module.

All four modules compile together through lcompile.py --all; no compiler warning occurs.
No existing definition, declaration signature, public import, or target statement changed.
All additions to the item's imports are proof-only. The unit record has no realized nodes;
the original spreading-out, flat-complex descent, and perfect descent route is retained.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.noetherian_approximation_data
(lem-pc-noetherian-approximation-data). Its proof is complete relative to the imported
statements. Also proved both new declarations:

- AlgebraicGeometry.filtered_cartesian_flat_complex_descent
  (lem-pc-filtered-cartesian-flat-complex-descent).
- AlgebraicGeometry.filtered_cartesian_perfect_descent
  (lem-pc-filtered-cartesian-perfect-descent).

Added exactly one hole, as the entire proof of the public named theorem
AlgebraicGeometry.tensorPullback_flat_proper_support
(lem-pc-tensor-pullback-flat-proper-support). Its source and complete argument are in
its docstring and node. It concerns one module under cartesian base change, with no
filtered diagram, descended scheme, complex, or perfect derived object; it is strictly
smaller than the original simultaneous approximation assertion.

This delivery is a decomposition: one original hole closed and one new hole added,
net zero holes. The original existing finite_flat_proper_support_descent and
perfect_complex_descends remain imported and unproved here. The perfect refinement
also uses the existing derivedPullback_preserve_perfect and
exists_derivedPullbackComposition. No claim of a sorry-free transitive proof is made.
No data definition chooses an arbitrary witness of an unproved existence theorem:
all existential elimination in the delivery occurs inside theorem proofs.

## No longer needed

No mathematical dependency node from the original plan is pruned:
thm-pd-spreading-out, lem-pc-finite-flat-proper-support-descent, and
lem-pc-perfect-complex-descent are all used. The latter two are now reached through
the corresponding new cartesian refinement helper. Their direct proof-only imports
in NoetherianApproximationData were removed because the main proof uses the helpers.
The original AffineTransitionLimit import is retained for scheme spreading out.

Removed the earlier sandbox attempt's unused Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import: the adjunction's left_adjoint_additive theorem directly supplies additivity.
Removed its redundant WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent import
from FilteredCartesianFlatComplexDescent: BaseChangeConventions already exposes the
needed maps through Picard.Defs. Removed the unused Filtered.Basic import from
TensorPullbackFlatProperSupport, along with its unused morphism finite-presentation import.
These were sandbox additions, so no previously
reachable library module is asserted to have left the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan calls the filtered index category directed. The existing two
geometric descent statements in fact accept a preorder, whereas the original item's
signature accepts any small filtered category. The new proved helpers bridge this
mismatch using Mathlib IsFiltered.exists_directed on Under i, whose forgetful functor
is final. They also transport between the given cartesian model and canonical pullbacks.

The perfect-descent result refines the complex's model rather than selecting an
unrelated stage; the explicit comparison triangle makes simultaneous descent possible.
The final differential check uses naturality of the tensor-pullback composition
isomorphism, not merely a degreewise object identification.

The earlier attempt left no node files or report. Its flat refinement did not compile
because the pullback constructor could not synthesize the identity map's isomorphism
instance at that elaboration point. An explicit local IsIso identity instance fixes it.
All mathematical signatures of that attempt were checked before reuse.

Edge cases checked: zero complex (any boundedness interval), zero module (empty proper
support), empty schemes, a one-object filtered category, parallel arrows in a filtered
category, and arbitrary nonflat base transitions. Relative flatness is preserved by a
cartesian square without assuming the transition morphism flat; no empty-index case
is lost because IsFiltered already supplies nonemptiness. No statement is disputed.

The whole-blueprint searches for filtered, flatness, proper support, perfect complex,
and flat complex found no declaration with these cartesian wrapper interfaces. Local
Lean/DAG searches found the existing directed-index results and tensor composition,
which are used. LeanFinder returned only generic finite-presentation/limit facts, not
an exact replacement; LeanSearch returned Internal Server Error and is recorded as
unavailable. Searches are retained in searches.jsonl.

## New nodes

lem-pc-filtered-cartesian-flat-complex-descent: proved conversion of the existing
finite_flat_proper_support_descent to arbitrary small filtered categories and arbitrary
cartesian models. File: Sheaf/AlgebraicGeometry/FilteredCartesianFlatComplexDescent.lean.

lem-pc-filtered-cartesian-perfect-descent: proved conversion of perfect_complex_descends
with a recorded cartesian refinement and comparison triangle. File:
Sheaf/AlgebraicGeometry/FilteredCartesianPerfectDescent.lean.

lem-pc-tensor-pullback-flat-proper-support: the sole new sorry, collecting finite
presentation, relative flatness and proper support under a cartesian base change.
File: Sheaf/AlgebraicGeometry/TensorPullbackFlatProperSupport.lean. Sources: Stacks
01U8, 056J and 0CYS, and the local finite-presentation pullback argument.

The existing item's proof, proof_deps and proof_origin are updated to match the Lean.
No change record is needed: no existing interface is changed and no module is adapted.

## Second reading by K3

1. **Interfaces — pass.** Read all four delivered modules and compared the existing
   NoetherianApproximationData module against the repository with diff. The entire
   declaration from `theorem noetherian_approximation_data` through its conclusion,
   preceding `:= by`, is byte-for-byte identical. Its existing public imports and
   docstring are unchanged; only proof-only imports and the proof changed. The other
   three modules are new, not adaptations. Each new node's `lean.statement` equals
   the corresponding Lean signature verbatim. No definition or target was changed.

2. **Kernel proof and holes — pass as a decomposition.** Independently compiled all
   four modules with `lcompile.py --all`: no errors or warnings. Explicit
   `#print axioms` checks in temporary copies for all four public theorems printed
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Source inspection
   found precisely one local sorry, the entire body of
   `AlgebraicGeometry.tensorPullback_flat_proper_support`; no forbidden declarations,
   no sorry in data, no new definitions, and no arbitrary witness chosen in a data
   definition. The two cartesian wrappers genuinely apply the existing directed-index
   theorems, then construct comparison maps and prove projection and differential
   equations; the upper theorem does not merely rename an unproved approximation
   theorem. One original hole is closed and one smaller hole added, net zero.

3. **New statements and sources — pass, with proof-plan repairs.** Independently read
   the statements of finite_flat_proper_support_descent and perfect_complex_descends.
   Their preorder hypotheses require the wrappers' final directed reindexing; their
   canonical pullback objects require the explicit scheme-isomorphism transport.
   The perfect wrapper additionally gives the actual refinement arrow and triangle
   used to carry Gj to the same final model as Ek. The flat wrapper requires no
   perfect object; the perfect wrapper requires no flat complex. Both are proved.
   The sole open assertion concerns one module in one cartesian square, strictly
   smaller than simultaneous scheme/complex/perfect-object approximation.

   Read Stacks [01BQ](https://stacks.math.columbia.edu/tag/01BQ),
   [01U8](https://stacks.math.columbia.edu/tag/01U8),
   [056J](https://stacks.math.columbia.edu/tag/056J),
   [0CYS](https://stacks.math.columbia.edu/tag/0CYS), and
   [00HT(6)](https://stacks.math.columbia.edu/tag/00HT), as well as
   [0032](https://stacks.math.columbia.edu/tag/0032) and
   [09RF](https://stacks.math.columbia.edu/tag/09RF).
   Local Stacks tex files are absent on this machine, so the primary published
   sources were used. Finite presentation implies the finite-type quasi-coherence
   needed in 01U8/056J/0CYS. Relative flatness needs the cartesian hypothesis, not
   flatness of the transition. The proper-support argument uses the statement of
   closed_subset_proper_over_base_properties, not its internal construction:
   a closed structure on the original support base-changes properly, and its
   inverse-image support is exactly the new support by finiteType_module_support_pullback.
   The repaired flatness explanation identifies affine-section localizations with
   stalks, then invokes the existing affine-sections-flat-over-base Mathlib leaf.

   Small cases checked mathematically: identity and one-object index categories,
   nontrivial parallel arrows (handled by Under i and finality, not a presumed order
   on I), zero terms and empty schemes, and an interval with no nonzero terms.
   For a nonflat base transition, take identity structure morphisms over Spec Z
   and Spec F_p with M=O: the pulled-back module is O on Spec F_p and is relatively
   flat with proper support, although the transition is not flat. This confirms
   that no unmentioned transition-flatness hypothesis is needed. An empty filtered
   index cannot occur because IsFiltered includes nonemptiness.

   Independent searches used different wording through msearch.py LeanFinder for
   relative flat sheaf base change, descent of bounded finitely presented flat
   complexes, and perfect derived object descent with a prescribed model. They
   returned algebraic flatness or scheme-limit facts, no exact replacement.
   Local rg searches found the existing support-pullback theorem and upstream
   isFinitePresentation_pullback for Mathlib's pullback. The latter does not close
   the relative-flatness and proper-support conjunction. No few-minute proof of
   that remaining conjunction was found. All searches are in searches.jsonl or
   recorded here; no duplicate statement was added during this reading.

4. **Route and pruning — pass.** Read dag/units/sk-thm-picard-semicon.json:
   realized.statement is empty and realized.steps is [[]]. The proof keeps the
   original spreading-out, flat-complex-descent and perfect-descent route.
   The old two descent dependency nodes remain transitively used through the
   wrappers; only their direct proof-only imports in the item were removed.
   No old mathematical dependency is claimed pruned. Checked the public imports
   of each new helper against its statement; its geometric descent, preservation,
   composition and directed-reindexing proof dependencies are plain imports.
   The composition isomorphism's naturality gives all differential equations,
   and additive pullback preserves zero objects for the original bounded interval.

5. **DAG agreement — pass after repair.** Read all four delivery node files and
   compared the existing node to the repository: only proof, proof_deps and
   proof_origin changed. The item's four steps match the four proof phases.
   All new nodes have the item/chapter/unit, source, self-contained statement,
   created/blueprint records, recorded searches, and exact Lean statement.
   Dependency lists equal the unions of step uses. The two reindexing steps had
   incorrectly been marked elementary with no dependency despite invoking the
   nontrivial directed-index existence theorem: they now cite
   lem-weil-pbc-filtered-category-exists-directed-final, the existing Mathlib leaf.
   The tensor-property node's flatness step now cites
   lem-pc-affine-sections-flat-over-base and is marked non-elementary.
   Both added citations are existing Mathlib tools; no new node is necessary.

**Changes by this reading:** repaired those three DAG proof-step records and their
proof_deps; expanded the new tensor-property docstring's affine-local flatness
argument using Tag 00HT(6); normalized an extra blank line between its imports.
No Lean statement, proof term, target, existing definition or public interface was
changed. The upper proof and both proved wrappers were retained as written.

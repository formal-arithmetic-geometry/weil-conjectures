## What changed

Reduced `AlgebraicGeometry.Etale.exists_etaleHypercohomology_filtered_resolution_maps`
without changing its signature or visibility. Its proof now uses the new module
`Sheaf.Paper.EtaleHypercohomologyCETotalMaps` for the coherent filtered CE-total
construction, and proves independence of an arbitrary supplied resolution lift in Lean.
The existing node `lem-weil-pbc-filtered-resolution-pullback` records that actual route.

The complete part of the argument does the following:

- Checks the finite-diagonal comparison against the presentation's `w_formula` by
  total-complex extensionality, treating negative resolution-degree summands as zero.
- Obtains quasi-isomorphism of the actual CE augmentation from
  `Functor.cartanEilenberg_augmentation_quasiIso`, with the presentation's `aug_formula`.
- Uses injectivity of precomposition into the target K-injective resolution to identify
  the constructed CE-total comparison with inverse image of the presentation comparison
  followed by the supplied `j`, up to homotopy.
- Constructs the sectionwise inverse-image unit as a chain map and proves its naturality.
  Applying global sections to the homotopy identifies the cohomology map of the CE total
  with that of the presentation's `w` followed by the supplied `w`.
- Cancels the canonical resolution isomorphism in `c_formula` to obtain exactly the
  conjugate of the supplied `HomologicalComplex.homologyMap w n`. Rewrites the
  filtration-inclusion equation with that equality and retains the stable-page equation.

The three private helpers `sections_naturality`, `sectionsUnit` and
`sectionsUnit_naturality` are completely proved/constructed. Repair of the returned
delivery: generalized `sections_naturality` in place from `AddCommGrpCat` to an arbitrary
coefficient category `A : Type (uNatural + 2)` with `Category.{uNatural + 1} A`,
`Abelian A`, `IsGrothendieckAbelian.{uNatural + 1} A` and `HasSmallSiteSheafify A`.
The calculation uses only those categorical hypotheses, and its existing callers
specialize it to `AddCommGrpCat`. Thus this is a genuine coefficient-category
generalization, not a renamed or textually disguised duplicate of the specialized
private helper in `EtaleHypercohomologyPullbackMaps`. That parent cannot be imported
because it imports this item; its private theorem is also unavailable to importers.
No module held by another group is adapted, and no public interface changes.

Both delivered modules compile locally in import order without warnings, using only
`lcompile.py`. The new construction is an existence theorem; no definition chooses
undetermined data from its remaining hole.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_filtered_resolution_maps`
(node `lem-weil-pbc-filtered-resolution-pullback`). Its module contains no `sorry`.

Added hole:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_ce_total_maps`
(node `lem-weil-pbc-ce-total-filtered-maps`), in
`Sheaf.Paper.EtaleHypercohomologyCETotalMaps`. Its proof is exactly `by sorry`.
This is the only `sorry` left in the delivered files.

This is a decomposition: one upper hole closed, one strictly smaller construction hole
added, net zero holes closed. The new statement concerns maps from the inverse image of
the actual CE total, with the finite-diagonal comparison specified on every summand.
It has no arbitrary supplied `j`, `hj`, `w` or `hw`. The passage to every such supplied
lift, including the comparison of the two concrete cohomology maps, is the complete
Lean argument in the original module. The construction and stationary-page comparison
are still work for the next item; they are not claimed proved here. The preexisting
augmentation quasi-isomorphism theorem remains an imported named dependency.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.CartanEilenbergExists`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`

The construction dependencies remain in the new construction module's proof plan.
`CartanEilenbergExists`, `KInjectiveComputes` and `HypercohomologyFirstPage` are also
already reached through the public presentation module. `TopologicalInvariance` is a
public statement dependency of the new module. These are direct-import removals and
relocations, not globally pruned modules. No module is claimed removed from the targets'
import closure. The original node no longer directly uses the CE-existence, first-page,
row-comparison or bounded-filtered-construction nodes; those now belong to the new node.
The K-injective comparison-principle dependency is retained. Added the direct proof
import `Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso`.

The old direct `proof_deps` absent from the new proof are exactly:

- `lem-sp-cartan-eilenberg-exists`
- `thm-sp-if-e1`
- `lem-weil-pbc-sheafH-ext-derived-comparison`
- `prop-weil-pbc-inverse-image-exact`
- `lem-weil-pbc-cartesian-eilenberg-functorial`
- `thm-sp-spectral-object-yields`
- `def-weil-pbc-cohomology-pullback`
- `lem-weil-pbc-cohomology-pullback-functorial`

Inverse-image preservation of quasi-isomorphisms in the reduction uses the proved
`Etale.preservesHomology_upperStar` instance from the upstream `UpperLowerStar.Defs`,
not an application of `upperStar_abelian_exact`. The new construction's plan still
names the inverse-image exactness node. The cohomology-pullback definition also
remains a statement dependency. None of these direct dependency removals is a claim
of pruning a module from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly found a word-for-word duplicate of the parent's private
`sections_naturality`. The repair generalizes the coefficient category in place, as
requested by the return, while retaining the proved naturality calculation. No import
cycle or forced adaptation is introduced. The existing second reading below describes
the previous version and predates this repair; a new independent reading remains due.

The original plan invokes `boundedFilteredComplex_spectralSequence` on the CE-total
filtration. Its hypothesis is `DecreasingFiltration.IsFinite` in the category of whole
complexes: one entire-complex step is top and another is bottom. A bounded-below complex
need not be bounded above, so its CE filtration is only degreewise finite. For example,
a zero-differential complex with a nonzero term in every nonnegative degree has a
nonzero diagonal at arbitrarily high complex degrees; no uniform upper filtration
cutoff kills the whole total. No statement has been changed to assume boundedness above.

The new node and docstring make the missing construction explicit: crop the filtration
at an upper index c to use the uniformly finite theorem; in total degree n take c>n+1.
The crop agrees with the original in degrees n-1,n,n+1 at every filtration index, so
canonical cycle/boundary comparisons identify every page in bidegree (q,n-q). Increasing
c gives identity filtered maps of crops, identified with identity maps on these
quotients. Common crop bounds for the degrees in a differential or structure map, and
for source and target of a filtered map, let the representative comparisons glue.
This gluing and its coherent naturality remain part of the new construction hole.
It is not an application of the finite theorem to an object lacking its hypothesis.

The existing dependency statements do not supply all simultaneous choices in the
original theorem, and do not identify an independently chosen spectral sequence with
the canonical functor's value. The new construction node records that glue rather than
pretending that the existing existence theorems can be applied directly.

Source checked: local Stacks source `derived.tex`, the proof of
`lemma-two-ss-complex-functor` and the following `remark-functorial-ss`; also
`etale-cohomology.tex`, `lemma-colimit-variant-complexes`. The existing node's label
`remark-two-ss-complex-functor` does not occur in that source; Tag 015K's label is
`remark-functorial-ss`, used in the new node. The existing statement and source fields
remain unchanged. The unit `sk-prop-h2` has no realized statement or steps attached to
this auxiliary node; its Kummer route and all unit records remain untouched.

Edge cases: a zero complex and the empty scheme give zero total summands and zero
filtrations, included by the construction. Negative complex-degree bounds are handled
by shifting before CE existence and shifting back. Negative resolution-degree summands
are explicitly eliminated in the Lean proof. No quasi-compactness, properness, torsion,
or dimension hypothesis is introduced. All homotopy cancellation hypotheses are
supplied by the actual augmentation formula and the target resolution's K-injectivity.

## New nodes

`lem-weil-pbc-ce-total-filtered-maps` is the coherent CE-total construction part of
original proof steps 1, 2 and the filtered/stationary portion of steps 3 and 4. It is
strictly separate from independence of an arbitrary lift, which is now proved in the
original module. Its statement specifies the CE-total source, the augmentation homotopy,
the sectionwise formula and the canonical finite-diagonal summand formula; it does not
rename the original universal-resolution-lift conclusion. Its docstring and DAG proof
include the degreewise-finite cropping/gluing argument and presentation-wise bounds.

Searched the whole blueprint for `filtered resolution`, `Cartan Eilenberg`, and
`hypercohomology`, and searched the Lean library and existing nodes. The existing
first-page theorem, exact-couple statements and convergence inputs are ingredients,
not this coherent total-map family. Targeted Mathlib LeanFinder returned total-complex
component identities and a Dold--Kan eventual-constancy lemma; grep returned no match.
LeanSearch returned Internal Server Error and is recorded as unavailable. No change
record is needed: existing statements, definitions and public imports are unchanged.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Read the complete diff against the repository module.
   Independently compared the existing theorem's signature from its declaration name
   to `:= by`: byte-identical. Its docstring, public import, namespace and visibility
   are unchanged. The only new definition is the private, concrete `sectionsUnit`;
   its components are the existing sectionwise unit, with its chain-map proof supplied
   by the proved named naturality theorem. No public definition changes and no
   undetermined witness is chosen in a definition. Existing-node changes are confined
   to `proof`, `proof_deps` and `proof_origin`; no change record is needed.

2. **Lean proof and axioms: pass as a decomposition.** Compiled both delivery modules
   with `lcompile.py --all` in import order, without errors or warnings (9.1 s and
   26.5 s in the recorded run). Searched the delivered sources: zero holes in the item,
   exactly one in the new named construction theorem, and no forbidden declarations
   or compiler escape hatches. Scratch copies with explicit `#print axioms` compiled:
   `sections_naturality`, `sectionsUnit`, and `sectionsUnit_naturality` use only
   `propext`, `Classical.choice`, `Quot.sound`; the two public existence theorems use
   those and `sorryAx`. The reduction really verifies the diagonal comparison,
   cancels the quasi-isomorphic augmentation in the homotopy category, applies
   naturality of the concrete sectionwise unit, and cancels the resolution isomorphism.
   No claim of an axiom-free target or positive net hole reduction is made.

3. **Split-off statement: pass.** Read the new statement, its complete docstring proof,
   and its node against Stacks `derived.tex`, lemma-two-ss-complex-functor and
   remark-functorial-ss, in the local source checkout. The remaining statement supplies
   the filtered CE-total construction, without any universally supplied resolution
   lift. The original module proves the additional independence/comparison argument;
   this is a genuine strict part of the argument, not a renamed application of the
   original statement. Checked zero complexes, empty schemes, total degrees below
   the source bound, shifted negative bounds, and negative resolution summands.
   Cropping requires a common bound above the adjacent cochain degrees, and gluing
   uses the canonical cycle/boundary comparisons; that work is explicitly still open.
   Independent LeanFinder search for stationary-page naturality, Loogle search for
   spectral-sequence morphisms, and grep for associated graded homology/convergence
   supplied no exact construction. Reviewed the local degreewise stable quotient,
   CE second filtration, mapped-total comparison and comparison-independence results:
   they provide ingredients, not this simultaneous family and its concrete formulas.
   The remaining construction cannot be closed in a few minutes by those results.

4. **Route, imports and pruning: pass.** Read the presentation, augmentation
   quasi-isomorphism, K-injective comparison principle and mapped-total declarations.
   The existing proved K-injective principle is used directly. The sectionwise
   naturality calculation in the parent cannot be imported without a cycle.
   The existing module's three proof imports support the reduction; the new module's
   public imports support its statement, and its plain imports name construction
   ingredients. Added an exhaustive list of all eight old proof-dependency IDs no
   longer directly used, distinguishing upstream exactness instances from the unused
   wrapper theorem. No module is claimed globally pruned. Read
   `dag/units/sk-prop-h2.json`: its realized statement and step lists are empty for
   this auxiliary result; the fixed Kummer route and unit records are unchanged.

5. **DAG consistency: pass.** Independently normalized whitespace and compared both
   nodes' `lean.statement` with their actual theorem signatures; they match. Verified
   that each `proof_deps` is exactly the union of its proof steps' `uses`. The original
   node describes the actual reduction and its augmentation dependency. The new node
   has the required source, creation, blueprint ancestry, chapter/unit, search and
   Lean records, and describes the outstanding coherent construction. Its proof
   explicitly distinguishes degreewise finiteness from whole-complex finiteness.

Second reading changed only the report (complete removed-node list and this review)
plus the new node's successful Loogle search record. No Lean proof, statement,
definition or import needed repair. One upper hole closed and one construction hole
added: decomposition, net zero; globally pruned modules: none.

## Second reading by K2

1. **Interfaces:** pass. I compared both delivered modules with the repository versions. The existing theorem signature and visibility are byte-for-byte unchanged; the only added declaration is the new public construction theorem, whose statement is recorded verbatim in its new DAG node. The generalized `sections_naturality` helper is private and changes no public interface. No definition selects data from an undetermined existence proof.

2. **Proof and axioms:** pass as a decomposition. Both modules compile with `lcompile.py --all` without errors or warnings. The filtered-resolution theorem has no `sorry`; the CE-total construction theorem is the single named split-off hole and has its required source, proof docstring, and node. No forbidden declarations occur. The completed proof uses only ordinary categorical and homological arguments; its remaining imported open theorem contributes the expected `sorryAx` until that dependency is proved.

3. **Statements:** pass. The split-off CE-total statement is a strict construction subproblem: it supplies coherent CE presentations, filtered maps, stationary-page comparisons, and concrete formulas, while omitting the arbitrary supplied resolution lift that the parent theorem handles. Its degreewise-finite filtration is handled by explicit cropping and gluing in the docstring rather than by falsely applying a uniformly finite theorem. Zero complexes, empty schemes, negative indices, and empty diagonal summands are covered by the stated constructions. No duplicate library theorem was found in the recorded searches.

4. **Route and pruning:** pass. The parent proof follows the new CE-total construction, checks the finite-diagonal formula, uses the augmentation quasi-isomorphism and K-injective comparison principle, proves the sectionwise unit naturality, and derives the required cohomology and filtration equations. Removed direct imports and obsolete proof dependencies are listed in `## No longer needed`; the remaining imports are used by statements or proofs. No target-closure module is claimed pruned, and the unit route is unchanged.

5. **DAG consistency:** pass. The existing node records the actual reduced proof and its updated dependency union. The new node's Lean declaration, statement, source, proof steps, dependency union, origin, searches, chapter, unit, and creation metadata agree with the delivered file. The unit's realized route is untouched.

I changed only this second-reading section; no Lean proof, statement, definition, import, or DAG node required repair.

## What changed

Reduced `AlgebraicGeometry.singleComplexStalkCondition_open` without changing its signature.
The item now imports `Sheaf.AlgebraicGeometry.SingleComplexOpenStalkConjugacy` for its proof.
The new module isolates the pointwise commuting square of additive stalk-comparison arrows.
It assumes no original stalk condition or invertibility: it supplies source and target
isomorphisms and the compatibility equation, even for noninvertible comparisons.
The item chooses original coordinates using the existing `nonempty_coordinates`, unfolds
the restricted condition, and proves it for every restricted coordinate presentation,
point and degree. It transfers the given invertibility through the arrow isomorphism,
then uses reflection of isomorphisms by the module-to-abelian-group forgetful functor.
The existing item node and the new conjugacy node record this route. This is a decomposition, not a sorry-free
proof of the underlying open-transport calculation.

## Proved and sorry left

Closed the item hole in `AlgebraicGeometry.singleComplexStalkCondition_open`
(node `lem-pc-single-complex-open-stalk-condition`): its entire proof is Lean with no sorry.
Added one strictly intermediate hole:
`AlgebraicGeometry.SingleComplexBaseChange.nonempty_stalkComparison_open_arrow_iso`
(node `lem-pc-single-complex-open-stalk-conjugacy`). Its whole proof is `by sorry`,
with a source and a complete proof in words in its docstring and node.
No other holes were added, and no sorry remains in the item's module.
One upper hole closed, one lower hole added; net hole reduction is zero.

The lower statement concerns one point and one degree and supplies an actual
commuting square with invertible vertical maps; its hypotheses contain neither
`StalkCondition` nor any comparison-invertibility hypothesis. The item proves the
separate implication from this naturality information to universal invertibility.
For the empty open the point quantifier is empty. The top open, zero complexes,
zero rings, and arbitrary unbounded representatives impose no extra hypotheses.

## No longer needed

No existing import was removed: the original public import is required by the signature.
No module is claimed to have left the targets' actual import closure.
The planned dependency `lem-pc-stalk-comparison-coordinate-invariance`
(`Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance`) is not needed as a
separate isIso theorem: the pending conjugacy uses the stronger source-transport
and pullback-naturality statements to construct its square for arbitrary coordinates.

The other old planned dependencies are no longer direct proof dependencies of the item:
`lem-pc-kflat-open-restriction` / `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`,
`lem-pc-open-restriction-stalk-extension-iso` /
`Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso`,
`lem-pc-affine-derived-pullback-tensor-tilde` /
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`lem-pc-ringed-spaces-derived-pullback-composition` /
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
`lem-weil-pbc-module-stalk-pullback` /
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`, and
`def-pc-base-derived-tensor-cohomology-model` /
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
These remain needed by the new conjugacy node's proof plan; they are not globally pruned.
`def-pc-single-complex-base-change-stalk-condition` remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The listed restriction and composition declarations do not by themselves state the
cross-square naturality equation for the localized tensor-cohomology comparison.
The missing step is now exposed as the additive-arrow conjugacy theorem, rather
than using an invertibility hypothesis to disguise this gap.
The existing coordinate-invariance theorem only gives an isIso equivalence;
its stronger source-transport and pullback-naturality dependencies supply the
commuting-square information needed by the pending proof.
No statement or definition was changed. The unit realization record has no bound
statement or proof-step nodes; this decomposition stays below the unit level.
The Stacks sources read were Tags 0DJ8 (locality paragraph) and 0DJ9
(source-open induction paragraph). LeanSearch returned an Internal Server Error;
LeanFinder supplied only underived restriction/stalk maps, and grep found no
matching comparison transport. The new node records these actual searches.

## New nodes

`lem-pc-single-complex-open-stalk-conjugacy`, in
`dag/nodes/sec-picard-framework/lem-pc-single-complex-open-stalk-conjugacy.json`,
is the pointwise source-open conjugacy of the original and restricted comparison
arrows after forgetting scalars. Its Lean module is
`Sheaf.AlgebraicGeometry.SingleComplexOpenStalkConjugacy`.
Its proof plan explicitly constructs restricted coordinates, identifies local rings
and stalk complexes, and composes the resulting square with coordinate transport.
The blueprint search found no matching node. No change record is required:
all existing signatures, visibility and public imports are unchanged.

## Second reading by P1

1. **Interface: pass.** Compared the delivered item with its repository version by
   diff and checked its signature byte for byte. Only the proof and one plain
   proof import changed. No existing definition, public import, visibility,
   hypothesis or conclusion changed; no change record is needed.
2. **Kernel and holes: pass as a decomposition.** Both delivered modules compile
   locally through lcompile.py without warnings. Scratch copies with `#print axioms`
   show exactly propext, Classical.choice, Quot.sound and sorryAx for both public
   theorems. There are no forbidden declarations or hollow definitions. The only
   delivered sorry is the whole proof of the documented public conjugacy theorem.
   The choices in the item are local to a proposition proof, not definitions of
   arbitrary library data. The upper theorem still depends on the lower hole and
   is not claimed to meet the sorry-free target criterion.
3. **Split statement: pass.** Read Coordinates, stalkComparison, the derived
   composition specification, source transport and pullback naturality. The new
   statement is the pointwise transport square for arbitrary coefficients; it
   assumes no StalkCondition or comparison invertibility. It therefore isolates
   the geometric comparison calculation from the separate invertibility argument,
   rather than renaming the item. Its docstring and node describe restriction of
   representatives, transport of the actual stalk ring actions and counits, and
   coordinate transport. Empty opens have no points; top opens use the same stalk
   identifications; zero complexes and zero rings add no condition. Unbounded
   complexes are handled by exact restriction and K-flat derived functoriality.
   Verified the locality and source-open paragraphs in Stacks Tags
   [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and
   [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9). Independent LeanFinder, Loogle,
   Mathlib grep and rg of Sheaf and upstream WeilConjectures found no duplicate.
   The existing coordinate invariance concerns one fixed square, and target-open
   restriction concerns simultaneous base opens; neither supplies this square.
   Closing the remaining geometric transport calculation is not a short repair.
4. **Route and pruning: pass.** The item uses preservation of isomorphisms,
   Arrow.isIso_iff_isIso_of_isIso and reflection by forgetful functors to derive
   the condition directly from the pending square. The existing public import is
   needed for its statement, and the new plain import is needed for its proof;
   both public imports of the new module are needed by its statement. The report
   accounts for every old proof dependency absent from the new direct route and
   makes no claim of global pruning. The unit sk-thm-picard-semicon has empty
   realized statement and proof-step bindings; no bound unit route is bypassed.
5. **DAG: pass.** Checked each Lean statement against its node's verbatim record,
   and checked proof_deps equals the union of the proof steps' uses. The existing
   node changes only proof, proof_deps and proof_origin. The new node has its
   source, proof in words, searches, creation record, blueprint origin, chapter,
   unit and Lean attachment. Its planned dependencies supply the restriction and
   coordinate-transport ingredients described in the docstring.

Second-reading changes: corrected the report's ambiguous reference to two node
copies, recorded the independent duplicate searches in the new node, and appended
this review. No Lean proof or statement repair was necessary. Holes closed and
added remain exactly those listed above: one upper hole closed, one intermediate
hole added, net zero; no module globally pruned.

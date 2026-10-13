## What changed

Replaced the proof of AlgebraicGeometry.singleComplexOpenComparison_affine without
changing its signature, visibility, or the definition of the comparison. The proof
constructs the restricted cartesian square by pullback pasting, proves that its
source schemes are affine, and uses derivedPullback_tensor_preserve_QCoh for the
restricted coefficient objects. It then transports the stalk condition to the
restricted square, constructs the spectrum pullback using the four isoSpec maps and
isoSpec_hom_naturality, then obtains coefficient coordinates with a commuting comparison
square, applies the existing singleComplexAffineBaseChange, and transports that
isomorphism back using functoriality and the endpoint isomorphisms.

Added two proof imports and their new modules:
Sheaf.AlgebraicGeometry.SingleComplexOpenStalkCondition and
Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates. Also imported
Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh for preservation of quasi-coherent
cohomology. The original affine criterion import is still needed. The second reader removed
two redundant public Mathlib imports from the new modules and imports
Mathlib.AlgebraicGeometry.Morphisms.Affine only in the item, without public,
for IsAffine.of_isPullback.

Updated the item's proof, proof_deps and proof_origin to describe this Lean route.
All existing statements and definitions are unchanged. The new existential
coordinate data are eliminated only inside a proposition proof; no definition or
object construction chooses data from an unproved mere-existence theorem.

## Proved and sorry left

Closed the upper hole AlgebraicGeometry.singleComplexOpenComparison_affine
(lem-pc-single-complex-open-affine). No sorry remains in the item's module.

Added exactly two holes, each in its own public theorem and module:

- AlgebraicGeometry.singleComplexStalkCondition_open
  (lem-pc-single-complex-open-stalk-condition).
- AlgebraicGeometry.exists_singleComplexAffineSpectrumCoordinates
  (lem-pc-single-complex-affine-spectrum-coordinates).

This is a decomposition of one upper hole into two coordinate-transport steps,
not a completed proof with only the three allowed axioms. The net hole change
from this delivery is one closed minus two added, namely -1, before any change
in the target import closure. The affine base-change argument itself is reused
from its existing declaration. Neither new theorem asserts the item's conclusion:
the first only preserves a stalk hypothesis, and the second only provides spectrum
coordinates and a commuting equation. Invertibility follows in the item's Lean
proof from the existing affine criterion, followed by preservation and composition
of isomorphisms.

Each new statement was checked mathematically for the empty and top open, the zero
ring/empty affine scheme, arbitrary nonflat arrows, unbounded coefficients and
arbitrary derived-category localization choices. The restriction lemma has no
quasi-coherence or affineness assumption; the coordinate lemma concerns a fully
affine square and does not claim base change invertible. The same canonical
composition comparisons used in the item's definition occur in the restriction
statement.

## No longer needed

None of the original imports or proof dependencies are pruned. The existing
singleComplexAffineBaseChange criterion remains necessary. No unit statement or
unit proof step is bypassed; the item's unit realized lists are empty, and this
refines the same affine-open step of its existing route. A direct Mathlib affine
import tried during development was removed because the new spectrum-coordinate
module initially supplied it. The second reader removed that redundant public
import and placed the needed affine-pullback lemma import in the item as a plain
proof import. Also removed the redundant public Mathlib.AlgebraicGeometry.Limits
import from SingleComplexOpenStalkCondition; its signature elaborates through
the existing public dependency. These are import cleanups within new modules,
not pruning of original proof dependencies or previously reachable modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original node combined two substantial
transport arguments into one paragraph without declarations that state them:
restriction of the canonical stalk condition and comparison naturality under the
four affine spectrum isomorphisms. The two new nodes make these obligations
explicit, while the existing affine criterion and quasi-coherence preservation
provide the other parts of the argument.

The literal source path literature/stacks-project/perfect.tex is absent in this
read-only clone. Read the stated source directly at the official Stacks Project
pages for Tags 0DJ8 and 0DJ9. Their proofs explicitly use locality on X' and the
affine spectrum reduction. Canonical transport details are marked as an agent
expansion rather than claimed verbatim from the source.

The previous attempt was blocked by the missing shared-cache artifact
SingleComplexOpenComparison.olean. The artifact is now published. On resumption,
all three delivered modules compiled through lcompile.py --all without errors or
warnings (2.9 s, 14.5 s and 10.4 s). The saved reduction therefore checks against
the original comparison definition itself; the scratch expression is no longer
needed for validation. Corrected doubled TeX backslashes in both new node
statements; their mathematical content and Lean signatures are unchanged.

The required deliver3.py --no-push dry run printed OK: all delivered modules
compile and preflight passes except for the second reading, which the second
reader writes. Nothing was pushed.

## New nodes

lem-pc-single-complex-open-stalk-condition: restriction of the stalk hypothesis to
an arbitrary source open and its cartesian inverse image, with the precise
coefficient map from the canonical composition comparisons. Its next worker must
prove the tensor-stalk compatibility and apply the existing coordinate-invariance
theorem to pass to arbitrary restricted presentations.

lem-pc-single-complex-affine-spectrum-coordinates: transport of an affine square to
the spectra of its global-section rings, for the explicitly constructed coordinate square, including quasi-coherent coefficients,
equivalence of stalk conditions, endpoint isomorphisms and the commuting equation
for the actual comparison. Its next worker must prove coordinate naturality;
it does not include the affine base-change criterion itself.

No change record is required: no existing signature, visibility or definition was
changed, and no other group's module was adapted.

## Second reading by C1

1. Interface: PASS. Compared the delivered SingleComplexOpenAffine module with
   the repository using diff. The sole existing theorem's signature is byte for
   byte identical, including the derived-category instance family, arbitrary
   cartesian square, affine bases, both quasi-coherence hypotheses, the given
   coefficient map, its stalk hypothesis, the affine source open and the exact
   singleComplexOpenComparison conclusion. Its docstring and visibility are
   unchanged. No definitions or other existing modules are changed; no change
   record or forced adaptation is needed.
2. Proof and trust: PASS as a decomposition. All three modules compiled through
   lcompile.py. The item constructs sqU by pullback pasting; affineness of the
   inverse image uses the affine morphism g between affine bases, not affineness
   of X. The change tactic checks the actual comparison definition, including
   the direction of the pullback-condition equality and both composition maps.
   The four isoSpec naturality equations give sq0 in the order required by the
   affine criterion. hstalk.mp supplies exactly its stalk hypothesis. hb0 installs
   the isomorphism instance needed after rewriting hcomp; the final composition
   consists of two endpoint isomorphisms and a functor image of an isomorphism.
   Scratch #print axioms checks for all three delivered declarations gave only
   propext, Classical.choice, Quot.sound and sorryAx. There are precisely the two
   reported public theorem sorries and no sorry in the item's proof or a
   definition; no axiom, unsafe, opaque, extern or implemented_by declaration.
   The existential coefficient coordinates are eliminated in a Prop proof only,
   never chosen to define a data object from an unproved existence statement.
3. New statements: PASS. Read the actual sources at
   https://stacks.math.columbia.edu/tag/0DJ8 and
   https://stacks.math.columbia.edu/tag/0DJ9, and opened both new Lean statements
   and nodes. These are explicitly marked agent expansions of the locality and
   affine-coordinate passages, not quotations from Stacks. The restriction
   lemma fixes the bases and restricts only the two source schemes. The two
   projections give open restriction, exact on modules and K-flat complexes;
   the specified phiU is the composition transport of phi. Local-ring maps,
   tensor-stalk identification and the represents equation conjugate the
   cohomology comparison; the existing coordinate-invariance theorem then
   handles the universal quantifier over presentations. Its cited affine tilde
   node includes a general open-restriction clause (1), so no affine hypothesis
   is silently used here. The spectrum lemma assumes all four schemes affine
   and provides coordinate coefficients, quasi-coherence, equivalence of stalk
   conditions, endpoint isomorphisms and an equation for the given comparison.
   Canonical spectrum isomorphisms, their inverse pullbacks, and adjoint mates
   give those data; composition coherence pins the equation to the actual
   counit construction. Neither lemma concludes that a base-change arrow is
   invertible. Checked empty and top opens, empty spectra/zero rings, zero
   coefficients, arbitrary nonflat maps and unbounded complexes: restriction
   or an equivalence suffices in each case and adds no hypothesis. Both holes
   are substantial transport obligations, not something to close with a quick
   tactic or a renamed copy of the item.
   Independent searches used LeanFinder with "canonical derived base change
   comparison naturality under isomorphisms of schemes", Loogle with
   AlgebraicGeometry.Scheme.toSpecΓ, and grep with
   "stalk.*restrict|restrict.*stalk" through msearch.py. Results provide ordinary
   module pullback composition, spectrum naturality and underived restriction
   stalk isomorphisms, not either new theorem. Also searched both library roots
   and the upstream AlgebraicGeometry sources. Opened the existing
   DerivedBaseChangeBaseCoordinates, DerivedBaseChangeTopIso,
   StalkComparisonSourceTransport and CanonicalModuleBaseChangeIsoComparison:
   these concern fewer vertices, changes of representatives on a fixed scheme,
   or a module in degree zero, and none supplies the unbounded coefficient and
   stalk-condition transport needed here. SingleComplexBaseChangeCriterion
   depends on this induction and has different coefficient hypotheses, so it
   is not an alternative route.
4. Route and pruning: PASS after import repair. The proof reuses
   singleComplexAffineBaseChange, the only old proof dependency, and uses
   derivedPullback_tensor_preserve_QCoh rather than splitting off preservation.
   No original dependency is unused. The unit sk-thm-picard-semicon has empty
   realized.statement and realized.steps entries; these are unchanged. The
   source-open affine step within the existing induction is kept. Removed the
   new spectrum module's redundant public Morphisms.Affine import and the new
   restriction module's redundant public Limits import. Compiling each new
   signature without these imports succeeds. Compiling the item afterward
   exposed its actual proof-only need for IsAffine.of_isPullback, so added
   plain import Mathlib.AlgebraicGeometry.Morphisms.Affine there. No proof-only
   import is exposed publicly by this delivery.
5. DAG: PASS. Compared the existing item node against the repository: only
   proof, proof_deps and proof_origin differ. Its four steps match sqU and
   affineness, quasi-coherence and stalk restriction, sq0 and spectrum
   coordinates, and the existing affine criterion with isomorphism transport.
   For all three nodes proof_deps is exactly the union of step uses. Both new
   nodes have the required source, created, blueprint provenance, chapter,
   unit and Lean metadata; their recorded Lean signatures are verbatim the
   actual theorem signatures. Read the cited dependency statements, including
   the general restriction clause of AffineDerivedPullbackTensorTilde and the
   scalar-compatible restriction stalk isomorphism. The new node docstrings
   give the construction and comparison argument for the remaining workers.

Changed only the three import lines described in point 4 and this report.
No additional hole was closed or introduced during the second reading. The
result remains one upper hole closed by reduction, two lower holes added,
and net -1 holes before import-closure effects; it is not a sorry-free proof.

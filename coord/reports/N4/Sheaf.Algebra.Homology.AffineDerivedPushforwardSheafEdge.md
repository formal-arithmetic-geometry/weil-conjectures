## What changed

Repair C4: added a DAG node for the existing proved acyclicity criterion and
added it immediately after `def-sp-acyclic` in both parent proof step 1 uses and
proof_deps. No Lean file, declaration, import, signature, or sorry changed.

Replaced the sorry in `AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge`
with a proof from affine higher-image vanishing, the existing unbounded
quasi-coherent cohomology comparison, and a new generic bottom-unit normalization
lemma. No existing signature, definition, or visibility changes.

The proof shows that the actual derived lower-truncation projection is invertible
in degree i on D_QCoh, using naturality of the existing affine cohomology comparison.
It composes its inverse with the normalized bottom comparison to construct the
edge. Applying the bottom-unit equation to the homology data mapped by F and by
F followed by direct image, then cancelling the exact cycle quotient, proves the
specified formula. Left exactness of direct image is proved by reflecting finite
limits through module-sheaf forgetful functors. Integer higher-image vanishing is
proved using a private, fully proved Čech dimension-shifting helper and the
unbounded/natural-degree comparison. This helper imports the lower-level exactness,
flasque, Čech and acyclicity APIs; it adds no hole.

Added `Sheaf.CategoryTheory.Abelian.DerivedBottomUnitNormalization`, one public
statement with its sourced proof in words. Updated the parent's proof route and
proof dependencies. Direct image is locally marked irreducible during this proof, with explicit
unfolding only in the finite-limit and ordinary-higher-image comparisons. This
avoids repeatedly unfolding its concrete sheaf implementation in the final
homological algebra calculation; the underlying definition and all interfaces
are unchanged. The final assigned file compiles in 55.4 seconds under the existing
60-second limit. Files under scratchpad are compiler experiments only and are
not delivered.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge`
(lem-pc-affine-derived-pushforward-sheaf-edge).

Added one hole:
`CategoryTheory.Functor.exists_rightDerivedFunctor_truncated_bottom_unit`
(lem-pc-derived-bottom-unit-normalization).
Its proof is exactly `:= by sorry` in its own new module. The assigned module has
no remaining sorry. This is a decomposition, not a net reduction in holes:
one hole closed, one strictly smaller generic argument split off.
The new private lemma `AlgebraicGeometry.affineDirectImage_rightAcyclic` is fully proved. The new theorem
only normalizes the bottom comparison after lower truncation; it does not establish
affine vanishing, invert derived lower truncation, construct the full affine edge,
or prove compatibility with exact functors F. All those remaining steps are Lean
in the assigned module. Existing dependencies may still rest on sorry.

Edge cases checked mathematically: for S the identity, delta is the inverse of the
homology map of the truncation projection and the formula is the usual cycle-class
quotient; for a zero functor or zero complex all maps are zero; shifts give the same
calculation for every integer, including negative degrees. An arbitrary left exact
S need not invert the derived truncation projection, and the new statement does not
claim that. For the identity affine morphism on a nonzero ring and a complex in
degree zero, the normalized edge is nonzero: the old zero witness cannot satisfy
this normalization. The proof makes no nonzero-ring or boundedness assumption.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence`
and node lem-pc-affine-derived-pushforward-sheaf-edge-existence. Its zero witness
provides none of the normalization required here.

Removed proof import `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility`
and node lem-pc-affine-derived-pushforward-sheaf-edge-compatibility. Its cancellation
argument is performed directly on the normalized bottom-unit equation, so no
intermediate normalized affine-edge hypothesis or compatibility theorem is needed.

Avoided proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`
and dependency lem-pc-affine-morphism-hi: that module currently has a transitive
import cycle back to this item. Its affine-acyclicity argument is proved inline
from the smaller closed source APIs. It is replaced in the DAG by the affine Čech
complex, section lifting, and generic acyclicity tools, so a dependency-import
regeneration will not restore the cyclic import.

The original dependency def-pc-ringed-spaces-derived-direct-image remains
needed for the direct-image construction and its exposed unit. The original
substantive dependency lem-sc-qcoh-acyclic-derived-pushforward-cohomology is retained. No unit statement or
realized step is bypassed (sk-thm-picard-semicon has no realization by this node).
No further module is claimed to become globally unreachable: other callers may
still need the removed modules.

## Where the brief, the DAG or earlier work was wrong

Repair C4: `def-sp-acyclic` defines acyclicity but does not state the
dimension-shifting criterion used in proof step 1. The added existing-theorem
node now explicitly records that substantive dependency.

The earlier decomposition provided existence of an arbitrary transformation by zero,
then asserted compatibility for arbitrary transformations. That universal assertion
was corrected by G4 to require cycle normalization. The parent was correctly
reopened, but the retained zero-existence import cannot fill the new premise. This
delivery constructs a normalized edge instead of applying the stale universal lemma.

The local compiled compatibility module initially still exposed the old arbitrary-edge
signature and rested on sorry, despite the corrected repository source. The delivery
avoids that cache discrepancy by writing the short cancellation argument inline.

The first dry run also found an import cycle through the current source
AffineMorphism module's import of DirectImage.FiniteFreeComplex. Its finite-complex
chain eventually reaches this assigned edge. Import-direction checks accepted all
replacement lower-level source modules. The private affine-acyclicity proof is the
source's existing Čech/dimension-shifting argument, with no statement change or
forced adaptation.

The second dry run compiled the delivered set and completed its axiom checks,
but the static interface scanner requested a change record for the local attribute.
The record explains its local scope and lists all transitive importers and their
holders. It makes no claim that an external definition or interface changes.

No new statement weakens or changes the parent. The new bottom lemma is a
unit-normalized refinement of the existing proved bottom comparison, not a renamed
version of the parent's existential assertion. Its source pages (Stacks Tags 05TC,
08D4, and 0AVW) were read online. Search used LeanFinder and Loogle, Mathlib and both
project roots, and blueprint search; LeanSearch returned Internal Server Error and
is recorded as unavailable rather than as a negative result.

## New nodes

lem-pc-right-acyclic-of-epi-map-g: records the existing theorem
`CategoryTheory.Functor.rightAcyclic_of_epi_map_g` in
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (line 329),
including both abelian categories, injective resolutions in C, additivity and
left exactness, all three property hypotheses, and the acyclicity conclusion.
Source and search records are attached. This adds no Lean declaration or hole.

lem-pc-derived-bottom-unit-normalization: generic left exact bottom comparison with
its actual right-derived-unit formula on arbitrary left homology data. The natural
isomorphism is constructed by double truncation, the single-object comparison, and
the inverse degree-zero unit. The remaining formula tracks cycle classes through
those maps. This is needed before composing with the affine derived truncation
inverse. Its module is
`lean/Sheaf/CategoryTheory/Abelian/DerivedBottomUnitNormalization.lean`.
The change record is
`coord/changes/AffineDerivedPushforwardSheafEdgeProofTransparency.md`; it documents
the proof-local irreducibility attribute requested by the lexical interface check.
No definition, signature, or exported attribute changes, and there are no forced
adaptations.

## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Independently diffed the delivered parent against the repository
   and compared its complete declaration header byte for byte through `:= by`.
   The rings, ring map, arbitrary integer, natural transformation on D_QCoh,
   exactness assumptions on F and direct image composed with F, quasi-coherent
   values, complex, membership proof, and actual right-derived-unit equality are
   unchanged. Existing node changes are exactly `proof`, `proof_deps`, and
   `proof_origin`. The only transparency directive is local; no definition or
   exported attribute changes. No arbitrary witness is used to define data.
2. Proof: PASS as a decomposition. Compiled both modules locally in import order:
   bottom normalization 1.7 seconds, parent 46.4 seconds, without warnings or
   errors. Independently printed axioms in an importing scratch module: the parent
   uses only propext, Classical.choice, Quot.sound and sorryAx; the new open lemma
   uses sorryAx. There is exactly one delivered sorry, in the named public bottom
   normalization theorem, and no forbidden declaration or hollow definition.
   Read the fully proved private Cech helper against the source AffineMorphism
   argument. Read the transfer of invertibility through the natural comparison
   and the final epi/mono cancellations; neither uses normalization of an
   arbitrarily selected comparison isomorphism.
3. Split statement: PASS. The new theorem handles additive left exact S, every
   integer n, and arbitrary left homology data related by the cycle inclusion.
   Left exactness identifies cycle kernels; the quotient of those cycles maps
   canonically to derived bottom cohomology after lower truncation. The
   single-object degree-zero unit is invertible, giving the specified inverse
   comparison and its cycle equation. Checked identity S, zero S, zero K, and a
   non-exact left exact S: exactness of S is not required, because the formula
   starts from S applied to cycles rather than asserting H(S K) = S(H K).
   No claim that RS inverts the original truncation is hidden in this statement.
   It is strictly the bottom-comparison and unit-calculation part of the parent;
   affine vanishing, QCoh truncation and derived-map invertibility are separate
   proved steps. Its docstring gives the construction and cycle calculation,
   source and matching node. Re-read Stacks Tags 05TC and 08D4 and searched with
   LeanFinder for canonical resolution-unit/cycle-quotient comparison, Loogle
   for toRightDerivedZero, and rg for truncation/unit and bottom comparison.
   Results give the existing unnormalized bottom isomorphism and degree-zero
   cycle identities, not the new equation. Completing the normalization requires
   tracing double truncation and bounded-below compatibility, not a short direct
   application of those search results; the hole remains explicitly reported.
4. Route and pruning: PASS. The parent first proves affine acyclicity from the
   smaller source APIs, then uses the existing QCoh comparison to invert the
   actual derived truncation map, and uses the normalized bottom lemma only
   for the cycle calculation. All added parent proof imports have roles in
   these steps and are plain imports. The new lemma's public imports provide
   its signature; its plain bottom-comparison import records the construction
   used in its pending proof plan. The old proof-dependency list has three
   entries: derived direct image and QCoh comparison remain used; affine
   higher-image vanishing's cyclic source module is replaced and explicitly
   listed above. Both removed parent imports are listed above as well.
   No additional globally unreachable module is asserted. Opened the unit
   sk-thm-picard-semicon: its realized statement and step lists are empty;
   no realized unit node is bypassed or modified.
5. DAG: PASS. Matched the parent's three steps to its finite-limit/acyclicity
   argument, naturality-based invertibility argument, and normalized-cycle
   cancellation. Its proof_deps are the union of those steps' uses. The new
   node has its source, complete statement, proof plan, search records,
   ancestry, chapter/unit, creation metadata and verbatim Lean signature.
   Its dependencies describe the existing bottom construction, single-object
   comparison and bounded-below/unbounded compatibility. No other node field
   or unit realization is changed.

Second-reading changes: appended this independent review and generated scratch
compile/axiom evidence. No Lean, node, signature, definition, or import repair
was needed. Accounting remains one original hole closed and one strictly smaller
hole added: decomposition, with zero net holes closed.

## Second reading by N4

1. Interface — PASS. Diffed the parent against the repository and independently
   compared the complete existing theorem header byte for byte through `:= by`:
   identical. Its public imports, visibility and existing docstring are unchanged.
   The extra helper is private; the irreducibility attribute is local and has a
   change record. There are no new definitions or choices of arbitrary data.
2. Proof — PASS as a decomposition. Independently compiled both delivered modules
   in import order, without errors or warnings (1.6 and 50.5 seconds). There is
   exactly one delivered sorry, the complete proof of the named bottom-unit
   theorem; no forbidden declaration or hollow definition occurs. Read the
   private affine acyclicity helper against the source AffineMorphism proof,
   the naturality argument transferring invertibility of the truncation map,
   and the final epi/mono cancellation. The unnormalized QCoh isomorphism is
   used only to transfer invertibility, never to assert unit normalization.
3. Split statement — PASS. Re-read Stacks 05TC, 08D4 and 0AVW and the existing
   bottom comparison construction. Checked zero complex, zero functor, identity
   functor, a single object in any integer degree, and a non-exact left exact
   functor: preservation of cycle kernels is sufficient, and no preservation
   of the boundary quotient by S is assumed. The equation uses S of cycles,
   not an asserted isomorphism H(S K) = S(H K). The lower-truncated derived
   object is bounded below; the upper-truncation triangle and degree-zero
   left-exact unit give its bottom comparison. The specified cycle equation
   is the natural augmentation calculation. This is a proper part of the
   parent, excluding affine vanishing and removal of the negative tail.
   Its docstring, source and node supply the construction and complete proof
   plan. Fresh LeanFinder search for canonical cycle-to-derived maps after
   smart lower truncation found generic homology/resolution APIs only; Loogle
   did not recognize the project homology-data identifier. Independent rg
   searches found RightDerivedSingleZeroUnit, RightDerivedUnitSingleDegree and
   LeftExactUpperTruncationComparison. Their statements cover single objects
   or upper truncation, not this arbitrary-complex lower-truncation formula;
   combining them still requires the double-truncation and shift calculation,
   so there is no few-minute direct closure of the remaining hole.
4. Route and pruning — PASS. Checked all proof imports against the finite-limit,
   affine Čech, homology-property, single-comparison and bottom-unit steps.
   Proof-only additions are plain imports; public imports serve the signatures.
   Compared the original proof_deps: derived direct image and the QCoh
   comparison remain; affine higher-image vanishing's cyclic module is replaced
   by its lower-level argument and is listed under No longer needed. The two
   removed edge imports are listed there too. The unit sk-thm-picard-semicon
   has empty realized statement and step lists; no realization is bypassed.
5. DAG — PASS. The parent differs only in proof, proof_deps and proof_origin.
   Independently checked each delivered node's proof_deps equals the union of
   step uses and every dependency exists. Matched the parent steps to the Lean
   argument. Read the new generic normalization node and its signature, source,
   search records, ancestry and creation metadata. The existing acyclicity
   criterion node faithfully includes its left-exactness, injective and all
   three property hypotheses; its existing proof uses dimension shifting.

Second-reading changes: appended this fresh review and generated independent
scratch compilation/axiom evidence. No Lean, signature, definition, import or
DAG repair was needed. One original hole is closed and one strictly smaller
hole is added: decomposition, zero net holes closed. No globally unreachable
module is claimed.

Independent scratch `#print axioms` checks of both public delivered theorems
completed successfully: each lists only propext, Classical.choice, Quot.sound
and sorryAx, consistent with the explicitly open normalization theorem and
open imported dependencies. Scratch files are outside the delivered lean/ tree.

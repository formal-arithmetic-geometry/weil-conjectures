## What changed

Replaced the sorry in `Sheaf.Paper.SmoothRetractRelativeGlobalCompleteIntersection` by
an unchanged-signature proof of `Algebra.smooth_retract_relative_global_complete_intersection`.
The proof uses the existing improvement theorem, composes smoothness, applies Mathlib's
Huber theorem, and explicitly transports both the conormal basis and the retraction.
Private, fully proved helpers identify the extension cotangent module with the quotient
cotangent module, transport it under polynomial renaming, and reindex the finite variables
and relations by `Fin`. The resulting quotient equivalence gives the maps σ and π;
pointwise cancellation proves π.comp σ = id. The A-algebra structure is σ.toRingHom.toAlgebra,
and an explicit A-algebra equivalence transports smoothness from the improved algebra.

Added one module, `Sheaf.RingTheory.SmoothQuotientFibreDifferentialRank`, for the remaining
rank calculation. Its statement assumes a smooth specified polynomial quotient and a
conormal basis, and computes the differential rank at a point of one fibre. It asserts
neither existence of a new algebra nor any retraction. The original module combines it
with smoothness of fibres, the existing smooth-point dimension theorem, and the supremum
of local dimensions. The nonempty spectrum is used explicitly to evaluate the supremum.
Updated the original node's proof, proof_deps and proof_origin to match this reduction.
All existing public signatures, universes, visibility and public imports are unchanged.

Validation: the two delivered modules compile in import order with lcompile.py.
Local sources for Mathlib Huber and the cotangent, presentation, basis and smoothness
interfaces were read. The Stacks files are absent in this local read-only clone, so the
actual sources were read at https://stacks.math.columbia.edu/tag/07CF,
https://stacks.math.columbia.edu/tag/07CG and https://stacks.math.columbia.edu/tag/07CH.
The unit `sk-thm-p1` and its realized steps are unchanged.

## Proved and sorry left

Closed: `Algebra.smooth_retract_relative_global_complete_intersection` (the item's one hole).
The four private helpers `quotientCotangentEquiv`, `reindexCotangentEquiv`,
`finite_conormal_basis_presentation`, and `smooth_conormal_basis_fibre_dimension` have
complete proofs; no private declaration or definition contains sorry.

Added: `Algebra.smooth_quotient_fibre_differential_rank`, exactly `:= by sorry`, in node
`lem-weil-pbc-smooth-quotient-fibre-differential-rank`. This is the only sorry in the
submitted files. Its module and node contain the full argument in words and its source.
One upper hole closed, one lower hole added: this is a decomposition, net zero holes,
not a sorry-free proof of the target's transitive closure. The existing
`Algebra.improve_presentation_smooth_conormal_free` remains an imported dependency;
its hole was not changed or added by this delivery.

Edge cases checked mathematically: the zero quotient and zero fibres have no fibre primes;
the new theorem is therefore vacuous there, while the presentation condition tests only
nontrivial fibres. With c=0 it gives the polynomial differential rank n. With n=0 and a
nonempty fibre the split sequence forces c=0. A basis with c>n cannot occur in a nonempty
smooth fibre; the inequality is an explicit conclusion, not an assumption. No nontriviality
hypothesis was added to the original target, and no arbitrary witness supplies data to a
definition: all new equivalences and algebra structures are explicit constructions.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.SingularIdeal`: its smooth-at-prime definition is exposed by the
  still-used `SmoothAtPrimeDifferentialsDimension` import.
- `Sheaf.RingTheory.SmoothLocalizationConormalSplit`: no application is made in this
  module; the new rank item plans to use the already-proved presentation-level split.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: its definitions are exposed by the
  still-used dimension theorem imports.

The rank item's proof plan uses `Sheaf.RingTheory.PresentationLocalizedConormalSplit`
(at a=1), differential base change, and elementary finite-dimensional product arithmetic.
It does not require base change of the conormal module to an arbitrary fibre or the
local-complete-intersection/regular-sequence route. No entire module is claimed removed
from the targets' closure: the improvement theorem still imports the older localized
conormal split, and the redundant imports' definitions remain used transitively.

Removed from the original node's direct proof_deps (retained where a lower statement
or definition uses them):
- `def-kun-topological-dimension-at-point`
- `def-kun-topological-krull-dimension`
- `def-weil-affine-spectrum`
- `def-weil-pbc-kahler-differentials`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-kahler-differentials-base-change`
- `lem-weil-pbc-smooth-localization-conormal-split`

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The DAG's Huber Mathlib match is
mathematically correct but is not a one-line Lean application: its basis is an S-basis
of an extension cotangent type synonym, and its output index sets are sums with Unit.
The target instead needs a quotient-ring basis indexed by Fin. The coefficient,
module and variable transports are now fully proved, including the equation-class identities.

The remaining fibre-rank glue is not supplied by one existing theorem in the required
form. It has therefore been isolated, rather than duplicated as an existential
retraction theorem. A broader existing basis is sufficient for this rank calculation;
the equation-class property remains proved and returned by the original target.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, not no match.

Recovery validation: both saved modules compiled again with lcompile.py --all
(2.7 and 5.2 seconds). The first dry run got past the historical ImportError but
briefly rejected installed Mathlib source imports as missing. Without any tool,
source, environment or proof workaround, a retry of the prescribed command printed
OK: the dry-run commit compiles and passes preflight, classified CODEX. Nothing
was pushed. The historical failure recorded in the second reading below is resolved;
the saved independent review and its findings remain unchanged.

## New nodes

`lem-weil-pbc-smooth-quotient-fibre-differential-rank` is the rank part of steps 4–5
of the original proof. It fixes a quotient, a prime of R and a prime of its fibre,
and uses the conormal basis to compute the residue-field differential rank.
Its split-sequence, scalar-extension and differential-base-change proof follows
07CG/07CH, with the already-proved localized presentation split as its first dependency.
Blueprint searches for "conormal differential rank" and "conormal" found no matching
statement; the latter returned only unrelated normal-bundle and curve differential notions.
No change record is needed: no existing public interface or statement was changed.

## Earlier second reading (a previous round; superseded)

1. Interface preservation: PASS. Read the full diff against the repository's module
   and compared the declaration tables with stage3_delivery.diff_module. The existing
   theorem's signature, universes, visibility and public imports are byte-for-byte
   unchanged. The new helpers are private and the added import is proof-only. No
   existing definition or statement changes, hence no change record is required.

2. Proof and axioms: PASS as a decomposition. Independently compiled both modules in
   import order with lcompile.py (6.6 and 9.1 seconds). Scratch copies with explicit
   #print axioms checked all six declarations: the two equivalence definitions and
   finite_conormal_basis_presentation use only propext, Classical.choice and Quot.sound;
   smooth_conormal_basis_fibre_dimension, the original theorem and the new rank theorem
   additionally use sorryAx from the reported open statements. There is exactly one
   textual sorry, in smooth_quotient_fibre_differential_rank. No forbidden declaration,
   hollow definition, or arbitrary witness chosen into a definition occurs. The
   retraction, quotient equivalences and transported algebra structures are explicit.
   The original theorem is reduced to smaller dependencies, not axiom-free yet.

3. Split statement: PASS. Independently read the rank statement and its full docstring
   proof, the localized presentation splitting theorem, the differential base-change
   interfaces, and Stacks 07CF, 07CG and 07CH. A finite polynomial presentation of the
   fixed quotient supplies the split sequence; scalar extension to the fibre-point
   residue field and differential base change give c + differential finrank = n.
   Empty fibres have no q; n = 0 forces c = 0 at a fibre point; c = 0 gives rank n;
   c > n cannot occur at a fibre point. The basis need not consist of equation classes.
   This is strictly the rank part of the argument: it constructs no algebra, basis,
   retraction or complete-intersection presentation. Repeated searches with different
   words through msearch.py (LeanFinder, Loogle and grep) and rg of Sheaf, upstream and
   Mathlib found no exact existing statement. Standard-smooth rank results require
   extra presentation data, and the nearby free-conormal-basis theorem chooses a
   localized subset rather than calculating this specified basis's fibre rank.
   Closing the rank theorem requires the remaining scalar-action and tensor transports;
   it is not a few-minute application of a theorem already available.

4. Route and pruning: PASS. The original proof uses the improvement theorem, Mathlib's
   Huber theorem, explicit quotient and index transports, fibre smoothness, the proved
   smooth-point dimension theorem and the proved dimension-supremum theorem. This is
   a real reduction from the top, including the basis equation identities and both
   retraction and smoothness transports. Read sk-thm-p1.json, including every realized
   step: none is bypassed or altered. All three removed direct imports are redundant
   for this proof, and the report names exactly all seven removed direct proof_deps.
   No entire module is asserted pruned from the targets' import closure. The new rank
   module retains its splitting/base-change proof-plan imports; its public imports
   provide the objects in its statement and its proof-only imports stay private.

5. Node agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Both nodes' proof_deps equal the union of their steps' uses. The new
   node contains its source, mathematical proof, search records, split status,
   created/blueprint/chapter/unit records and the verbatim Lean signature. The Lean
   reduction implements the rewritten steps and the new node carries exactly the
   sole newly introduced hole. One old hole closed and one added is net zero, as
   the report correctly states.

Changes in second reading: added this independent review and search evidence.
No Lean or node repair was needed. Removed the temporary axiom-probe copies after
compilation; they are not delivered.

Delivery tool failure after second reading: the prescribed deliver3.py --no-push
command exited before its compilation/preflight/push phase with ImportError:
cannot import name 'refuse_missing' from 'import_cycles'
(/home/ubuntu/weil-conjectures-sheaf-Q1/tools/import_cycles.py), raised by
check_import_sources at /home/ubuntu/weil-launcher/deliver3.py:65.
No delivery was pushed. Per AGENTS.md section 3 and section 6, the reviewer did not
edit the tool or work around its checks. The launcher/maintainer must repair the
delivery-tool import interface before this reviewed sandbox can be delivered.


## Second reading by Q1

1. PASS: independently read the full module diff. The sole existing public theorem's
   signature is byte-for-byte unchanged, including universes and hypotheses; public
   imports are identical. New helpers are private. No existing definition changes
   and no change record is required.

2. PASS as a decomposition: compiled both modules in import order with lcompile.py.
   Scratch copies with #print axioms checked all six declarations. The two explicit
   cotangent equivalences and finite_conormal_basis_presentation use only propext,
   Classical.choice and Quot.sound. The fibre-dimension helper, target theorem and
   new rank theorem also use sorryAx from the reported open dependencies. Exactly
   one textual sorry remains in the delivery, in the named rank theorem. No forbidden
   declarations, hollow definitions or arbitrary witness chosen into a definition
   occur. Scratch copies were removed before delivery.

3. PASS: read the new rank signature, complete docstring proof and node, the proved
   presentation-localization splitting theorem, Mathlib's smooth cotangent criterion,
   Huber theorem and differential tensor equivalence, and Stacks 07CF/07CG/07CH.
   Tensoring the split sequence over Q with the residue field K gives a direct sum
   of dimension n; the conormal basis gives the first summand dimension c, and
   differential base change identifies the second with the stated fibre differential
   module. Zero fibres have no q; c=0 gives rank n; n=0 forces c=0 at a fibre point;
   c>n cannot occur there. The lemma is strictly smaller than the retraction target.
   Fresh searches with msearch.py LeanFinder (smooth polynomial quotient cotangent
   basis residue field dimension codimension), Loogle (KaehlerDifferential,
   Module.finrank), grep (finrank.*Cotangent|finrank.*Kaehler|splitSurjectiveEquiv),
   and rg of Sheaf, upstream and installed Mathlib found components but no direct
   replacement. The remaining scalar and tensor transports are not a few-minute
   application of an existing result, so the documented rank hole is retained.

4. PASS: the proof follows improvement, Huber presentation, explicit quotient and
   basis transports, transported retraction and smoothness, fibre rank, local
   dimension and the nonempty supremum. Read sk-thm-p1's realized steps; none is
   bypassed or edited. All three removed direct imports are redundant, and the
   report names precisely the seven removed proof_deps. No entire module is claimed
   pruned from the targets' closure. New proof-plan imports are plain imports;
   public imports supply the new statement's objects. One upper hole closed and
   one lower hole added is a decomposition with net zero holes.

5. PASS: existing node changes only proof, proof_deps and proof_origin. Verified
   programmatically that both proof_deps sets equal the unions of their steps' uses,
   and the new node's Lean signature is verbatim. Its source, complete proof, searches,
   split status, created, blueprint, chapter, unit and Lean records are present.
   The node plans match the implemented reduction and its sole added hole.

Changes in this second reading: appended this fresh independent review and validation.
No Lean or node repairs were needed.

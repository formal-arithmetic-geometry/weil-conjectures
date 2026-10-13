## What changed

Only `lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechTotal.lean` and its existing node
`def-sc-principal-open-alternating-total` change. All existing signatures, visibility,
definitions, imports, options and previously proved helpers stay unchanged.

Proved `AlgebraicGeometry.principalCechDerivedComparison_exists` using the functorial
K-injective resolution and a natural derived-sections unit. Inverting the augmentation
on the resolution defines a natural comparison; cancellation proves its prescribed
formula for every K-injective resolution. This follows the categorical construction
already used in `QCohComplexAlternatingCechDerivedSections`, without importing it or
requiring quasi-coherence. Added only the proved private derived-unit definition and
its computation lemma. They occur only in public theorem proofs, not public definitions.

The original session also developed and compiled a complete augmentation construction.
The delivery dry run fetched an updated base where that obligation is already proved.
The sandbox was reconciled to preserve the fetched base's entire augmentation proof
and helpers verbatim. No credit for that independently completed obligation is claimed.

Validation: the complete module compiled without warnings before the dry run. The final
reconciled file is compiled again by the delivery dry run and its declaration/axiom probe.

## Proved and sorry left

Closed 1 of the 3 holes on the updated delivery base:
`AlgebraicGeometry.principalCechDerivedComparison_exists`.
Added holes: none. This is a complete proof from the existing augmentation theorem
and derived-functor interface; it still uses the original K-injective augmentation hole.

Every remaining sorry in the delivery belongs to
`def-sc-principal-open-alternating-total` and retains its source and proof docstring:

- `AlgebraicGeometry.principalCechDifferential_square`.
- `AlgebraicGeometry.principalCechAugmentation_quasiIso`.

The derived comparison depends on both remaining obligations. No assertion of
axiom-free completion of these dependent constructions is made.

## No longer needed

None. No imports were added or removed. The existing node has no external proof
dependencies, and the unit has no realized nodes to bypass. The categorical pattern
from `QCohComplexAlternatingCechDerivedSections` is used directly, so that module and
its quasi-coherence, affine-acyclicity and resolution-comparison imports are not needed
by this proof; they were never imported by this item. Neither remaining obligation nor
any existing DAG module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction is needed. The original derived-comparison
argument can be realized by natural transformations and cancellation, without proving
preservation of homotopies by principal totalization as a separate prerequisite.

The base advanced during the session: the augmentation obligation and its private
helpers were added by another delivery. The initial dry run detected that conflict;
the final sandbox preserves all those declarations and delivers only the new derived
comparison proof. No interface correction or change record is necessary.

## Second reading by X3

1. Interface preservation: read the complete delivered module and compared it with
   the repository version using `diff -u` and the declaration parser. Every existing
   signature, visibility, definition body, import and option is unchanged. The only
   existing proof changed is `AlgebraicGeometry.principalCechDerivedComparison_exists`.
   Its hypotheses still allow every commutative ring, every finite cover (including
   r = 0), every unbounded coefficient complex, and every K-injective quasi-isomorphic
   resolution. The two added helpers are private and occur only in the theorem proof.
   No statement change or change record is needed. Verdict: pass.
2. Proof and axioms: compiled the delivered module locally through lcompile.py with
   no errors or warnings (38.6 seconds). Compiled a scratch copy with `#print axioms`
   for both private helpers, the completed theorem and the public comparison definition
   (33.3 seconds). The helpers use only propext, Classical.choice and Quot.sound;
   the theorem and comparison additionally use sorryAx from the existing open
   obligations. The only two sorry occurrences are the named, documented original
   theorems principalCechDifferential_square and principalCechAugmentation_quasiIso.
   No forbidden declaration or hollow definition was introduced. The comparison's
   prescribed equation determines its value uniquely: use the functorial resolution,
   whose localized map and localized augmentation are invertible. Its definition
   therefore does not select an arbitrary unspecified witness. Verdict: pass.
3. Split statements and edge cases: no statements were split off and no new holes or
   public statements were added. Both private helper statements are proved: the first
   explicitly transports the existing right-derived unit through quotientCompQhIso,
   and the second unfolds rightDerivedFunctorObjQIso. The construction has no
   nonempty-cover or nonzero-ring assumption. Empty covers and zero complexes follow
   the same natural-transformation argument; the singleton cover recovers the ordinary
   section comparison. Verdict: pass; no new-node searches are required.
4. Route and pruning: checked the natural transformations and each cancellation from
   the top theorem downward. For beta = B(eta) a(I)^{-1} b(I) D(eta)^{-1}, naturality
   gives a beta = b; on any K-injective J the unit b is the inverse of the prescribed
   section identification, so cancelling a_J gives the required identity. Naturality
   of beta then proves the equation for every i, without a separate homotopy-preservation
   lemma. Read the existing QCohComplexAlternatingCechDerivedSections pattern and
   searched the upstream right-derived interface and Mathlib localization/derived
   modules for a shorter applicable route. Their generic units and isomorphisms are
   already used; the QCoh theorem concerns different section and totalization functors
   and adds hypotheses, so importing it would not replace this proof. All three current
   public imports supply existing statements or definitions (including IsKInjective
   and rightDerivedFunctorObjQIso in the theorem's signature), rather than proof-only
   exports. No imports or old proof dependencies are unused by the replacement.
   The unit sk-thm-picard-duality has empty realized statement and step lists; no unit
   step is bypassed or modified. Neither remaining hole admits an immediate closure
   from the searched interface. Verdict: pass; pruning list remains none.
5. DAG agreement: opened def-sc-principal-open-alternating-total and its unit record,
   and compared the delivered JSON. Only proof and proof_origin change. The added
   step describes exactly the natural-resolution construction and explicitly retains
   the K-injective augmentation obligation. proof_deps remains empty because all
   item-specific obligations belong to this same node; the Lean uses the existing
   imported generic categorical interface. No new nodes or public declarations need
   records. Verdict: pass.

Second-reading changes: appended this review and its independent compilation/axiom
results. No Lean or node repair was necessary. Net holes closed: one; holes added:
zero; two original holes remain. The completed comparison is a reduction to existing
open obligations, not an assertion that its full axiom closure is already proved.

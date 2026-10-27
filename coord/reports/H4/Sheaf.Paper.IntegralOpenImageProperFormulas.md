## What changed

Completed the three proofs in Sheaf.Paper.IntegralOpenImageProperFormulas from the
existing integral open-image, localizing base-change and projection detail declarations.
No split-off statements, new definitions or source-library changes.
The complete module passed lcompile.py with no diagnostics in 55.5 seconds; the
resumed 2026-10-25 check returned the same successful compile result.

The open-image detail uses the spectral integer ring on ULift E. Its proved comparison
with the embedded integer ring is reused from IntegralCoefficientExtComparison via a
proof-only `import all`; the proved scalar-restriction constructibility helpers come
from IntegralConstantModelHeartClosure. The already proved bounded_transport_iff
helper in IntegralProperCohomologicalBounds packages exact restriction's transport of
boundedness and
cohomology. The published derivedComapLowerStarIso transports the pushforward conclusion
back, and the existing Dctf=Dbc theorem supplies finite Tor amplitude.

Base change rewrites the two localizing-closure predicates and applies its detail
statement. Projection uses the same detail base-change theorem on the identity square,
identifies derived identity pullback with the identity functor, applies tensor closure,
and transports membership through the canonical projection isomorphism by repleteness.
The node's proof and proof_deps now record the coefficient transport actually used.
All added imports are proof-only. The existing integerRingSheafIso and derived
coefficient-comparison definitions are locally irreducible during elaboration; this
preserves their definitions and public interfaces while avoiding expensive unfolding.
The monoid-hom proof for the sheaf-composed ring isomorphism is supplied explicitly. Original public imports are preserved.

Corrected integralProperProjection with `include k in` to retain the existing source's
standing hypotheses. This repairs an elaboration defect, not the mathematical node.
The change record is coord/changes/H4-integral-projection-standing-setting.md.
The current downstream audit lists 130 modules and zero external theorem callers, so no consumer changes
are needed. No target declaration or definition changes.

## Proved and sorry left

Original module: three named holes. Current module: zero holes. Added holes: zero.

- integralOpenDirectImage: original statement proved, original hole closed.
- integralProperBaseChange: original statement proved, original hole closed.
- integralProperProjection: corrected standing-setting statement proved; original
  overgeneral signature is not claimed as proved. Its former hole is removed by the
  documented statement repair, not counted as proof of that original signature.

Thus two of the three original statements are proved unchanged, and the third is
corrected and proved. All belong to sk-thm-sf-pf-adic. No new theorem with sorry is
introduced, and no sorry remains in this delivery. The detail declarations used as
premises may themselves depend on sorry; that is the authorized stage-3 assembly.

Edge cases remain included: the empty open, identity open, zero objects and identity
cartesian square. Coefficient transport is an actual ring isomorphism and adds no
flatness hypothesis; extension along its inverse is isomorphic to exact restriction.

## No longer needed

None. All original private proof imports and all stated mathematical proof dependencies
are retained. No module or node is withdrawn. The three detail results remain on the
unit's route, as do the Dctf=Dbc identification and qcqs facts. The additional imports
supply proved coefficient and identity-pullback comparisons used in the written proof.

## Where the brief, the DAG or earlier work was wrong

The original Lean integralProperProjection accidentally omitted the documented base
field and its standing hypotheses because section variables absent from its explicit
type are not included by Lean. The first attempted proof failed with Unknown identifier
k; its context had no base-field data. The detail theorem and the natural-language node
correctly require these hypotheses. `include k in` restores them, without changing the
node's mathematical assertion or a target signature. Both library-root usage searches
and tools/downstream.py --uses integralProperProjection found no callers to adapt.

The open-image detail and item do not use definitionally identical coefficient rings.
The proved embedded/spectral isomorphism and derived scalar-restriction comparison
bridge this presentation difference. The natural-language proof had suppressed this
encoding step; it is now recorded in the node and implemented in Lean.

The unit record remains the older master-era description, with empty realized fields;
the existing node already reports this mismatch. The proof follows all three detail
steps of the current literature/blueprint/latest unit and does not bypass them.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Reduced `AlgebraicGeometry.exists_strictlyPerfect_evaluation_comparisons` without
changing its signature. Resolve the arbitrary second complex by a K-injective
complex. Prove internal Hom preserves this quasi-isomorphism using bounded
exact-term Hom and a proved retraction from the finite-free short exact sequence.
Compose the resolved source comparison with Q fI, the inverse localized Hom
resolution map and the inverse Q f. Compose its target comparison with the
inverse localized Hom resolution map. Associativity and cancellation prove
the required square, without a tensor-resolution or evaluation-naturality map.

One new statement module isolates the resolved comparison square. Its source
and proof in words are included in its docstring and DAG node. No definitions, existing public
interfaces, target signatures or other held modules were changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_strictlyPerfect_evaluation_comparisons` by decomposition.
The item's module contains no remaining sorry. Added one hole:

- `AlgebraicGeometry.exists_strictlyPerfect_kInjective_evaluation_comparisons`
  (`lem-pc-strictly-perfect-kinjective-evaluation-comparisons`). This handles only
  a K-injective second representative; it excludes the resolution transport
  and the proof that Hom(P,-) preserves quasi-isomorphisms.

The private retraction, exact-Hom and quasi-isomorphism helpers are fully proved.
Validation: the main module compiles without warnings using lcompile.py.

Net holes: one closed, one added; this is a decomposition, not a sorry-free proof
of the target's import closure. The unrestricted second-complex reduction and
finite-projective-to-exact-Hom steps are now proved.

## No longer needed

Removed the direct proof imports
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and
`Sheaf.Paper.DerivedInternalHomRestrictOpen` from the item's module. These remain
part of the K-injective comparison node's plan and are not globally pruned.
The parent proof no longer directly needs the bounded dual construction or the
restriction comparison: those belong only to the resolved comparison item.
No blueprint unit statement or realized unit step is bypassed.

The complete list removed from the parent's old `proof_deps` is:
`def-pc-canonical-derived-tensor-hom-bijection`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-tensor-complex-sheaves`,
`def-pur-hom-complex`, `lem-pc-bounded-above-flat-kflat-site`, and
`lem-sc-derived-internal-hom-restrict-open`. These remain statement dependencies
or dependencies of the new resolved case; no module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The given proof dependencies do not expose a commuting evaluation square on
representatives: the restriction theorem only gives a Nonempty isomorphism.
The missing compatibility is isolated in the already K-injective target case,
while the arbitrary-resolution transport is written in Lean in this delivery.
The affine strictly-perfect Hom interface cannot apply on arbitrary U; the
bounded-exact-term result applies on the localized ringed site without affineness.

The resolved case includes zero complexes and empty opens. No arbitrary witness
from an unproved existence theorem is used in a definition: the new hole is a
proposition, and its witnesses are eliminated inside the proof of the original
proposition. The new theorem adds the substantive K-injectivity assumption;
it cannot be applied to the arbitrary F without the resolution, localized Hom
quasi-isomorphism and explicit isomorphism transport proved here.

Searches used LeanFinder, Loogle, grep on Mathlib and both library roots, and
LeanSearch (unavailable: Internal Server Error). The source tags 08DQ, 08DM and
08DL were read online. Upstream categorical derived dualizability exists but does
not identify this project's fixed Hom-complex and canonical tensor-Hom family.

## New nodes

`lem-pc-strictly-perfect-kinjective-evaluation-comparisons` isolates the local
comparison for a K-injective second model. It is a strict special case used after
resolving the input; the parent proves descent back to the unresolved input.

No change records or forced adaptations are needed.


## Second reading by N1

1. Compared both delivered modules with the repository. The only existing public
   declaration has a byte-for-byte identical signature, including binder names,
   hypotheses and conclusion. The two public imports are unchanged. All added
   proof dependencies are plain imports. There are no definition or interface
   changes, forced adaptations or change records. Verdict: pass.
2. Compiled both modules in dependency order using lcompile.py, without warnings.
   Scanned for forbidden declarations and data holes: the sole textual sorry is
   the whole proof of the public resolved-case theorem listed above. The original
   theorem and three private helpers contain no sorry. Checked the retraction
   components, contravariant Hom direction, functorial resolution, and final
   cancellation. A scratch-copy axiom check records the actual transitive axioms
   below; inherited sorryAx is permitted only for the still-open dependencies.
   Verdict: pass, as a decomposition with one hole closed and one added.
3. Read the new theorem, its source-based proof in words and matching node.
   K-injectivity is an additional genuine assumption, discharged for the actual
   resolution in the parent; the parent also proves preservation of its resolution
   quasi-isomorphism. Thus this is strictly the resolved comparison part, rather
   than renaming the original claim. For P=0, F=0, rank-zero terms and empty U,
   evaluation and the derived objects are zero and the asserted comparisons are
   consistent; unbounded F is allowed throughout. Searched again using LeanFinder
   for derived duality of bounded finite projectives, Loogle for K-injectivity and
   short exactness, and grep for dual evaluation and short-complex retracts in
   Mathlib and both library roots. No existing theorem supplies this fixed
   sheaf-complex comparison. Closing the resolved case requires the remaining
   derived tensor/Hom compatibility argument, not a routine application.
   Verdict: pass; the hole remains explicitly reported.
4. Checked the top-down reduction and imports. The explicit resolution transport
   avoids an unnecessary evaluation-naturality square by choosing the existential
   source comparison through the two invertible ordinary evaluation maps.
   The generic short-exact retraction helper has no direct Mathlib replacement
   found by the independent search. Existing bounded-exact-term and finite-free
   Hom theorems are used. Proof-plan imports of the holed resolved case are kept.
   The No longer needed section now names every removed parent proof dependency.
   The unit sk-thm-picard-duality has empty realized statement/step lists; no
   realized node is bypassed and the local finite-duality route is retained.
   Verdict: pass; no global module pruning claimed.
5. Compared node records: the existing node changes only proof, proof_deps and
   proof_origin. Each proof_deps list equals the union of its steps' uses. The
   parent records the three actual reduction steps. The new node has its source,
   complete proof plan, searches, provenance, blueprint ancestry and Lean record,
   including the additional K-injectivity assumption. Verdict: pass.

Second-reading changes: completed the explicit removed-dependency inventory and
added this independent review. No Lean proof, signature or node repair was needed.


Axiom-check evidence from a scratch copy compiled with lcompile.py: all three
private helpers use only propext, Classical.choice and Quot.sound. The parent
and the new resolved-case theorem use those three plus sorryAx, as expected
for the explicitly remaining comparison hole. No other axioms appeared.
The scratch copy was removed before preflight.

Independently read the online source proofs at
[08DQ](https://stacks.math.columbia.edu/tag/08DQ),
[08DM](https://stacks.math.columbia.edu/tag/08DM) and
[08DL](https://stacks.math.columbia.edu/tag/08DL), since the local TeX source is
not present on this machine. Their bounded finite-projective calculation,
K-injective computation and open restriction support the new special case.
Also read the applicable C2-ordinary-evaluation-construction-location change:
its moved constants are definitionally equal and require no downstream edits.

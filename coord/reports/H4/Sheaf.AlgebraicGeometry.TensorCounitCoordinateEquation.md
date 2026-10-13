## What changed

Proved `AlgebraicGeometry.tensorCounit_coordinateEquation` in
`Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation`, preserving its original signature
and docstring. Added the proof-only import `Sheaf.Algebra.Homology.KFlatResolution`.
The private helpers `pinnedComparison_natural` and `modelMap_natural` prove chain comparison
naturality from the summand equations and localization tensor naturality, respectively.
The main proof resolves both inputs, uses the canonical predicate on the resolved pair,
transports both sides by naturality, and cancels the derived resolution tensor map.

Local registrations of the existing tensor instances and local colimit instances cache
standard coproduct existence proofs during elaboration; they introduce no global instance
registration and no change to any existing statement or definition. A declaration-scoped
heartbeat budget supports tensor/localization instance elaboration; the 60-second compile
limit is unchanged. No arbitrary object
is chosen in a definition. The existential resolutions are eliminated only inside a proof.
The node's proof, proof dependencies, and proof origin now describe this Lean argument.
The four new public cache names and their local instance registrations are documented in
`coord/changes/tensor-counit-colimit-instances.md`; no existing interface is changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.tensorCounit_coordinateEquation`
(node `lem-pc-tensor-counit-coordinate-equation`).
No `sorry` remains in the delivered module. No holes are added or split off.
Both private helpers and all local colimit instances have complete proofs.
The proof uses existing named declarations, notably
`CochainComplex.exists_isKFlatResolution`; any proof holes below those existing declarations
are not new holes in this delivery. This closes one upper hole without adding lower holes.

## No longer needed

No existing import is removed: the canonical comparison module supplies the statement's
objects and definitions, and the new K-flat resolution import is used by the proof.
The proof does not use `lem-pc-derived-pullback-tensor-product` /
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct`; its direct proof-dependency edge is
removed. That module can remain reached through other imports of the canonical comparison
module, so this is not a claim that the entire module leaves the targets' closure.

The earlier sandbox attempt's `tensorCounit_coordinateEquation_cancel` and its node
`lem-pc-tensor-counit-coordinate-equation-cancel` are not retained. The proof cancels the
actual derived tensor resolution map directly with `cancel_epi`.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt only added a generic cancellation lemma and left the assigned theorem
with its original hole. Its assertion that the arbitrary-complex transport step could not
be stated from the available declarations was incorrect: the existing K-flat resolution
and canonical predicate, together with the two naturality helpers, give the full argument.
The original mathematical resolution route is retained. In particular, it does not require
ordinary pullback to preserve the quasi-isomorphisms r or s, and uses neither invertibility
of the localization tensor map at the original inputs nor invertibility of their counits.


## Second reading by H4

1. Compared the sole delivered module with the repository using `diff`. The existing
   `tensorCounit_coordinateEquation` signature is byte-for-byte identical, including
   its universe annotations, hypotheses, let-bound instances, and quantified pinned
   comparison. Its original docstring is unchanged. The only additional public names
   are the four fully proved colimit-existence caches; their local registrations and
   interface addition are explicitly documented in the change record. No definition
   or target statement changes, and no other module is delivered. Verdict: pass.

2. Read both private helper proofs and the resolution transport proof in full. The
   module compiles locally without errors or warnings through `lcompile.py`. It has
   no `sorry`, axiom, unsafe, opaque, implemented_by, or extern declaration. K-flat
   resolutions are eliminated inside the theorem proof, never used to define an
   arbitrary object. The cancellation uses only the derived images of the two
   resolution quasi-isomorphisms, not quasi-isomorphisms of ordinary pullbacks or
   invertibility of the total tensor resolution map. Verdict: pass, with the separate
   axiom check recorded below.

3. There are no split-off statements or added holes. The private naturality helpers
   are fully proved; the colimit caches specialize established existence instances.
   The argument applies unchanged to zero complexes, the empty scheme, and identity
   resolution maps: no hidden nonzero, boundedness, or surjectivity premise enters.
   Searched Mathlib with `msearch.py grep` using totalization and naturality terms,
   and searched the project with `rg` for tensor-model and comparison naturality.
   Existing `tensorModel_natural` is private; the public Mathlib lax tensor naturality
   theorem is already used. The mapBifunctorComparison naturality theorem concerns a
   constructed comparison, whereas this theorem quantifies over the given pinned
   isomorphism, so the summand-extensionality helper supplies the required bridge.
   Verdict: pass.

4. The proof resolves the original upper hole directly and adds none. Both imports
   are needed: the public canonical comparison import supplies the signature and
   the private K-flat resolution import supplies the proof. No proof-only import is
   public. The report lists the complete removed old dependency edge, namely
   `lem-pc-derived-pullback-tensor-product`, without claiming its module is globally
   pruned. Read `dag/units/sk-thm-picard-semicon.json`: its realized fields remain
   unchanged, and the K-flat resolution argument is below the unit level and
   bypasses no realized unit step. Verdict: pass.

5. Compared the old and delivered DAG records. Their mathematical statement and
   Lean statement are unchanged. The new proof steps describe summand naturality,
   K-flat resolutions, counit and localization naturality, and cancellation exactly
   as in Lean. Checked programmatically that `proof_deps` is precisely the union of
   all step `uses`; `proof_origin` records H4 and the source route. No new node is
   required for an open statement because there is no new open statement. Verdict:
   pass.

Second reading changes: added this independent review and validation evidence to the
report. No repair to the Lean proof, node, or change record was needed.

Final validation: a scratch copy with `#print axioms
AlgebraicGeometry.tensorCounit_coordinateEquation` compiled and reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs in this theorem's
axiom closure. The delivery dry run printed OK at `3c922faf33`, with review class
CODEX because the node and documented public cache names change. Its compilation,
all-declaration axiom probe, and preflight passed. Some earlier compile attempts hit
the unchanged 60-second limit; both the actual file and the explicit axiom scratch
copy subsequently compiled cleanly through the prescribed tool. No Lean edits were
made during the second reading.

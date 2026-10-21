## Worker report

Item: sk-d-real-weights. Source read: the complete definition in
literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-weights/_section.md,
and the current DAG statement and its five proof steps. The statement is unchanged.
The delivery supplies only RealWeights.lean and reuses the landed local-factor dependency unchanged.
No new DAG nodes, axioms, hollow data, or proof developments are introduced.

The upstream module WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights already
supplies frobeniusWeight for an arbitrary coefficient field. This declaration is reused
directly. Its representation-level localPolynomial, localEigenvalues, IsPunctuallyPure,
HasWeightsAtMost and IsReal, however, fix PadicAlgCl l and V : Type u with the scheme.
They cannot be applied to the chosen Setup.Qbar : Type v and an independently sized
finite-dimensional representation. LocalWeights supplies that generalized interface;
it uses the same WeilGroup and the same primitive polynomial constructions. It agrees
definitionally with those upstream definitions at their specialization. There is no
second logarithm, norm, reverse characteristic polynomial, or Weil group.

Clause-by-clause correspondence:

* Standing fields and embedding: RealSheaves.Setup is imported through RealWeilSheaves.
  Its arbitrary chosen coefficient field can be used as E; its plain field embedding
  can be used as iota. The formulas are defined for any field E, with algebraic closure
  required explicitly for the spectral and reality theorems. In particular no
  surjectivity, continuity, or identification of coefficient and scheme universes is
  required. The formulas do not require lissity, smoothness, or a lattice to evaluate;
  they apply to every representation supplied by the chapter's Weil-sheaf definition.
  The chapter curve is a specialization of the existing IsCurve parameter of WeilGroup.
* Representation and finite dimension: W : WeilGroup p and rho : Representation E
  W.carrier V use the dependency's group and local geometric Frobenius, with independent
  universes u, v, w and [FiniteDimensional E V]. No semisimplicity is assumed.
* Closed point and residue cardinality: C0.finitePoints is exactly closedPoints C0
  over the finite field by Scheme.Hom.finitePoints_eq_closedPoints (PointCount.lean).
  C0.pointNorm x.val is Nat.card of the residue field. For the chapter this is the
  q^(e_x) denoted Setup.closedPointCardinality. Constructible clauses use the literal
  closedPoints subtype and Nat.card of its residue field, as the punctual dependency.
* Local polynomial: LocalWeights.localPolynomial W rho x is
  (rho (W.frobenius x)).charpolyRev, the recorded basis-independent det(1-TF).
* Local eigenvalues and multiplicity: LocalWeights.localEigenvalues is
  (rho (W.frobenius x)).charpoly.roots. Mathlib's roots includes algebraic root
  multiplicities. local_spectral_data states nonvanishing of every eigenvalue,
  the product of the factors (1-alpha T), and equality of rootMultiplicity at
  inverse alpha for the local factor with rootMultiplicity at alpha for charpoly.
* Weight: the imported AlgebraicGeometry.WeilGroup.frobeniusWeight is literally
  2 * Real.log (norm (iota alpha)) / Real.log qx. No different power normalization
  or integral-weight convention is used.
* Punctual purity: LocalWeights.IsPunctuallyPure universally quantifies over x and
  alpha in that local eigenvalue multiset and requires the weight to equal w : Real.
* Upper bound: LocalWeights.HasWeightsAtMost has the identical quantifiers and <= w.
  This is a pointwise spectral bound, not the existence of a mixed filtration.
* Reality: LocalWeights.IsReal requires every embedded local coefficient to be fixed
  by starRingEnd Complex, exactly zero imaginary part. isReal_iff_conjugation states
  equality of the complex eigenvalue multiset with its conjugate, including repetitions.
  Algebraic closedness is an explicit theorem binder, so section-variable omission
  cannot silently remove this necessary hypothesis.
* Constructible stalk convention: the imported SfPunctualEigenvalue and
  SfIsPunctuallyPureOfWeight use the exact common-stage constructible heart and the
  scalar extension of localClosedFrobeniusCohomology in degree zero. The theorem
  constructible_purity_iff_logarithmic identifies that existing purity predicate
  with the displayed logarithmic one; it does not redefine purity. The definition
  HasConstructibleWeightsAtMost quantifies over these same stalk eigenvalues and
  uses the same logarithmic weight. The landed sfLocalCharacteristicFactor
  supplies the polynomial on those very stalk operators, and SfIsReal supplies
  coefficientwise reality. constructible_reality_iff_conjugation states the multiset
  equivalence on the roots of the reversed embedded factor, namely the complex
  stalk eigenvalues. No global representation, rank constancy, or lissity of the
  entire constructible sheaf is assumed.

Dependency declarations read and used:

* Sheaf.Paper.RealWeilSheaves: RealSheaves.ConstructibleWeilSheaf and its global
  compatible-system/rational-Weil-pair construction; its imported WeilGroup and
  local geometric Frobenius interface is retained.
* Sheaf.Paper.RealSheavesSetup: RealSheaves.Setup, Setup.IsCurve,
  Setup.closedPointDegree, Setup.closedPointCardinality and Setup.localFrobenius.
* WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix: LinearMap.charpolyRev,
  defined as the reverse of charpoly, with its determinant and change-of-basis API.
* Mathlib.LinearAlgebra.Charpoly.Basic: LinearMap.charpoly.
* Mathlib.Algebra.Polynomial.Roots and Div: Polynomial.roots and rootMultiplicity.
* Mathlib.Analysis.Complex.Norm: Complex.instNorm and norm_def.
* Mathlib.Analysis.SpecialFunctions.Log.Basic: Real.log, log_of_pos, exp_log,
  log_exp and log_pos; the norm and logarithm are reused through frobeniusWeight.
* Sheaf.Paper.AdicPunctualWeights: WeilConjectures.SfPunctualEigenvalue and
  SfIsPunctuallyPureOfWeight, including their finite-stage and residue-embedding
  quantifiers. The unrelated SfIsMixedOfWeightsAtMost is not substituted for a bound.
* Sheaf.Paper.AdicLocalCharacteristicFactor: the original landed sfLocalCharacteristicFactor
  and SfIsReal, without any definition or record change in this delivery.
* Sheaf.Algebra.Polynomial.ReciprocalRootFactorization: the generic uniqueness and
  inverse-root multiplicity statement in the node's proof plan.

Theorem placeholders: local_spectral_data (item proof step 1),
isReal_iff_conjugation (item step 3), constructible_purity_iff_logarithmic
(steps 4 and 5), and constructible_reality_iff_conjugation (steps 3 and 5).
Every theorem in RealWeights has only sorry and a source/proof docstring.
Every definition has actual data. The original dependency's proved
sfLocalCharacteristicFactor_existsUnique is preserved unchanged.

Edge cases checked mathematically before and during drafting: a zero representation
or stalk has polynomial 1 and empty eigenvalue multiset, hence vacuous purity and
upper bounds and true reality; multiplicities are zero. In rank one alpha=1 gives
weight 0, and alpha=q_x gives weight 2. A nonreal scalar fails reality while a
conjugate pair satisfies it. Jordan blocks retain their algebraic multiplicities.
For residue degree greater than one the denominator is log(q_x), not log(q).
Invertibility excludes zero eigenvalues and finite residue fields have q_x>1.
No edge case uses an embedding onto Complex. In the local-factor dependency,
different presentations and residue embeddings are compared by conjugacy; its
unique universal characterization is not a choice of an arbitrary stalk operator.
The empty-scheme constructible version is vacuous at closed points. The expression
is meaningful for independently sized coefficient closures and vector spaces.

Searches actually run (recorded by msearch.py in searches.jsonl):

* leanfinder: "Local Frobenius polynomial logarithmic weights punctual purity reality
  Weil sheaves"; eight hits on arithmetic Frobenius, Witt vectors and pretilts,
  none giving this Weil-sheaf interface.
* loogle: "AlgebraicGeometry.WeilGroup.localPolynomial,
  AlgebraicGeometry.FrobeniusModule.IsReal"; zero hits, with the explicit diagnostic
  unknown identifier AlgebraicGeometry.WeilGroup.localPolynomial. This service
  does not index the project declaration; it was located by the source searches.
* grep: "frobeniusWeight|IsPunctuallyPure|localPolynomial"; two hits, both the
  unrelated elliptic-curve local polynomial and its use in LFunction.lean.
* leansearch: "Local Frobenius eigenvalues logarithmic weights real Weil sheaves";
  eight unrelated Witt-vector, isocrystal, height and sieve hits.
* rg and the requested node-id grep over lean/WeilConjectures found the existing
  RealSheaves/Weights.lean definitions and Operations.lean reality lemmas; read
  their complete signatures and docstrings. Source searches also found the generic
  FrobeniusModule definitions, which concern a single operator rather than this
  arbitrary-closure Weil representation and the common-stage constructible heart.
* rg over lean/Sheaf found RealWeilSheaves, RealSheavesSetup, AdicPunctualWeights,
  and CommonStageLocallyFree. DAG search found the existing def-wf-iota-real record.
  The quarantined Q106/G5 module is the existing owner of the canonical
  constructible factor. It is not recreated or delivered in this repair.
* scompile.py --source Sheaf.Paper.AdicLocalCharacteristicFactor returned
  "Module source unavailable". The source of AdicLocalFrobeniusModelConjugacy was
  also unavailable. The presentation-independence argument is retained in the
  named theorem's proof docstring, with that existing DAG lemma as its input.

The original two-file packet passed its initial dry run, but that result does not
validate this repair: the original packet incorrectly recreated a quarantined module.
The repaired one-file packet must compile against the restored original dependency.
No lake/global build was run. There is no statement correction or unresolved dispute.

## Returned delivery repair

The return on immutable head ded644f6e20a identified H13+H2. Removed the sandbox
AdicLocalCharacteristicFactor.lean and def-wf-iota-real.json entirely; restored the
item's stmt_deps to current main, removing the added def-wf-iota-real edge. The
item's only node change is now lean. RealWeights.lean is retained unchanged,
including its imports and use of the original sfLocalCharacteristicFactor and
SfIsReal. This delivery neither overwrites Q106's record nor replaces G5's proved
sfLocalCharacteristicFactor_existsUnique with sorry, and does not modify the
finite-stage signature, SfIsReal or SfIsRealizable.

Read the quarantined original module and tools/rework.py rules 2–4. The module is
still quarantined (coord/rework.tsv); the prescribed live-source reader reports
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor". The original
imports ImmersionWeilLocalBehavior and AdicLocalFrobeniusModelConjugacy, themselves
still quarantined. Rule 2 requires restoring these prerequisites first; rule 3
requires restoration via the rework landing, rather than a stage-2 recreation.
The separate maintainer advisory about changing SfIsRealizable to IsCommonStageLisse
belongs after that restore with a change record; this delivery does not touch that
unrelated predicate. The item does not use SfIsRealizable.

## Repair validation

Self-check: the repaired item node differs from current main only in lean;
stmt_deps is identical. The packet contains one Lean file, RealWeights.lean,
and no dependency node or dependency module. The returned head's unwanted
local-factor rewrite is removed rather than rebased or pushed unchanged.

The prescribed scompile.py invocation for the retained module fails locally and
in SERVER CONFIRMATION at its import: "object file .../Sheaf/Paper/
AdicLocalCharacteristicFactor.olean ... does not exist". The repaired deliver2.py
--no-push repeats the same server-confirmed failure and prints "COMPILE FAILED on
the server, nothing pushed". Its source reader independently reports "Module source
unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor". The dependency is absent
at its original path and remains present at its quarantined path. Thus this is
the exact restoration prerequisite specified in the return, not an interface
mismatch to repair by recreating it. No delivery was pushed. The stage-2 wrapper
has no rework-restoration operation; restoring through that item's normal rework
landing (with its prerequisites) is required before this retained packet can pass.

## Repair retry 2026-10-21T14:01:45Z

Inspected the retained packet first and ran the prescribed deliver2.py Q10
sk-d-real-weights --no-push before making any change. It again exited 1:
"COMPILE FAILED on the server, nothing pushed", with SERVER CONFIRMATION that
Sheaf/Paper/AdicLocalCharacteristicFactor.olean does not exist. A separate
scompile.py Q10 sk-d-real-weights invocation for RealWeights.lean reproduced the
same server-confirmed missing-object-file diagnostic (1.3 seconds, no timeout).
scompile.py --source Sheaf.Paper.AdicLocalCharacteristicFactor exited 1 with
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".

Compared the retained node with the current shared node without Git: only lean
differs; stmt_deps is identical. The packet still has exactly RealWeights.lean
and sk-d-real-weights.json. The rejected dependency module and dependency record
are absent. Confirmed that the original sources of AdicLocalCharacteristicFactor,
AdicLocalFrobeniusModelConjugacy and ImmersionWeilLocalBehavior are absent from
lean/ and present in quarantine/. The first imports both other modules. Their
rows remain in coord/rework.tsv. Read the rework rules again: rule 2 requires
bottom-up prerequisite restoration; rule 3 requires the rework landing; rule 4
holds consumers. This stage-2 packet cannot restore those modules through its
permitted module/node inventory, and recreating them is explicitly rejected by
the return. No Lean or DAG changes were needed or made during this retry, and
no push was attempted after the failed dry run. The packet is retained pending
the required rework restoration; the SfIsRealizable advisory remains deferred
as instructed in the return.

## Repair retry 2026-10-21T14:09:08Z

Read the retained report first and ran deliver2.py Q10 sk-d-real-weights
--no-push on the saved packet before changing anything. The wrapper exited 1
with "COMPILE FAILED on the server, nothing pushed". Both LOCAL COMPILE and
SERVER CONFIRMATION report that the object file for
Sheaf.Paper.AdicLocalCharacteristicFactor does not exist. The independent
scompile.py Q10 sk-d-real-weights invocation reproduces the missing-import
failure. The prescribed scompile.py --source reader exits 1 with
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".

Compared the retained node against current shared source by JSON field: only
lean differs. The saved packet contains exactly RealWeights.lean and the
item's node file; the rejected dependency module and dependency record are absent.
The original AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy and
ImmersionWeilLocalBehavior sources are absent under lean/ and remain under
quarantine/; all three remain listed in coord/rework.tsv. Re-read rules 2–4 in
tools/rework.py and the immutable-head return: prerequisite restoration must
proceed bottom-up through rework landing, and recreating the dependency through
this stage-2 delivery is expressly rejected. Therefore there is no authorized
Lean/interface rewrite to apply to this packet for the current missing-source
diagnostic. No live source, launcher tool, dependency record, or Lean declaration
was modified. No push was attempted. The SfIsRealizable advisory remains deferred
until restoration, as the return requests; this item does not use that predicate.

## Repair retry 2026-10-21T14:15:18Z

Inspected report.md and ran the required saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed"; both LOCAL COMPILE and
SERVER CONFIRMATION report missing AdicLocalCharacteristicFactor.olean.
An independent prescribed scompile.py invocation for RealWeights.lean also
exited 1 with the same server-confirmed missing import (1.3 seconds on server).
The source reader reports "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor". These are not busy-server timeouts.

Compared the saved node with current shared main by JSON fields: only lean
differs. The packet still contains exactly RealWeights.lean and the item's
node; no rejected dependency module or dependency node record is present.
Confirmed that AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy
and ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. The original local-factor module imports both
other quarantined modules. Re-read tools/rework.py rules 2–4: restoration is
bottom-up through rework landing, and ordinary consumers are held until restored.
The immutable-head return expressly forbids recreating the dependency through
this stage-2 packet. Therefore the saved repair remains retained, with no Lean
or node changes and no push. The SfIsRealizable advisory remains deferred until
the required restoration; this item does not use that predicate.

## Repair retry 2026-10-21T14:19:18Z

Inspected the retained report and ran the required saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". Both local compilation and
SERVER CONFIRMATION report missing AdicLocalCharacteristicFactor.olean.
The independent prescribed scompile.py invocation for RealWeights.lean also
exited 1 with that server-confirmed import failure (1.3 seconds on server).
The prescribed source reader exited 1 with "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor". No busy-server timeout occurred.

Compared the packet node with current shared source by JSON field: only lean
differs, and stmt_deps is identical. The packet contains only RealWeights.lean
and the item node; the rejected dependency module and node record are absent.
AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy and
ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. The original local-factor module imports both
other quarantined modules. Rework rules 2–4 and the immutable-head return
require bottom-up restoration through the rework landing before this consumer
can compile; recreating the dependency in this packet is expressly rejected.
No authorized source/interface repair addresses the current unavailable-module
diagnostic. Retained all Lean and DAG content unchanged and did not push.
The SfIsRealizable advisory remains deferred until restoration, as requested.

## Repair retry 2026-10-21T14:28:24Z

Read the retained report and ran the prescribed saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". LOCAL COMPILE and SERVER
CONFIRMATION both report missing AdicLocalCharacteristicFactor.olean.
An independent `scompile.py Q10 sk-d-real-weights` check of RealWeights.lean
reproduced the same server-confirmed missing import (1.3 seconds on server).
`scompile.py --source Sheaf.Paper.AdicLocalCharacteristicFactor` exited 1:
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".
These failures are not busy-server timeouts.

Compared the saved node against the current shared node by JSON field: only
lean differs, and stmt_deps is identical. The packet contains only the item's
RealWeights.lean and node file; the rejected dependency module and dependency
record remain absent. The original AdicLocalCharacteristicFactor,
AdicLocalFrobeniusModelConjugacy and ImmersionWeilLocalBehavior sources remain
absent from lean/, present in quarantine/, and listed in coord/rework.tsv.
Re-read tools/rework.py rules 2–4: restoration must proceed bottom-up through
normal rework landing before consumers resume. The immutable-head return
expressly rejects recreating this dependency in the stage-2 packet. Therefore
no authorized packet repair resolves this current compilation-service failure.
Retained all Lean and DAG content unchanged; did not push. The SfIsRealizable
advisory remains deferred until restoration, as the return specifies.

## Repair retry 2026-10-21T14:31:30Z

Read the retained report and ran the saved-packet dry run before changes.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed"; LOCAL COMPILE and SERVER
CONFIRMATION both report missing AdicLocalCharacteristicFactor.olean.
The independent prescribed scompile.py check reproduces that missing import.
The prescribed source reader exits 1 with "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor". These are not busy-server timeouts.

Compared the saved node with the current shared node: only lean differs;
stmt_deps is identical. The packet contains only RealWeights.lean and the item
node. The rejected dependency module and record remain absent. The original
AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy, and
ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. Rules 2–4 in tools/rework.py require bottom-up
restoration through the rework landing before consumer work resumes. The return
expressly forbids recreating the dependency through this stage-2 packet.
Retained all Lean and DAG content unchanged and did not push. The advisory
SfIsRealizable change remains deferred until restoration as requested.

## Repair retry 2026-10-21T14:41:10Z

Read the saved report and ran deliver2.py Q10 sk-d-real-weights --no-push
before any edit. It exited 1 with "COMPILE FAILED on the server, nothing pushed".
LOCAL COMPILE and SERVER CONFIRMATION both report that the object file for
Sheaf.Paper.AdicLocalCharacteristicFactor does not exist. The independent
prescribed scompile.py invocation for RealWeights.lean reproduces that exact
server-confirmed failure (1.3 seconds on server, not a busy-server timeout).
The prescribed --source reader exits 1 with "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor".

Compared the saved packet to current shared main without Git: only the item's
lean field differs; stmt_deps is identical. The packet contains exactly
RealWeights.lean and sk-d-real-weights.json, with no rejected dependency module
or dependency node record. Confirmed that AdicLocalCharacteristicFactor,
AdicLocalFrobeniusModelConjugacy, and ImmersionWeilLocalBehavior remain absent
from lean/, present in quarantine/, and listed in coord/rework.tsv. The original
local-factor module imports the latter two. Re-read tools/rework.py rules 2–4:
prerequisites must be restored bottom-up through the rework landing; normal
consumers are held meanwhile. The return expressly forbids recreating this
module in the stage-2 packet, so this dispatch cannot repair the missing module
through its authorized delivery. Retained all Lean and DAG content unchanged,
and did not push. The SfIsRealizable advisory remains deferred until restoration,
as the return requests; this item does not use that predicate.

## Repair retry 2026-10-21T14:51:14Z

Read the retained report first and ran the required saved-packet dry run before
any edit. `deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". LOCAL COMPILE and SERVER
CONFIRMATION report missing Sheaf.Paper.AdicLocalCharacteristicFactor.olean
(server check 1.4 seconds). The independent prescribed scompile.py check of
RealWeights.lean reproduces the same import failure. The prescribed source
reader exits 1: "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor". There was no busy-server timeout.

Self-check against current shared main without Git: only the item's lean field
differs; stmt_deps is identical. The packet contains exactly RealWeights.lean
and the item node. H13+H2 repair remains in place: the rejected dependency
module and dependency record are absent, and the original local-factor API and
proved existence/uniqueness theorem are not overwritten. All three original
modules AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy and
ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. Re-read tools/rework.py rules 2–4: restoration
proceeds through rework landing with its prerequisites; normal consumers are
held meanwhile. The immutable-head return explicitly forbids recreating the
module in this stage-2 packet. No authorized packet/interface edit can supply
this unavailable dependency without violating that return. Retained all Lean
and DAG content unchanged and did not push. The SfIsRealizable advisory stays
deferred until restoration, as requested; this item does not use it.

## Repair retry 2026-10-21T14:57:35Z

Inspected the retained report and ran the required saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". LOCAL COMPILE and SERVER
CONFIRMATION both report missing AdicLocalCharacteristicFactor.olean
(server confirmation 1.7 seconds). The independent prescribed scompile.py
invocation for RealWeights.lean also fails on that missing import. The prescribed
source reader exits 1 with "Module source unavailable:
Sheaf.Paper.AdicLocalCharacteristicFactor". These failures are not timeouts.

Self-check against current shared main without Git: only the item's lean field
differs; stmt_deps is identical. The packet contains only RealWeights.lean and
the item node. The H13+H2 repair remains in place: the rejected dependency module
and dependency record are absent, with no overwrite of the original local-factor
API or proved existence/uniqueness theorem. AdicLocalCharacteristicFactor,
AdicLocalFrobeniusModelConjugacy and ImmersionWeilLocalBehavior remain absent
from lean/, present in quarantine/, and listed in coord/rework.tsv.

Re-read tools/rework.py rules 2–4 and the immutable-head return: the dependency
must be restored through its rework landing with its prerequisites. Recreating
it in this stage-2 delivery is expressly forbidden. The SfIsRealizable advisory
is conditional on restoration and remains deferred; this item does not use it.
No authorized packet repair resolves the current missing-source diagnostic.
Retained Lean and DAG content unchanged and did not push.

## Repair retry 2026-10-21T15:08:43Z

Read the retained report and ran the required saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". LOCAL COMPILE and SERVER
CONFIRMATION both report missing AdicLocalCharacteristicFactor.olean.
The independent prescribed scompile.py invocation also fails at that import;
`--source Sheaf.Paper.AdicLocalCharacteristicFactor` exits 1 with
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".
These are missing-dependency failures, not busy-server timeouts.

Self-check against current shared main without Git: only the item's lean field
differs; stmt_deps is identical. Exactly one Lean module and one node are in
the packet. The rejected dependency module and record remain absent, preserving
the landed sfLocalCharacteristicFactor/SfIsReal API and the proved uniqueness
theorem. The dependency and AdicLocalFrobeniusModelConjugacy and
ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. Read the original imports and rework rules 2–4:
bottom-up restoration must land through rework before this consumer resumes.
The return explicitly forbids recreating the dependency in this stage-2 packet;
the prescribed stage-2 wrappers provide no rework restoration operation.
No Lean or DAG changes or push were made. The SfIsRealizable advisory remains
conditional on restoration and is outside the retained item's declarations.

## Repair retry 2026-10-21T15:14:23Z

Read the retained report and ran the prescribed saved-packet deliver2.py dry run
first. It exited 1: "COMPILE FAILED on the server, nothing pushed". Local
compilation and SERVER CONFIRMATION both report that
Sheaf.Paper.AdicLocalCharacteristicFactor.olean does not exist. An independent
scompile.py invocation for RealWeights.lean reproduces that import failure
(server check 1.3 seconds); the prescribed --source reader exits 1 with
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".
This is not a busy-server timeout.

Current shared-source comparison without Git confirms that only the item's lean
field differs and stmt_deps is identical. The packet contains exactly
RealWeights.lean and the item node, with no rejected dependency module or record.
AdicLocalCharacteristicFactor, AdicLocalFrobeniusModelConjugacy and
ImmersionWeilLocalBehavior remain absent from lean/, present in quarantine/,
and listed in coord/rework.tsv. Rework rules 2–4 require bottom-up restoration
through a rework landing and hold normal consumers meanwhile. The return expressly
forbids recreating this dependency in the stage-2 packet. No authorized packet
repair resolves this unavailable-module diagnostic. Lean and DAG content were
retained unchanged; no push was attempted. The SfIsRealizable advisory remains
conditional on restoration, as instructed.

## Repair retry 2026-10-21T15:23:03Z

Read the retained report and ran the prescribed saved-packet dry run first.
`deliver2.py Q10 sk-d-real-weights --no-push` exited 1 with
"COMPILE FAILED on the server, nothing pushed". LOCAL COMPILE and SERVER
CONFIRMATION both report that AdicLocalCharacteristicFactor.olean does not exist.
The separate prescribed scompile.py invocation reproduces this missing import;
`--source Sheaf.Paper.AdicLocalCharacteristicFactor` exits 1 with
"Module source unavailable: Sheaf.Paper.AdicLocalCharacteristicFactor".
These are missing-source failures, not busy-server timeouts.

Compared the retained packet with current shared source without Git: only the
item's lean field differs; stmt_deps is identical. Exactly one Lean file and
one node file remain. The rejected dependency rewrite and record are absent.
The original AdicLocalCharacteristicFactor and its prerequisites
AdicLocalFrobeniusModelConjugacy and ImmersionWeilLocalBehavior are absent from
lean/, present in quarantine/, and listed in coord/rework.tsv. Read the original
module imports and tools/rework.py rules 2–4: restoration proceeds bottom-up
through rework landing before normal consumers resume. The immutable-head return
expressly forbids recreating this dependency in this stage-2 packet. The
SfIsRealizable advisory is conditional on restoration; this item does not use it.
No authorized packet edit resolves the unavailable original module. Retained
all Lean and DAG content unchanged and did not push.

## Second reading by Q10

Repair retry 2026-10-21T15:37Z. Re-read the saved RealWeights module, current
item and dependency node records, current blueprint definition, and upstream
weight and punctual-eigenvalue declarations. The local determinant uses
charpolyRev, eigenvalues use charpoly.roots with multiplicities, and the imported
frobeniusWeight is exactly twice the logarithmic complex norm divided by the
logarithmic residue cardinality. Purity and upper bounds quantify over every
closed point and eigenvalue. Coefficientwise conjugation renders polynomial
reality; both equivalence theorems retain multiset multiplicities. Constructible
clauses use the recorded common-stage stalk convention without a lissity or
mixed-filtration hypothesis. The spectral and representation reality theorems
explicitly retain IsAlgClosed E; the definitions specialize to the chosen closure.
Independent universes remain explicit. Zero-dimensional representations and zero
stalks give polynomial 1 and empty spectra; conjugate pairs and residue degrees
greater than one retain the stated meaning. No Lean change was needed.

Confirmed the returned H13+H2 correction: the packet has just RealWeights.lean
and sk-d-real-weights.json; the rejected dependency module and dependency node
record are absent. Compared current shared node fields: only lean differs,
including no extra def-wf-iota-real dependency edge. The current server source
reader now supplies the original AdicLocalCharacteristicFactor module, including
the proved sfLocalCharacteristicFactor_existsUnique and the original
sfLocalCharacteristicFactor and SfIsReal. These declarations are imported
unchanged. The advisory SfIsRealizable adjustment is not part of this item:
RealWeights does not use SfIsRealizable and this packet does not edit its owner.

## Successful repair validation

The first saved-packet dry run still reported the missing local-factor object.
The subsequent prescribed server source read succeeded. The separate scompile.py
check then compiled the restored server dependency overlays
ImmersionWeilPullbackLocalBehavior, AdicLocalFrobeniusModelConjugacy and
AdicLocalCharacteristicFactor, followed by the sandbox and library RealWeights
module, with exit 0 and no unexpected warnings. The next prescribed deliver2.py
--no-push returned "OK (dry run): commit f57080b0647 passes the preflight and
compiles; nothing pushed". Earlier unavailable-source entries above are historical;
the current successful check resolves that prerequisite. No dependency source,
proof, or record is supplied or overwritten by this delivery. No global build
or direct Git command was run.

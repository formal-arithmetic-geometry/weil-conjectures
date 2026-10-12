## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison`
by a compiling assembly of the actual five-step geometric argument. The existing
signature and docstring are unchanged. There are no definition or interface changes
in existing modules and no forced adaptations.

Added three modules, each with one public theorem and its own node:

- `ClosedQuotientFormalPresentation`: proved from the existing coherent-formal
  closed-immersion equivalence, coherent support formula, and proper-preimage theorem.
  The counit and pushforward comparison give the specified system isomorphism;
  stalk bijections and injectivity identify the pulled support. The empty quotient
  contradicts the prohibition of a proper closed support.
- `ChowPullbackAlgebraization`: leaves the projective-compactification and algebraization
  step open, with the actual tensor-pullback completion isomorphism in its conclusion.
- `ClosedImmersionFormalComparisonTransport`: leaves the closed-pushforward kernel,
  ideal-lifting, and proper-support transport open. It requires an actual comparison
  and a limiting kernel fork with termwise power annihilation.

The main proof uses the first theorem to descend M to V(K), checks the base-adic
ideal using `comap_comp`, obtains the Chow algebraization data, and applies the
EXISTING `exists_formalSystemsPushPull` to its specified beta. It passes the returned
coherence, alpha, positive exponent, limiting kernel fork and annihilation to the
transport theorem. `ker_subschemeι` finishes the strict inequality. The cokernel is
not needed by this comparison theorem.

Validation: all four modules compile together with lcompile.py in import order,
without compiler warnings. The main assembly also compiles individually. New Lean
lines are at most 100 characters. Existing public imports are preserved. The item
node's proof and proof dependencies now record this assembly, with the unchanged
unit route sk-thm-p1. No arbitrary existence witness is used to define data.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.grothendieckExistence_chow_comparison`
(node `lem-weil-pbc-grothendieck-existence-chow-comparison`).
No sorry remains in the item's module.

Additional complete proof from existing declarations:
`AlgebraicGeometry.exists_closedQuotientFormalPresentation`
(node `lem-weil-pbc-closed-quotient-formal-presentation`).

New holes, exactly two, each the whole proof of a public theorem:

- `AlgebraicGeometry.exists_chowPullbackAlgebraization`
  (node `lem-weil-pbc-chow-pullback-algebraization`).
- `AlgebraicGeometry.exists_closedImmersionFormalComparisonTransport`
  (node `lem-weil-pbc-closed-immersion-formal-comparison-transport`).

This is a decomposition, not a sorry-free proof of the geometric theorem:
one original hole closed, two new holes added, net -1 for these declarations.
The existing imported lemmas retain their own holes; they are not changed by this
delivery. Each new hole isolates a strictly separate part of the argument, with a
source and a complete natural-language proof in its docstring and node.

## No longer needed

No original geometric node or module is pruned from the full dependency route.
The main module removes these direct proof imports, moving their work to the
new intermediate nodes rather than discarding the geometric work:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective`
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`
- `WeilConjectures.AlgebraicGeometry.ChowLemma`

`FormalSystemsPushPull` stays directly imported and is applied in the main proof.
The direct proof dependencies of the original node are now the three intermediate
nodes, the push-pull theorem and the elementary ideal identities. The original
geometric dependencies are retained under the new nodes. The unused direct
`ClosedSubsetProperOverBaseProperties` import was removed from the proved presentation
module; its proof uses the proper-preimage theorem instead.

The earlier rejected core module and its two nodes remain only in scratchpad/rejected
and are excluded from the delivery. They are neither imported nor cited.

The old direct proof dependencies no longer directly used by the main theorem are:

- `def-nagata-scheme-theoretic-image` (retained under the new intermediate nodes).
- `def-weil-pbc-coherent-formal-module` (retained under the new intermediate nodes).
- `lem-weil-pbc-adic-complete-jacobson-radical` (retained under the new intermediate nodes).
- `lem-weil-pbc-chow-noetherian` (retained under the new intermediate nodes).
- `lem-weil-pbc-closed-immersion-coherent-equivalence` (retained under the new intermediate nodes).
- `lem-weil-pbc-closed-subset-proper-over-base-properties` (retained under the new intermediate nodes).
- `lem-weil-pbc-closed-subset-proper-over-base-union-preimage` (retained under the new intermediate nodes).
- `lem-weil-pbc-coherent-formal-modules-abelian` (retained under the new intermediate nodes).
- `lem-weil-pbc-formal-systems-pullback` (retained under the new intermediate nodes).
- `lem-weil-pbc-grothendieck-existence-projective` (retained under the new intermediate nodes).
- `lem-weil-pbc-module-support-proper-over-base` (retained under the new intermediate nodes).
- `lem-weil-pbc-pushforward-coherent-on-open` (retained under the new intermediate nodes).
- `lem-weil-pbc-reduced-induced-closed-subscheme` (retained under the new intermediate nodes).
- `lem-weil-pbc-support-pullback-finite-type` (retained under the new intermediate nodes).
- `lemma-nagata-immersion-open-in-scheme-image` (retained under the new intermediate nodes).
- `pqf-lem-locnoeth-lft` (retained under the new intermediate nodes).

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's arbitrary properly supported N, followed by a map theorem for
that N, is invalid. This repair has no such theorem. Its F is linked to the particular
Chow pullback by beta, and the existing push-pull theorem constructs alpha into the
completion of the corresponding pushforward. The new transport theorem takes that
actual alpha and its limiting kernel, not an arbitrary target. The first-support
properness and the base-adic equality Q = I O_Z are explicit hypotheses of the
algebraization step. No vacuous existence-of-N statement is used.

Repairs to the previous second reading's numbered findings:

1. Kept the existing signature and public imports unchanged; all new imports of the
   main module are private proof imports. No downstream adaptation is needed.
2. Compiled all four modules and the assembly. The only new direct sorry users are
   the two named split theorems; the proved presentation and main theorem use them
   or existing open declarations transitively.
3. Replaced both rejected splits with actual geometric data and kernel transport.
   The closed-quotient presentation itself is proved. Read the local Stacks source
   at Theorem grothendieck-existence (088E), including the compactification,
   Jacobson-radical/Nakayama argument and final push-pull step. Each open theorem
   now has the complete argument in words.
4. Kept the unit route and all its realized steps. Direct imports removed from the
   item are accounted for above and remain below the new nodes; no geometric work
   is claimed pruned.
5. Added complete nodes with actual statement and proof dependencies and verbatim
   Lean signatures. Searches of both library roots, Mathlib and the whole blueprint
   found no exact replacement for the new glue. LeanSearch was unavailable and is
   recorded as unavailable, without an absence verdict.

Edge checks: the presentation excludes an empty quotient by its proved contradiction.
For the algebraization step, the zero system can algebraize to zero but still retains
its required beta; a proper Z also satisfies the statement. I = 0 keeps the real
algebraization requirement, rather than giving an unrelated Q. If I is the unit ideal
in a complete ring, A is the zero ring and nonempty Z over Spec A is impossible.
For transport, the nonempty complement of L.support prevents L^t from being zero;
this remains true on a nonreduced quotient because its stalk is the unit ideal there.
Empty Z or L with full support cannot satisfy that hypothesis. A zero comparison to
zero is allowed only if its actual kernel meets the annihilation hypothesis; the
previous N=0 counterexample therefore supplies no false conclusion here. Positive t
and a limiting fork are retained explicitly.

## New nodes

`lem-weil-pbc-closed-quotient-formal-presentation`, module
`Sheaf.AlgebraicGeometry.ClosedQuotientFormalPresentation`: a proved closed-quotient
presentation and proper-support descent. Uses the actual inverse-equivalence object,
its counit and the natural pushforward comparison. No new hole.

`lem-weil-pbc-chow-pullback-algebraization`, module
`Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization`: the geometric compactification,
extension, projective algebraization and support calculation. Supplies precisely
q, L, F, beta and proper pushforward support required by the existing push-pull theorem.
One open theorem.

`lem-weil-pbc-closed-immersion-formal-comparison-transport`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionFormalComparisonTransport`: general closed
pushforward transport of an already constructed comparison with a power-annihilated
limiting kernel. Supplies the strictly larger inverse-image ideal and the proper
closed support of the pushed completion. One open theorem.

No change record is needed: no existing definition, signature or visibility changes.

## Second reading by U2

1. PASS. Diffed the existing module against the repository and compared the raw
   signature substring through `:=`: byte-for-byte unchanged. Its original public
   imports, docstring and visibility are unchanged. Only its proof and private proof
   imports differ; the other three modules are new. No existing definitions change.
2. PASS with declared open dependencies. Independently compiled all four modules in
   import order with lcompile.py, without errors or warnings. Scanned their source for
   forbidden declarations and hidden holes. Exactly the two reported new public
   theorems have `sorry`, each as its whole proof; no definition is introduced. A fresh
   scratch module printed axioms of all four delivered declarations: only propext,
   Classical.choice, Quot.sound and sorryAx. The presentation's sorryAx is inherited
   from the existing equivalence/support dependencies. This is a decomposition, not
   a completed geometric proof. No arbitrary existence witness supplies defined data.
3. PASS. Read both open statements, their docstrings and nodes against Stacks 088E
   (https://stacks.math.columbia.edu/tag/088E). The algebraization split supplies beta
   for the specific tensor pullback; the transport split requires the actual map and
   its limiting kernel killed by L^t. Neither is a renamed copy of the item. Checked
   zero systems, I=0, empty quotients, nonreduced quotients and L with full support.
   On the nonempty complementary open L^t is the unit ideal, ensuring strictness;
   a zero comparison cannot evade the stated kernel annihilation. Independent
   LeanFinder search for coherent algebraization after proper modification returned
   unrelated affine-limit/localization lemmas; Loogle Ideal.comap returned useful
   ring ideal identities, but no formal-system transport. Searched both library
   roots with alternate terms and read ClosedSupportedFormalAlgebraization and
   GrothendieckExistenceSupportedSystem: both require a fixed supported algebraization
   hypothesis unavailable here. Neither open split can be closed by a short application.
4. PASS. The main proof actually applies the existing FormalSystemsPushPull theorem
   to beta and carries its limiting kernel and exponent into transport. All removed
   direct imports and old direct node dependencies are now individually listed under
   No longer needed; they remain in the refined route, so no module is claimed pruned.
   Read sk-thm-p1.realized: none of its realized statement/step nodes is bypassed or
   modified. Existing public imports are needed by signatures; new proof imports
   are private. The proved presentation has no unused proof import.
5. PASS after a node-text repair. Each proof_deps equals the union of its proof
   steps' uses. The existing node changes only proof, proof_deps and proof_origin.
   New nodes have sources, searches, provenance, blueprint links and matching Lean
   signatures. Traced the presentation's equivalence/counit, stalk bijections, proper
   preimage and empty-source contradiction, and the main assembly, against those
   records. Corrected the algebraization node's first step from undefined V(K) to
   its actual scheme Z.

Second reading changed no Lean proof or signature. It corrected that stale node
reference, made the removed direct node dependencies explicit in the report, and
replaced the stale rejected-core axiom scratch file by checks of the current delivery.

## What changed

Constructed the integral natural isomorphism in
`Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms` by composing the actual
whole-system coefficient exchange with the fixed source and target
`compactRealization` isomorphisms. Lifted this natural transformation into the
full constructible subcategory and used componentwise invertibility to obtain
`b`. Its ambient component equation is definitional. Applied the separate finite
normalization lemma and the proved rational-localization lemma to finish the
original existential statement, without changing any existing signature or definition.

Added three modules, one per new node. `CompactSupportRationalScalarIso` proves
rational naturality by tensor induction, including the literal endpoint transports
specified by rational scalar extension. Its private helpers are completely proved.
`CompactSupportCoefficientExchangeInvertible` and
`CompactSupportFiniteScalarMateNormalization` state the two remaining steps.
The former concerns only invertibility of the existing middle exchange; the latter
concerns only normalization of a given comparison and assumes its actual system-map
formula. Neither asserts the existence-and-normalization conclusion of the item.

The unit `sk-def-sf-operations` has empty `realized.statement` and `realized.steps`;
its operations and compactification route are retained. The new-node arguments are
exactly the original plan's steps 2--4, 1 and 5, and 6, respectively.

## Proved and sorry left

Closed the original body hole in
`WeilConjectures.sfCompactSupportNormalizedScalarIsomorphisms`
(node `lem-weil-compact-support-normalized-scalar-isomorphisms`) by a complete
assembly from the following strictly smaller steps. This is a decomposition,
not a net hole reduction.

Proved `WeilConjectures.sfCompactSupportRationalScalarIso`
(node `lem-sf-compact-support-rational-scalar-iso`), including localization of
inverse components, naturality for all Hom tensors, and the required HEq formula.

Added exactly two holes, both public named theorems with proof exactly `by sorry`:

- `WeilConjectures.sfCompactSupportCoefficientExchange_isIso`
  (`lem-sf-compact-support-coefficient-exchange-invertible`).
- `WeilConjectures.sfCompactSupportFiniteScalarMateNormalization`
  (`lem-sf-compact-support-finite-scalar-mate-normalization`).

There are no holes in the item module, rational-localization module, private
helpers or definitions. Original holes closed: 1; new holes: 2; net: -1.
Server checks: all three new modules and the assembled item compile within the
server limit. The rational calculation is first carried out for abstract finite
coefficient fields by the proved private helper `rationalScalarIsoOfFields`; this
avoids elaboration expanding the universe-normalized coefficient representation.
The required initial `deliver3.py S7
Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms` check was rerun against
current shared sources on 2026-10-25. It exited with `PREFLIGHT FAILED, nothing
pushed`, reporting exactly three errors: each of the three new helper edges is
said to introduce a DAG cycle. The two split-off holes were explicitly advisory,
not a refusal. The retained Lean and node work was not changed in this session.

The resumed worker repeated the required delivery check on 2026-10-25 and
independently reproduced all three cycle errors against the current shared DAG.
The current shortest base cycle starts through
`def-weil-integral-rational-qbar-compact-support` and
`lem-qcqs-compact-support-finite-comparison`, then follows the purity/Frobenius
return path recorded below. Each helper is absent from the base DAG, so
`reaches(base_graph, helper, item)` at `tools/stage3_delivery.py:592` is false.
The existing item still changes only `proof`, `proof_deps`, and `proof_origin`.
No delivery was pushed. This is the same reproducible gate failure, rather than
a compile timeout or a refusal of the two split-off theorem holes.

A fresh breadth-first traversal of the unmodified shared node JSON independently
verified the existing cycle displayed below, using
`lem-qcqs-compact-support-finite-comparison` as the return from
`def-weil-integral-rational-qbar-compact-support`. It also verified the genuine
return path from each new helper to the assigned node. All three helper ids are
absent from the base DAG. The existing item node changes only `proof`,
`proof_deps`, and `proof_origin`.

The current `edge_fails` implementation in `tools/stage3_delivery.py` requires
both directions of reachability in `base_graph` to exempt an existing cycle.
Since a new helper is absent from that graph, the exemption cannot recognize
these subdivisions of the existing cyclic dependency. Removing the genuine
statement dependencies would falsify the records. The launcher and delivery
scripts are not editable by this worker. A maintainer correction of the shared
DAG or gate is required; all four Lean modules and their nodes are retained.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Paper.CoefficientExtensionReductionModel`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.Paper.FiniteCompactSupportScalarTransport`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Paper.CompactSupportReductionTower`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.ScalarLocalization`.
- `Sheaf.Paper.SfRationalizationKaroubi`.

These imports are replaced by the three step modules. Their mathematical content
is still needed in the two remaining steps and is retained in those nodes' proof
plans; this delivery does not claim that any of these modules is globally pruned.
The scalar-localization and rationalization declarations are used by the proved
rational step. All four existing public imports remain verbatim.
No declaration or module is withdrawn, and no original mathematical dependency
is asserted unnecessary across the complete argument.

## Where the brief, the DAG or earlier work was wrong

No statement repair. The six-step DAG describes the correct mathematical route,
but its existing declarations do not directly expose either invertibility of the
particular realized proper/open coefficient exchange or its finite mixed-unit
normalization. Those two connections are now separately stated with their complete
source-based proofs in words. The downstream module
`CompactSupportSystemTransposeNormalization` imports the assigned item, and the
import-direction tool explicitly rejects importing it back. The existing
`integralCoefficientComparison` has a finite-field base and finite-Tor domain,
so it does not close this general comparison. A source-only traversal also found
pre-existing DAG cycles below the item
(e.g. via the compact-support definition, purity conventions and Frobenius
cohomology transport); no such global nodes are edited here. The Lean import
assembly compiles. The delivery gate nevertheless rejects each new step edge with
`proof_deps gains ..., which introduces a DAG cycle`. A traversal of the completely
unmodified shared repository confirms this full cycle already exists:

`lem-weil-compact-support-normalized-scalar-isomorphisms` ->
`def-weil-integral-rational-qbar-compact-support` ->
`lem-qcqs-compact-support-normalized-lift` ->
`lem-pur-compact-support-integral-coefficient-comparison` ->
`def-pur-conventions` -> `lem-pur-twist-frobenius-scalar` ->
`def-weil-frobenius-cohomology-transport` ->
`def-weil-frobenius-square-exchange` ->
`def-zl-weil-compact-support-cohomology` ->
`lem-weil-compact-support-finite-field-independence` ->
`lem-weil-compact-support-normalized-scalar-isomorphisms`.

The new statements refer to the existing compact-support action definitions and
therefore encounter this old cycle. Removing those definition dependencies from
their nodes would conceal genuine dependencies. No node outside the assigned
proof route or launcher/preflight script was modified to bypass this gate.
The maintainer must reconcile the existing cycle or adjust how preflight treats it.
The current `edge_fails` implementation in `tools/stage3_delivery.py` compares
each new helper against `base_graph`. Since a new node has no outgoing edges in
that graph, its exemption for a pre-existing strongly connected component cannot
apply. Even the fully proved rational step returns through its necessary
`def-weil-compact-support-finite-action` dependency and the old cycle. This is
not a Lean import cycle or an unproved rationalization obligation. Removing the
new nodes or their genuine dependencies solely to evade the gate would make
the delivery records false; no such workaround was attempted.

Current-session verification (2026-10-25): the required initial delivery command
again exited 1 with exactly the three cycle errors, and nothing was pushed.
An independent breadth-first traversal of the current shared JSON confirmed that
all three helper return paths join the existing item cycle. The shortest existing
return uses `lem-qcqs-compact-support-finite-comparison`, rather than the alternate
`lem-qcqs-compact-support-normalized-lift` route displayed above. The base item
already has `def-weil-integral-rational-qbar-compact-support` as a direct dependency.
Only `proof`, `proof_deps`, and `proof_origin` differ in the existing item node.
The gate's `edge_fails` exemption requires reachability from each helper in the
base graph, where none of the three helper ids exists. Thus its documented
exemption for pre-existing cycles cannot apply to this decomposition. No scripts,
shared sources, mathematical dependencies, or retained Lean files were changed.
The packet still has exactly two `by sorry` theorem bodies and no item-body hole.

Checked edge cases of the split: identity inclusion and zero input reduce to the
usual unit and zero comparisons; empty schemes have the same categorical
construction. At exponent one with a ramified inclusion, no finite quotient map
is assumed flat or injective. Constructibility of the completed scalar extension
and exact faithful etale/pro-etale pullback supply boundedness of its etale
antecedent. The Hom bijection in normalization still quantifies over every derived
target, with no boundedness hypothesis. The rational step assumes only an integral
natural isomorphism and therefore applies independently of either remaining hole.

## New nodes

`lem-sf-compact-support-coefficient-exchange-invertible`:
`Sheaf.Paper.CompactSupportCoefficientExchangeInvertible`, original proof steps
2--4, finite transport plus system conservativity and realization.

`lem-sf-compact-support-finite-scalar-mate-normalization`:
`Sheaf.Paper.CompactSupportFiniteScalarMateNormalization`, original proof steps
1 and 5, the mixed-unit Hom bijection and the actual system-map reduction equation.

`lem-sf-compact-support-rational-scalar-iso`:
`Sheaf.Paper.CompactSupportRationalScalarIso`, original proof step 6, now proved
by localizing components and using pure-tensor naturality.

No change record is needed: existing definitions, statements, visibility and
public imports are unchanged.

Resumption verification on 2026-10-25: the required initial delivery check again
ran server preflight and exited 1 with exactly the three cycle errors above.
An independent traversal of current shared node files confirmed the existing
cycle and all three helper return paths; the existing item still changes only
`proof`, `proof_deps`, and `proof_origin`. The packet still has zero holes in the
item and rational step, and one hole in each of the other two helpers. No Lean
or node files were changed, no fresh compile result is claimed, and nothing was
pushed. The worker cannot repair `tools/stage3_delivery.py` under the read-only
repository and launcher-tool rules. The gate must recognize a decomposition
through the existing cyclic component, or the maintainer must reconcile that
component; removing genuine dependencies would make this packet inaccurate.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

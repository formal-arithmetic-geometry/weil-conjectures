## What changed

Partial proof delivery for `Sheaf.Paper.WeakSerreSupportedDerivedGeneration`.
The unrestricted theorem is not proved by this packet. During this session the
human removed this detour from the target routes; see the current-source audit
below. Its current signature is
unchanged, including the maintainer's concurrent removal of the all-continuous
algebraic-closure coefficient, recorded in
`coord/changes/L-coefficient-allcontinuous-removal.md`.

Added six proved public supporting results in the item module:

- `supportedImageHull_proetale_descent`: transports the existing chain-hull descent
  theorem to the tree-path hull used here.
- `supportedGeneration_heart_colimits`: the degree-zero inverse-image hull contains
  the generators and is closed under extensions, filtered colimits and coproducts.
- `indConstructible_mem_supported_derived_generation`: for arbitrary condensed
  commutative coefficients, filtered colimits of constructible modules belong to
  the supported hull in degree zero.
- `indFiniteHeart_mem_supported_derived_generation`: for the five coefficient
  families, filtered colimits of finite constructible complex hearts belong to
  that hull. This uses the existing supported finite-model image theorem.
- `finiteCoefficient_weakSerre_mem_supported_derived_generation`: the finite
  discrete coefficient branch over arbitrary qcqs schemes.
- `noetherian_weakSerre_mem_supported_derived_generation`: all five coefficient
  branches when the qcqs scheme is locally Noetherian.

Private proved helpers implement finite factoring-tree refinement, exact
open-closed localization, simultaneous refinement for images, the two short exact
sequences computing a complex's zeroth homology, and degree-zero filtered
colimits with common termwise lower bound zero. The simultaneous stratification
uses scheme fibre products, so both actual restriction maps factor through the
old strata. It does not infer factorization from inclusion of topological ranges.
Local irreducibility of the pullback functors prevents expensive unfolding;
comparison isomorphisms provide their API. The stratification intersection is
reduced explicitly only when establishing the common refinement.

The new module `Sheaf.Paper.SupportedModelHullComparison` proves
`supportedModelHullClass_iff` and `supportedModelHull_iff`. It converts paths to
chains and completes chains by complementary leaves, comparing the actual
extension functors by natural isomorphisms. The lower-bound clauses are identified
by `CochainComplex.isStrictlyGE_iff`. The descent transport uses this comparison
on the affine charts and the qcqs root. No new hole is added.

New public imports provide the finite-complex-heart presentation predicate and
the Noetherian scheme and weak-contractibility assumptions used in the new
signatures. Other imports are private proof imports. The generic private refinement and localization helpers
are imported with `import all`; no scalar-restriction theorem for the
finite-subextension-valued algebraic closure is used. The new arguments preserve
actual abelian images and homology and require no comparison with that ring.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. This packet is partial
progress, not a proof or a decomposition of the unrestricted theorem.

The six public declarations listed above, the two comparison declarations, and
every private helper have complete Lean proofs. The finite-model image and Noetherian heart closure inputs are
existing library statements, with their own nodes; any unfinished proofs of those
inputs are not new holes introduced by this delivery.

The sole remaining hole in the delivered module is
`AlgebraicGeometry.ProEtale.CondensedRing.weakSerre_mem_supported_derived_generation`,
node `lem-sfb-weak-serre-supported-derived-generation`. Its proof is exactly
`:= by sorry`. No new module or theorem with `sorry` is introduced. Its docstring
retains the complete existing plan and identifies the unresolved step precisely.

The missing step is relation resolution for arbitrary maps between objects
already obtained by weak Serre operations over an arbitrary qcqs scheme with
non-discrete coefficients. Images between two finite scalar local models only
supply the first relation step. The new finite-complex-heart result handles those
finite relations and filtered presentations, without asserting that the resulting
class is closed under arbitrary kernels on an arbitrary qcqs scheme.

## No longer needed

No file or declaration is withdrawn by this packet. The original two public
imports are retained; all additional proof imports are used.

The current target routes no longer need this item. The human's 2026-10-25
`coord/changes/L-weak-serre-detour-reroute.md` reroutes
`properLowerStar_uniformBound_ellAdic` and `refinementMap_isIso` through the
blueprint arguments. A fresh transitive import audit of the current source finds
this item in neither `Challenge.lean`'s 4,198-module closure nor
`TargetsCheck.lean`'s 15,579-module closure. This is a concurrent maintainer
pruning, not progress claimed for this packet.

Withdrawal of the item itself is not justified by that audit: its immediate
importer `Sheaf.Paper.ClosedTorsionRigiditySerreTransfer` still applies its
unrestricted theorem, and its reverse import cone contains 19 modules. The
corresponding DAG parent still cites this node. The maintainer's record says the
detour modules stay in the library. Their signatures and proofs are therefore
preserved; no `deleted.txt` is supplied. The new specializations do not replace
the unrestricted parent use.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief's claim that this item is reached from the targets became
stale during the session. The current human-authorized route replacement above
removes that need. No further theory below this unused detour is introduced.

The existing node already recognizes that the finite-model image theorem does
not resolve arbitrary iterated weak Serre relations. This delivery confirms that
distinction in Lean; triangle closure alone is insufficient to infer closure of
the inverse-image heart under arbitrary kernels and cokernels. The repaired
finite-complex-heart closure input requires local Noetherianity, which has not
been inferred from qcqs. I found no applicable existing declaration that removes
that assumption for topological coefficients, and no counterexample to the
unrestricted supported-hull statement is asserted here.

The shared source changed during this session. The human's coefficient-removal
record now drops `continuousMapRingObj (PadicAlgCl ℓ)` from this item's interface.
The packet was reconciled with that current source and preserves the existing
node's statement-change record. The image-generation and Noetherian closure
inputs were also updated to the same five-case tables during the session. The
proofs now pass the current five-case hypothesis directly; their signatures are
not changed by this delivery.

Edge cases are covered by the actual constructions: zero objects on empty
leaves, the root support path, finite zero scalar modules, zero coefficient
rings, arbitrary differentials, and filtered presentations indexed in universe
`u + 1`. No nonzero-ring, nonempty-scheme, finite scalar-entry, or Noetherian
assumption has been silently added to the arbitrary-qcqs results.

## New nodes

`lem-sfb-ind-constructible-supported-generation` records finite-tree generator
reconstruction followed by strict degree-zero filtered colimits. Its public
statement is fully proved for arbitrary condensed commutative coefficients.

`lem-sfb-ind-finite-heart-supported-generation` records simultaneous refinement
of constructible images, the two homology short exact sequences, and strict
filtered colimits. It is fully proved from the existing finite-model image input.

`lem-sfb-finite-coefficient-supported-generation` records the finite discrete
branch via the existing finite-coefficient Serre-to-ind-finite-heart comparison
and the preceding result. It is fully proved.

`lem-sfb-noetherian-supported-generation` records the local-Noetherian branch via
weak Serre minimality, existing Noetherian finite-heart closure, and the preceding
result. It is fully proved.

`lem-sfb-supported-generation-heart-colimits` records the generator, extension,
filtered-colimit and coproduct closure argument. It is fully proved for arbitrary
condensed commutative coefficients.

`lem-sfb-supported-model-hull-comparison` records the fully proved equivalence of
classes and hulls in the new comparison module.

`lem-sfb-supported-image-hull-proetale-descent` records the fully proved transport
of the existing descent obligation to the tree-path hull.

All seven nodes attach to proved declarations in the item or comparison module,
introduce no remaining proof obligation, and retain the original blueprint unit. The original
node's proof record distinguishes these completed subarguments from its remaining
relation-resolution step. There is no definition or statement repair and no new
change record.

Validation: the comparison module and item compile through `lcompile.py`; the
latest standalone item compile completed in 32.2 seconds. The full delivery
command performs the consumer, node and independent-reader checks.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

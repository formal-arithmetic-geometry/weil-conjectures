## What changed

Replaced the whole-proof sorry of `AlgebraicGeometry.mixedGlobalHom_baseChange_exchange`
with a reduction to the internal-Hom exchange and the Leray transport identity.
The existing statement, binders, visibility and two public imports remain identical.
Added proof-only imports of `MixedInternalHomBaseChangeExchange` and
`MixedGlobalSectionsBaseChangeMate`. Each new module states one strict part of the
argument. The internal identity takes no global-sections or module-category input;
the Leray identity takes an arbitrary sheaf morphism and has no internal-Hom input.
The new `mixedGlobalSections_baseChange_mate` is proved from the existing unit square,
so only the internal exchange is left as a new hole.
The private generic `globalMate_postcomp` and `globalMate_exchange` helpers use only
adjunction naturality, Leray naturality, functoriality and associativity. They adapt
the already proved single-universe glue in `GlobalHomBaseChangeExchange`.

## Proved and sorry left

Closed the original named hole `AlgebraicGeometry.mixedGlobalHom_baseChange_exchange`
(node `lem-sc-mixed-global-hom-base-change-exchange`) by decomposition. No sorry is
left in that module or its private helpers.

Added one named whole-proof hole:

- `AlgebraicGeometry.mixedInternalHom_baseChange_exchange`, node
  `lem-sc-mixed-internal-hom-base-change-exchange`.

`AlgebraicGeometry.mixedGlobalSections_baseChange_mate` (node
`lem-sc-mixed-global-sections-base-change-mate`) is proved from the existing
`AlgebraicGeometry.mixedSectionsBaseChange_unit_square` by adjunction/Leray
naturality, naturality of the scalar square, and cancellation. It adds no hole.

This is one upper hole closed and one lower hole added: a decomposition with
net zero holes, not a sorry-free proof or a positive net hole reduction.
Every new hole has its source,
complete proof in words and DAG node. No definitions or axioms were added.

Edge cases: both assertions allow arbitrary scheme morphisms, arbitrary unbounded
complexes, empty schemes and zero complexes. No perfectness, qcqs, flatness,
properness or base-change invertibility is used. The Leray transport permits a zero
morphism a; naturality makes both sides zero. In the internal exchange the two
base-change components occur in opposite Hom entries with the displayed variance.
Identity squares reduce to the pinned evaluation-mate comparisons. The internal
statement has only the sheaf localization universe w; the Leray and original
statements keep independent sheaf universe w and module universe wA.

Validation: the generic glue and the new arbitrary-map Leray transport compiled
through lcompile.py without warnings. All three sandbox modules compiled together.
The inherited unscoped heartbeat option caused a style warning and was removed.
The delivery dry run checks the final sources, axioms and metadata.

## No longer needed

No original imports or original proof-dependency modules can be pruned. The
normalized tensorator, evaluation-mate direct-image comparison, canonical
base-change map and normalized Leray are all still needed below the two partial
identities. The original dependency `lem-sc-mixed-hom-tensor-pullback-iso` is used
in the new internal-Hom node, and `def-pc-derived-base-change-map` is used in both
new nodes. They move below those nodes rather than being discarded.

The single-universe modules `GlobalHomBaseChangeExchange`,
`InternalHomBaseChangeExchange` and `GlobalSectionsBaseChangeMate` were read for
reuse but are not imported: their signatures use the single-universe comparison
choices and do not directly supply the independently localized mixed identities.
No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines two substantial coherence identities in one
paragraph. Its listed dependencies give the comparison constructions, not the
exchange or Leray square identity. This delivery separates those two steps and
provides the actual Lean naturality glue between them.

The retained attempt left both new identities sorry and its final bare application
triggered a compilation timeout. The final proof now explicitly expands only the
three global comparison definitions and functor composition, then applies the
generic naturality glue. No file was split to bypass the timeout and no definition
was changed. The repaired combined sandbox compilation passes the time limit.

The retained attempt left both new identities sorry. A newer existing declaration,
`AlgebraicGeometry.mixedSectionsBaseChange_unit_square` in
`MixedSectionsBaseChangeUnitSquare` supplies
the unit case of the Leray identity; naturality proves the full arbitrary-map
version without any new hole.

The old node has `blueprint.from.node` pointing to another created node; following
the counit-transport parent reaches the blueprint node `lem-sc-finite-duality`.
The new nodes record that ancestor explicitly. Existing non-owned blueprint fields
are unchanged.

The local compiled snapshot initially lacked `MixedGlobalHomAdjunctionIso` and
`MixedHomDirectImageComparison`; compilation resumed when the shared artifacts
arrived. No dependency sources were compiled into an unauthorized overlay.

The local literature files are absent. Read the cited Stacks pages online:
[0AA8](https://stacks.math.columbia.edu/tag/0AA8),
[08HY](https://stacks.math.columbia.edu/tag/08HY),
[08I3](https://stacks.math.columbia.edu/tag/08I3),
[079U](https://stacks.math.columbia.edu/tag/079U),
[0D5T](https://stacks.math.columbia.edu/tag/0D5T), and
[0B6I](https://stacks.math.columbia.edu/tag/0B6I).
The general internal exchange is an agent-written refinement of their canonical
comparison constructions, not a verbatim assertion of 0AA8's isomorphism theorem
(which assumes properness, affine bases and Tor independence). Its proof in words
uses only formal mate identities and coherence of the normalized tensorators.
LeanSearch returned HTTP 500; this is recorded as unavailable, not as absence.
LeanFinder and Mathlib grep found only generic or underived adjunction lemmas.
Repository and whole-blueprint searches found the single-universe analogues but
no statement for these fixed mixed comparisons.

## New nodes

`lem-sc-mixed-internal-hom-base-change-exchange`, in
`lean/Sheaf/AlgebraicGeometry/MixedInternalHomBaseChangeExchange.lean`: the exchange
identity in D(O_Y') before applying global sections, using the normalized mixed
tensorator and fixed evaluation-mate direct-image comparison. Its proof expands
evaluation, transposes base change, cancels counits and compares canonical tensor
paths on K-flat representatives.

`lem-sc-mixed-global-sections-base-change-mate`, in
`lean/Sheaf/AlgebraicGeometry/MixedGlobalSectionsBaseChangeMate.lean`: Leray
transports the canonical base-change mate of any sheaf morphism, with independent
localization universes and no Hom/tensor input. Its complete Lean proof uses the
existing unit-square statement, adjunction units, naturality and cancellation.
No change records or forced adaptations are needed.


## Second reading by A3

1. Compared the existing Lean module and node with the repository by diff. The
existing theorem signature and docstring, its public imports, and visibility are
byte-for-byte unchanged. Only proof bodies, private proof helpers and proof-only
imports are added. No definitions, change records or forced adaptations occur.
Restored the existing node's reviewed and reviewed_proof fields from the current
repository: the sandbox had carried stale landing identifiers and a stale note.
Other non-owned fields remain unchanged.

2. Read both generic helpers, the reduction and the arbitrary-map Leray proof.
The first helper is adjunction naturality in the codomain and Leray naturality;
the second substitutes the internal exchange and uses domain naturality.
The Leray proof cancels only the restricted Leray isomorphism, never base change.
The only source sorry is the named whole-proof internal exchange theorem, with
its matching node and complete proof docstring. No axiom, unsafe, opaque, extern,
implemented_by, hollow definition or arbitrary-witness construction was added.
Local compilation and axiom checks are recorded in scratch/second-compile.log
and scratch/second-axioms.log; the delivery check validates these again.

3. The remaining internal statement is strictly below the global target: it has
neither derived global sections, scalar restriction nor the module-localization
instance. The other new statement concerns arbitrary sheaf maps and is proved
from the existing unit square. Checked Hom variance and the types of both beta
components; identity squares reduce to evaluation mates, and zero/empty cases
introduce no invertibility requirement. Read Stacks Tags 0AA8, 08I3 and 08HY:
0AA8's isomorphism hypotheses are not used to claim an isomorphism here. The
internal assertion is the documented formal coherence refinement, not that
isomorphism theorem. Repeated searches with "monoidal pullback adjunction",
"Beck Chevalley", "internal hom evaluation comparison", internalHomMate and
homEquiv naturality, through LeanFinder, Loogle, Mathlib grep and repository rg.
Found only generic naturality/evaluation lemmas and the single-universe analogues;
the latter use different tensorators/comparisons. No applicable duplicate or
short proof of the remaining coherence statement was found.

4. The proof opens the top hole, uses the actual internal and Leray reductions,
and proves the naturality glue. Public imports supply declarations appearing in
signatures; new imports used only in proofs are plain import. No old import is
removed. The old proof dependencies removed from the parent's direct list are
lem-sc-mixed-hom-tensor-pullback-iso and def-pc-derived-base-change-map; both remain
needed below the new nodes, as No longer needed already explains. The unit
sk-thm-picard-duality has empty realized.statement and realized.steps entries;
this item is not a unit realization, and this delivery changes no unit route.

5. Checked node statements against the Lean signatures, the proof-step uses
against proof_deps, sources, creation records, chapter/unit and blueprint ancestry.
The existing node's three steps describe the actual Lean reduction. The new
Leray node describes the compiled naturality proof; the internal node describes
the remaining obligation rather than claiming a Lean proof. New node statements
are not aliases for the global target. Verdict: acceptable decomposition, one
original hole closed and one strictly lower hole added, net zero; two auxiliary
statements introduced, one already proved. Second reading changed only stale
non-proof node metadata and this report, with no mathematical or Lean edits.

## What changed

The signature and existing docstring of `AlgebraicGeometry.smoothProper_dualizing` are
unchanged. Its single sorry is replaced by a compiled composition of right unitor,
tensor of determinant evaluation, inverse associator, tensor of diagonal evaluation,
and left unitor. The proof obtains finite local freeness of relative differentials
from the existing, proved upstream theorem
`Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`.

Two new modules isolate genuinely separate steps of Stacks Tag 0BRT:
`Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation` states the diagonal
chain through the shifted normal determinant, without cancellation;
`Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation` states determinant inversion
for an arbitrary finite locally free sheaf, with no proper morphism or right adjoint.
The parent node now records the actual three-step Lean proof. The first new node
retains the original geometric dependencies; the second cites the existing Mathlib
exterior-power determinant pairing leaf.

Local compilation of all three modules passed in import order. The target proof has
no sorry or incomplete tactic step. All new modules use the recorded derived tensor
structure and the shared sheafified exterior-power definition. Both new statements
were checked on rank zero (empty wedges give the structure sheaf), empty schemes,
and rank one (a line and its dual). For a smooth proper curve the normal determinant
has shift -1 and the differentials determinant shift +1, so their shifts cancel.
The diagonal theorem handles the original independent derived universes explicitly.

Searches were run with the launcher's LeanFinder, Loogle, LeanSearch, and grep.
LeanSearch returned HTTP 500, recorded as unavailable. LeanFinder found ordinary
sheaf adjunctions and module exterior powers in degrees zero and one, but no matching
derived determinant or relative-dualizing theorem. Direct source search found the
ring-module determinant pairing, already represented by
`lem-sc-exterior-power-dual-pairing`. No duplicate node was made for that result.
The blueprint searches for determinant dual and diagonal evaluation found no match.

## Proved and sorry left

Proved from named intermediate statements:
`AlgebraicGeometry.smoothProper_dualizing`
(`lem-sc-smooth-proper-relative-dualizing-general`), the only original sorry.

Exactly two new sorries remain, each the complete proof of a public named theorem:

- `AlgebraicGeometry.smoothProper_dualizing_tensor_evaluation`
  (`lem-sc-smooth-proper-dualizing-tensor-evaluation`), in
  `lean/Sheaf/AlgebraicGeometry/SmoothProperDualizingTensorEvaluation.lean`.
  This is the evaluation identity A tensor N ≅ unit, namely the displayed diagonal
  chain of Tag 0BRT before determinant cancellation. Its docstring gives the complete
  geometric argument and the transports needed by the existing Lean interfaces.
- `AlgebraicGeometry.shiftedDeterminant_dual_evaluation`
  (`lem-sc-shifted-determinant-dual-evaluation`), in
  `lean/Sheaf/AlgebraicGeometry/ShiftedDeterminantDualEvaluation.lean`.
  This is the independent identity N tensor D ≅ unit for every finite locally free
  sheaf, established locally by determinant evaluation, gluing, flatness, and shift
  compatibility. Its docstring describes these steps including rank zero.

Neither theorem has the target conclusion A ≅ D, and neither takes that conclusion
as a hypothesis. The target performs the actual cancellation in Lean using both
identities; it is not one application of a renamed target. These are a partial
reduction, not a claim that the transitive proof is axiom-free yet.

## No longer needed

Removed from the target's direct proof imports:

- `Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials`
- `Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure`
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing`
- `Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint`
- `Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular`
- `Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula`

These imports and all their original nodes remain needed by the first intermediate
module, where they are retained as proof imports. Thus no geometric dependency is
pruned from the target's transitive closure. No public import is removed or added in
the target, and no unit or chapter route is bypassed. Pruned nodes/modules: none.

The old direct `proof_deps` no longer used directly by the parent are:

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-proper-base-change`
- `lem-pc-noetherian-derived-direct-image-right-adjoint`
- `lem-sc-smooth-proper-diagonal-koszul-regular`
- `lem-pc-smooth-flat`
- `lem-sc-smooth-proper-diagonal-pushforward-structure`
- `lem-sc-smooth-proper-diagonal-tensor-formula`
- `lem-sc-smooth-proper-diagonal-koszul-dual`
- `lem-sc-smooth-proper-diagonal-conormal-differentials`

Each remains a dependency of the geometric evaluation node; none is transitively pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original final step labelled
cancellation elementary, but its Lean prerequisites were not exposed: an isomorphism
between the shifted normal determinant and its inverse had not been stated. That
missing reusable determinant step is now an explicit intermediate theorem, and its
composition with the geometric evaluation is a complete Lean proof.

The geometric lemmas use different presentations: the diagonal counit and tensor
formula use canonical full-subcategory lifts and a common derived universe; Koszul
duality uses a locally ranked complex and the ideal-sheaf conormal; the target allows
a comparison-specified functor, a structure-object isomorphism, and independent
universes. The new geometric theorem records this glue rather than changing any
existing signature or hiding it inside a partial proof.

This machine's read-only clone lacks the literal source files
`literature/stacks-project/duality.tex` and the unit `_section.md`. The full unit text
was read from `dag/units/sk-thm-picard-duality.json`; source statements and the complete
0BRT argument were read from the official Stacks pages
https://stacks.math.columbia.edu/tag/0BRT and
https://stacks.math.columbia.edu/tag/0BR0. The node's source paths retain the project's
canonical literature locations. No repository files were written by hand.

## New nodes

`lem-sc-smooth-proper-dualizing-tensor-evaluation` is in
`dag/nodes/sec-picard-framework/lem-sc-smooth-proper-dualizing-tensor-evaluation.json`.
It records the geometric evaluation chain from original Steps 1–6, the identification
of the composite pullback, and functor/object/universe transports. It stops before
using invertibility of the determinant. Its module is
`lean/Sheaf/AlgebraicGeometry/SmoothProperDualizingTensorEvaluation.lean`.

`lem-sc-shifted-determinant-dual-evaluation` is in
`dag/nodes/sec-picard-framework/lem-sc-shifted-determinant-dual-evaluation.json`.
It generalizes the original Step 7 determinant inversion to every finite locally free
sheaf. Its two proof steps give local determinant evaluation and its shifted derived
version. Its module is
`lean/Sheaf/AlgebraicGeometry/ShiftedDeterminantDualEvaluation.lean`.

Both nodes inherit the original chapter and unit and point through the original item
to blueprint ancestor `lem-sc-finite-duality`. No change record is needed: existing
statements and definitions are unchanged, and the target's public imports are unchanged.

## Second reading by V1

1. Interface: PASS. Compared the delivered parent module with the repository using
   `diff -u`: only private proof imports and the theorem body differ. The signature
   and existing docstring are byte for byte unchanged. No definitions are delivered,
   no target statement changes, and no change record is required.
2. Proof and trust: PASS as a partial reduction. All three files compile locally in
   import order without warnings or errors. Scratch copies with `#print axioms` for
   each theorem report exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
   The parent contains no sorry; each of the two new sorries is the entire proof of
   its named public theorem. No forbidden declaration or hollow definition occurs.
   The parent is not yet transitively axiom-free, as the first report already states.
3. Split statements: PASS. Read both statements, docstring proofs and nodes against
   Stacks Tags 0BRT and 0BR0. The geometric lemma is the diagonal chain before
   cancellation; the determinant lemma is independent of properness and adjoints.
   Rank zero gives the unit, rank one pairs a line with its dual, and empty schemes
   give the zero category; the geometric identity for the identity morphism has
   d=0, and for a smooth proper curve the shifts are -1 and +1. Neither lemma merely
   renames the parent conclusion. Independent LeanFinder queries for invertible
   determinant evaluation and diagonal upper shriek, Loogle `Module.Invertible`,
   and repository searches for determinant dual/evaluation found no matching derived
   sheaf theorem. Mathlib PicardGroup supplies ring-module invertibility, not the
   needed sheafification, derived single-object, and shift compatibility. The existing
   exterior pairing node is reused. Neither open step can be closed in a few minutes
   from the current interfaces.
4. Route and pruning: PASS. The actual composition is
   A -> A tensor unit -> A tensor (N tensor D) -> (A tensor N) tensor D
   -> unit tensor D -> D. Its directions match the two supplied isomorphisms.
   Public imports supply statement types and the recorded derived tensor instance;
   proof-only imports are plain imports. The old geometric proof imports remain in
   the new geometric module. All removed direct dependency ids are now listed under
   No longer needed, with their continued indirect use explicit. No node leaves the
   transitive route. The unit sk-thm-picard-duality has empty realized statement and
   step lists; no realized node or unit route is bypassed or changed.
5. DAG: PASS. The parent proof and dependency union match the two applications,
   upstream finite local freeness, and monoidal composition. Both new nodes have
   source, complete stepwise proof, dependency union, search records, split status,
   created/blueprint/chapter/unit fields, and matching Lean declarations/signatures.
   Existing node changes are confined to proof, proof_deps and proof_origin.

Second reading changed only this report: added the explicit list of old direct
proof dependencies now used indirectly and recorded the independent review.
No Lean repair was needed.

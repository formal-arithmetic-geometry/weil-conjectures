## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.exists_comparisonSourceIso` in
`Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport`, preserving its complete signature,
all definitions, existing instances, visibility, and imports. Added two proved private helpers:
`restriction_scalar_naturality` transports coefficient multiplication through exact restriction
and the localization factors; `lift_tensor_iso` upgrades the specified B-linear equivalence
using tensor induction and proves uniqueness using faithful restriction.

The main proof applies the first helper to the derived stalk morphism conjugated by its
localization factors, uses naturality of the derived-functor identification, applies homology,
and conjugates by the model cohomology identifications. Their `cohomologyIso_smul` equations
supply precisely the coefficient hypothesis of the second helper. Updated the existing node's
proof and proof_origin to describe this implementation; its proof dependencies remain needed.

Searches: LeanFinder for derived coefficient naturality returned change-of-rings interfaces
but no exact match; Loogle for `CategoryTheory.Functor.leftDerivedNatIso` returned the existing
universal derived-functor isomorphism and its hom/inv lemmas; the logged grep and local searches
located Mathlib's derived-category linear instances and the model scalar-action equation.
Read Stacks Tags [0DJ7](https://stacks.math.columbia.edu/tag/0DJ7) and
[06Y6](https://stacks.math.columbia.edu/tag/06Y6) online, because the cited literature files
are not present in this clone. The unit route is unchanged.

Validation: the complete module compiles with `lcompile.py`, with no errors or warnings.
The two generic helpers include zero tensors, sums, arbitrary modules (including zero modules),
and arbitrary coefficient rings; no flatness, K-flatness, or representable chain map is added.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_comparisonSourceIso`
(node `lem-pc-stalk-comparison-source-transport`).

Both new private helpers are fully proved. Zero holes added or split off. No `sorry` remains
in this module or is introduced elsewhere by this delivery. Existing dependency holes are
unchanged; this proves the item from its already stated model and stalk interfaces.

## No longer needed

None. No imports, nodes, or modules were pruned. The single-complex stalk interface and
base-derived tensor model are needed to state the theorem; module stalk exactness and
abelian-group stalk additivity remain needed by the existing exact derived stalk construction.
Mathlib exact-functor and linear derived-category infrastructure are used in the proof.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The previous proof_origin note described coordinate-normalization
and invertibility glue belonging to the parent delivery rather than this scalar-transport node;
it now records the implemented proof. The argument need not construct a new localized natural
transformation: Mathlib's A-linear derived category already gives coefficient commutation,
and the existing localization factors transport it to the recorded model inputs.

## Second reading by F1

1. **Existing interface unchanged: pass.** Read the complete repository/sandbox Lean diff.
   Only two proved private helper theorems and the body of
   `AlgebraicGeometry.SingleComplexBaseChange.exists_comparisonSourceIso` were added.
   Every existing signature, definition body, instance, visibility, and import is byte-for-byte
   unchanged. There are no change records or adapted modules.
2. **Kernel proof: pass relative to the existing dependencies.** Independently compiled the
   complete module with `lcompile.py` (15.4 seconds, no errors or warnings). Scanned the
   delivered Lean for `sorry` and forbidden declarations/options: none. In a scratch copy,
   `#print axioms` for both private helpers reports only `propext`, `Classical.choice`, and
   `Quot.sound`; the main theorem additionally reports `sorryAx` from existing dependencies.
   This closes the item's own hole, not the unresolved dependency closure. No definition or
   choice of data was introduced or modified.
3. **New statements and edge cases: pass.** No split-off statement or new hole exists.
   Read both private helper proofs: scalar commutation holds for an arbitrary derived
   morphism by linearity; localization-factor naturality transports it without choosing a
   chain-map representative. The lifting helper handles zero tensors, pure tensors and sums;
   its additive equivalence has the original underlying map, its inverse is the inverse
   linear equivalence, and faithful restriction proves uniqueness. Zero modules, zero rings,
   and the identity transport require no extra assumptions. A fresh Loogle search for
   `TensorProduct, LinearEquiv` and local searches of change-of-rings and derived linearity
   found standard tensor equivalences and restriction tools, not a replacement for the
   coefficient-compatible lifting statement. No restatement of the item was left open.
4. **Route and pruning: pass.** The proof first uses Mathlib derived linearity and naturality,
   then the existing model's `cohomologyIso_smul`, and finishes by elementary tensor induction.
   Read both model/stalk interfaces and `dag/units/sk-thm-picard-semicon.json`; its `realized`
   entries are unchanged and no unit step is bypassed. All three old proof dependencies are
   still used. Tried deleting each proof-only import in separate scratch copies:
   without `ModuleStalkExact`, `module_stalk_exact` is unavailable; without
   `Mathlib.Topology.Sheaves.Abelian`, abelian-group stalk additivity fails to synthesize.
   The public exact-functor import supplies constructions used by the existing public
   definitions, so it is not merely a proof import. Nothing can be pruned here.
5. **DAG matches Lean: pass.** Compared the node JSON with the repository: only `proof` and
   `proof_origin` changed. Read the Lean records of all three proof dependencies and verified
   that `proof_deps` equals the union of the proof steps' `uses`. The recorded steps accurately
   describe coefficient transport, cohomology conjugation, tensor induction and uniqueness.
   There are no new nodes requiring a source/docstring review.

Second reading changed only this report: added independent verification and the explicit axiom
qualification. No repair to the Lean proof or node was needed. Holes closed: one
(`AlgebraicGeometry.SingleComplexBaseChange.exists_comparisonSourceIso`); holes added: zero;
split off: zero; pruned: none.

## What changed

Reduced the item theorem to derived transport plus a proved counit cancellation.
The new lower statement does not assume that the derived pullback counit is invertible
and does not mention the prescribed representative. The item proof combines the final
direct-image maps by functoriality and uses the cancellation theorem to recover its
original conclusion. Its signature is unchanged.

The representative module exposes its actual complex comparison, its component formula,
and a proved cancellation theorem. The coefficient target map shares an explicit chain
map with the lower statement. These interface refactorings are recorded in
`coord/changes/affineBaseChangeTildeRepresentative.md` and
`coord/changes/affineTildeTensorOrdinaryTargetMap.md`.

## Proved and sorry left

Closed the item's sole hole, `AlgebraicGeometry.affineTildeTensorOrdinaryExchange`,
by a decomposition. Added one hole:
`AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization`.
It still needs the ordinary tensor-generator calculation to be transported through
the homotopy quotient and the natural right-derived unit. Its source and complete
proof route are in its docstring and node. It is strictly before representative
normalization and has no invertible-counit hypothesis.

Also proved `AlgebraicGeometry.affineBaseChangeTildeComplexIso_hom_f` and
`AlgebraicGeometry.affineBaseChangeTildeRepresentativeIso_counit`; the shared complex
comparison and pushforward chain map contain no proof holes or hollow data.

## No longer needed

No mathematical node or module is pruned. Removed the redundant direct imports
`Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization`,
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and
`Sheaf.AlgebraicGeometry.TensorPullbackTilde` from the item module. Their mathematical
content remains available through the existing source/representative API or the new
lower transport module. Unlanded exploratory generator helpers and
generic mate glue were removed from the sandbox; the final proof uses the single lower
transport statement and the proved cancellation API. No deleted library file is claimed. The old direct proof dependencies
`lem-pc-affine-tilde-pushforward-cohomology-normalization`,
`lem-pc-derived-base-change-unit-compatibility`,
`lem-pc-module-pullback-adjunction`, and `lem-weil-pbc-tilde-pullback-base-change`
leave the parent proof plan, but remain in the lower calculation; they are not globally
pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's split merely expanded the target map and restated the parent.
That split was replaced: the new statement has no invertible-counit assumption and
ends at the localized inverse complex comparison. The parent now performs a real
functorial combination and representative cancellation. The new node does not depend
on the parent node, avoiding a DAG cycle.

## New nodes

`lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization`, attached to
`Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization`, states the
remaining derived transport without representative normalization. It still needs the
ordinary generator calculation and its homotopy/derived-unit transport as described
above. The two new maps are explicit constructions; no arbitrary witness is selected
from a mere existence statement.

## Second reading by P1

1. I compared every delivered Lean module with the repository versions. The item theorem
   signature and all existing declaration signatures are unchanged. The representative module adds
   named comparison and cancellation declarations, with the construction itself unchanged;
   the two interface changes are recorded in the change records. Verdict: pass.

2. I compiled all delivered sandbox modules with `lcompile.py --all`. The only remaining
   `sorry` is the whole proof of
   `affineTildeTensorOrdinaryExchange_preNormalization`, a named public theorem whose
   docstring and DAG node give its source and proof route. There are no axioms, unsafe or
   hollow definitions. Verdict: pass.

3. The split-off statement is a strict lower transport statement: it omits the parent
   theorem's invertible-counit hypothesis and ends at the localized inverse comparison.
   It is therefore not a restatement of the parent. The cancellation theorem is proved by
   functoriality and inverse/counit cancellation. Searches in Mathlib and lean/Sheaf found
   no existing declaration with these statements. Verdict: pass.

4. The parent proof follows the shortest available reduction: apply pre-normalization,
   reassociate the direct image, use the proved representative-counit cancellation, and
   unfold the shared target map. The extra exploratory helpers are absent from the
   delivery. The three redundant direct imports listed above were removed. No mathematical
   node or module is globally pruned. Verdict: pass.

5. The DAG proof, proof dependencies, Lean declarations, and report agree. The unit
   remains `sk-thm-picard-semicon`; its realized route is preserved through the source
   comparison, derived base-change compatibility, pre-normalization, and cancellation.
   Verdict: pass.

I restored the original named local additive instance, removed three redundant direct
imports from the item, and corrected the report, change-record format and DAG proof metadata. The Lean proofs
and existing public signatures were not changed during the second reading. The new
module is publicly imported because the existing target-map definition uses its explicit
chain-map construction, not merely its theorem.

Independent searches: LeanFinder for "associated sheaf restriction of scalars base
change mate tensor generator naturality localization" returned generic sheafification
and scalar-extension adjunction lemmas; Loogle for `CategoryTheory.Functor.map_comp`
confirmed the functorial reduction; Mathlib grep and alternate-word searches in both
Lean source roots found no replacement for the lower affine exchange equality. For
zero complexes both composites are zero; for the identity square and identity ring
maps the formula is the adjunction unit/counit identity. The generator proof also
includes zero rings without a nonzero hypothesis. The unit realized arrays are empty
in this snapshot and are unchanged; this split is below the unit level.

The remaining split is a decomposition with net zero holes closed, rather than a
complete proof of ordinary exchange.

Additional scratch checks proved by `rfl` that both refactored definitions equal their
original repository constructions with the same arguments. Explicit `#print axioms`
checks show only `propext`, `Classical.choice`, and `Quot.sound` for the complex
comparison, component formula, and cancellation theorem; the parent and the lower
transport theorem additionally use `sorryAx`, as reported.

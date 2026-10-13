## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangePrefix`
by the composite mate calculation. The public theorem's signature and docstring are unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.CoefficientSquarePasting`.
All helper theorems are private and proved: inverse-mate transposition, composite-adjunction
transposition, comparison pasting, its naturality with a coefficient morphism, the image
comparison counit identity and its inverse form, the defining base-change transpose, and
the local U transpose. The final proof pulls the U formula back along W and applies the
comparison identity there. The full module compiled successfully in 50.5 seconds;
the sole style warning was fixed by explaining the local heartbeat budget. No other module is adapted and no definition is changed.

The existing `coefficient_square_pasting` supplies the coherence calculation at both U
and W. The node copy records this dependency and the actual two-step proof. The unit's
realized statement and steps are untouched.

## Proved and sorry left

Closed `AlgebraicGeometry.relativeMV_composite_baseChange_prefix`
(blueprint `new-relative-mv-composite-base-change-prefix`): one hole closed, zero added.
There is no `sorry` in the delivered module, including its private helpers. No new
statements with holes, new modules, axioms or data constructions are added.

## No longer needed

No imports removed and no module pruned. No target-open-counit or restriction-naturality
module is needed for this prefix computation. `RelativeMVRestrictionSourceCounit` and
`RelativeMVRestrictionFirst` were read for their private adjunction calculations, but
are not imported: their public conclusions are not used. The original direct proof
edge to `lem-pc-ringed-spaces-derived-pullback-composition` is replaced by the existing
`lem-pc-coefficient-square-pasting`; pullback composition remains required transitively
by the pinned definitions and by that theorem and is not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's domain mismatch is resolved by transposing through the inverse
right-adjoint comparison before applying pullback pasting. The coefficients must be
tracked at A and C separately, and the U base-change square comparison is the inverse
of the U coefficient comparison. These distinctions account for the inverse factors
and allow cancellation without identifying incompatible morphism domains.

Sources read: Stacks Tags [08HY](https://stacks.math.columbia.edu/tag/08HY) and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S), and Mathlib Adjunction Basic/Unique.
The local literature directory has only tracked indexes, so the two Stacks pages were
read online. Searches by LeanFinder, Loogle and grep are logged in `searches.jsonl`.
The proof uses only functoriality, adjunction equations and comparison coherence;
therefore equal or empty opens and zero coefficients require no extra hypotheses.

## Second reading by N3

1. Compared the delivered module with the repository version. The public theorem signature and existing declarations are unchanged; only the proof and a proof-only import were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. There are no `sorry`, axioms, unsafe declarations, or hollow definitions in the delivered file. The helpers are private and the proof uses only the permitted logical axioms.
3. Checked the proof route and dependencies against the imported declarations and the node. The composite mate, coefficient-square pasting, counit identities, and transpose lemmas are genuine intermediate reductions; no split-off statements were added and no existing library theorem is duplicated.
4. Checked pruning and imports. `Sheaf.AlgebraicGeometry.CoefficientSquarePasting` is required by the proof; no existing import can be removed, and the unit route through coefficient-square pasting and derived pullback composition is retained.
5. Checked the DAG node against the Lean theorem. Its statement, proof steps, proof dependencies, and proof origin agree with the delivered proof; the unit's realized statement and steps are unchanged.

Changed only the proof of `AlgebraicGeometry.relativeMV_composite_baseChange_prefix`, adding private helper calculations and the proof-only coefficient-square-pasting import. No statements, definitions, nodes, or other modules were changed.

## What changed

Proved `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_open_unit` in
`Sheaf.AlgebraicGeometry.NormalConstantOpenUnit`, preserving its signature and visibility.
Added proof-only imports of `Sheaf.AlgebraicGeometry.NormalConstantGenericUnit` and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`.
The generic local-spectrum map factors through the nonempty open. Its unit and the
pushforward composition isomorphism put the constant sheaf in the essential image of the
fully faithful open pushforward. Mathlib's adjunction criterion then proves the open unit
is invertible. Updated the theorem's proof docstring and the existing node's proof route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_open_unit`
(node `lem-weil-pbc-normal-constant-generic-open-unit`).
No `sorry` remains in the item; no holes or modules were added.
This is a proof from the existing theorem
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit`
(node `lem-weil-pbc-normal-constant-generic-unit`), whose pre-existing `sorry` remains
outside this delivery. It is not yet an axiom-free proof of the full geometric result.

## No longer needed

No original imports were removed; no existing nodes or modules are pruned.
The direct strict-henselian calculation originally suggested for this item is unnecessary:
the generic-point theorem supplies the geometric input. The proof needs neither a second
generic-point unit on U nor a constant-sheaf pullback comparison nor geometric-stalk
conservativity.

## Where the brief, the DAG or earlier work was wrong

The original node's proof had no dependencies and proposed repeating the strict-henselian
calculation. The shorter categorical argument instead uses the existing generic-point
unit and full faithfulness of open pushforward; the node now records those dependencies.
No statement or definition was changed, and no forced adaptations were needed.

## Second reading by X3

1. **Signatures and statements.** Compared the delivered module with the repository version. The
   theorem signature and visibility are byte-for-byte unchanged. The node statement is unchanged;
   only its proof route, dependencies, and provenance now describe the delivered proof.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is clean and contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses the already
   stated generic-point theorem, the lower-star composition isomorphism, and the open-immersion
   fully-faithful instance. The generic point factors through every nonempty open, and the
   essential-image criterion is applied to the resulting explicit isomorphism.

3. **Statements and dependencies.** No new statement was added. The existing node remains exactly
   the nonempty-open unit claim and is strictly supported by the three declarations used in the
   Lean proof; no Mathlib or upstream duplicate was introduced.

4. **Pruning and route.** The route keeps the unit's generic-point and direct-image comparison
   steps and then applies the open-immersion categorical criterion. No old import or proof
   dependency is unused, and no module or node is newly pruned.

5. **DAG agreement.** The node's proof steps, `proof_deps`, and `proof_origin` match the code:
   factorization, generic-point unit plus `lowerStarComp`, then full faithfulness and
   `isIso_unit_app_of_iso`. The unit record's realized route is preserved.

The second reading changed only this report section and records the checks above; no Lean
signatures, definitions, or theorem statements required repair.

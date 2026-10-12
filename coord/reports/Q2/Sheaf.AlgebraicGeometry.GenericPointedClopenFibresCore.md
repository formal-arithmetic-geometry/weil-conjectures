## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore` with a
complete Lean reduction following the original geometric route. Its signature, public
imports, and existing docstring are unchanged. Added proof imports of
`Sheaf.AlgebraicGeometry.PointedClopenIntegralModel`,
`Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`.

The integral model is fully constructed and proved in a new module. Its base is the open
restriction of the concrete vanishing-ideal subscheme of the closure of y. The total space
is the open subscheme corresponding to the clopen trace of A in the base change. The
proof establishes integrality, finite type, the open embedding of bases, fibre
homeomorphisms, and the rational point of the generic fibre. No model data are chosen from
an unproved existence theorem. Choice selects only homeomorphisms whose existence the
same proof establishes without sorry.

The core proof transfers generic preconnectedness, obtains connectedness using the
rational point, and applies the already proved rational-point criterion from the source
library (Stacks 04KV). It then uses the new general spreading theorem (Stacks 055G) and
explicitly transports its relatively open neighbourhood and fibre connectedness back to T.
The original node's proof, proof_deps, and proof_origin now describe these exact steps.

All three modules compile together in import order using lcompile.py. A temporary
#print axioms check of `exists_pointed_clopen_integral_model` reported exactly propext,
Classical.choice, and Quot.sound. The core still transitively uses sorryAx from the
spreading theorem; it is a decomposition, not a complete axiom-free proof of the item.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.exists_open_preconnected_fibres_of_pointed_clopen_core`
(node `new-lem-sbc-generic-pointed-clopen-fibres-core`). No sorry remains in the item module.

Also fully proved the new theorem:
`AlgebraicGeometry.exists_pointed_clopen_integral_model`
(node `lem-sbc-pointed-clopen-integral-model`). Its proof has no sorry dependency.

Added one direct hole, and this is the only sorry in the delivered modules:
`AlgebraicGeometry.exists_open_geometricallyConnected_fibres_of_generic`
(node `lem-sbc-generic-geometrically-connected-spread`). Its proof is exactly `by sorry`,
with the source and a complete natural-language proof in its docstring and node.
This is the general geometric spreading step over any irreducible base. It assumes
neither a section nor a pointed clopen piece. The original problem is thus reduced
strictly to one independent part of its argument. Holes closed: 1. Holes added: 1.
The direct net reduction is 0; this delivery is a decomposition, with the model and
all combination and transport steps proved.

## No longer needed

No original imports, existing nodes, or existing modules were removed. The original
core node had no proof_deps to prune. The extra trial import
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` was removed from the new model module;
its required declarations are available through the used subscheme import.

Do not add a dependency on `WeilConjectures.RingTheory.GenericConnectedness` for this
proof. Its existing generic connectedness theorems concern affine finite type algebras
over a noetherian domain; the current model need not have affine total space and the
base need not be noetherian. It is useful for a future proof of special cases, but does
not discharge the remaining general theorem under the hypotheses here.

## Where the brief, the DAG or earlier work was wrong

The original core node packaged the integral-model construction, the rational-point
criterion, generic geometric spreading, and ambient-open transport in one unproved
step with no proof dependencies. These are now distinguished, and only generic
spreading remains open. No false statement or interface change was found.

The new model was tested against empty A (excluded by hpoint), arbitrary changes to A
outside the prescribed trace (irrelevant to the construction), a singleton closure,
an open V that is not quasi-compact, nonreduced T, and possibly empty other fibres.
Clopenness makes its inclusion a closed immersion and thus quasi-compact even when V
is not quasi-compact. Fibre homeomorphisms work for empty fibres. The generic rational
point supplies the nonemptiness needed by the geometric connectedness criterion.

The remaining spreading theorem is exactly Stacks 055G, including finite type rather
than finite presentation, and with no noetherian or quasi-separated hypothesis. Empty
X cannot satisfy its geometrically connected generic-fibre assumption. A nonreduced
base is handled by reduction in the cited proof. The unit route stays unchanged;
`dag/units/sk-prop-normal-form.json` has no realized node that this proof bypasses.

Mathlib searches used LeanFinder, Loogle, and grep; LeanSearch returned Internal Server
Error and is recorded as unavailable. The whole blueprint was searched for generic
connectedness, 055G, 055N, and clopen integral models; no duplicate statement was found.
The exact existing rational-point criterion was reused, and the general affine
noetherian theorem in GenericConnectedness was read and assessed as a special case.

## New nodes

`lem-sbc-pointed-clopen-integral-model`, in
`Sheaf.AlgebraicGeometry.PointedClopenIntegralModel`: the integral-base construction,
fibre homeomorphisms, and a generic rational point. Fully proved in Lean from existing
Mathlib and source declarations; no connectedness or spreading is assumed or asserted.

`lem-sbc-generic-geometrically-connected-spread`, in
`Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread`: Stacks 055G,
more-morphisms.tex, lemma-geometrically-connected-generic-fibre. This is the only
postponed part, with a complete proof in words. Both nodes retain the original chapter
and unit and identify the slicing ancestor. No change record is required because no
existing interface or statement changed.

## Second reading by Q2

1. **Repository comparison:** compared the delivered core module with the repository
version. The target declaration, its hypotheses, conclusion, and docstring are unchanged
byte for byte; only proof imports and the proof body were added. The two added modules are
new declarations and do not alter an existing interface.

2. **Compilation and proof hygiene:** compiled all three modules with `lcompile.py --all`.
The only remaining `sorry` is the named theorem
`exists_open_geometricallyConnected_fibres_of_generic`; there are no axioms, unsafe or
hollow definitions. The integral-model theorem compiles without a sorry dependency.

3. **New statements:** checked both new statements against their constructions and edge
cases. The integral model is explicitly constructed from the reduced closure and the
clopen restriction, with no arbitrary witness chosen from an existence theorem. The
spreading statement is exactly Stacks Tag 055G and is strictly more general than the
target reduction; its source, proof sketch, and DAG node are present.

4. **Shortest route and pruning:** the core proof uses the existing rational-point
criterion, the explicit integral model, and the single general spreading step. Imports
needed only by proofs are plain imports. The original node had no proof dependencies to
prune, and no existing module became unused.

5. **DAG and unit route:** verified that the core node's `proof`, `proof_deps`, and
`proof_origin` match the Lean proof, and that both new nodes carry the same chapter and
unit. The unit's realized route remains unchanged.

I changed only this report section after the first reading check; no Lean code or node
statement was changed during second reading.

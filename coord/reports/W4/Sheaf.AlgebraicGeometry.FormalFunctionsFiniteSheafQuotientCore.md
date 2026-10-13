## What changed

Proved `AlgebraicGeometry.formalFunctionsFiniteι_isClosedImmersion` directly. The proof
uses Mathlib pullback pasting to establish the defining finite-level pullback square,
then applies stability of closed immersions under base change to the quotient Spec map.
The closed-immersion node now records this actual proof route. All existing signatures,
visibility, definitions, and public imports remain unchanged.

## Proved and sorry left

Closed 1 of 2 original holes:
`AlgebraicGeometry.formalFunctionsFiniteι_isClosedImmersion`
(node `lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed`). Its proof uses no
new holes or project theorem with a sorry. No holes were added.

The original hole `AlgebraicGeometry.formalFunctionsFinite_sheaf_quotient_iso`
(node `lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso`) remains unchanged.
The remaining work is the identification of the recursively constructed ideal-power
inclusion with the closed-immersion kernel, and the tensor-pullback composition and
adjunction-unit transport. `ClosedImmersionPowerQuotient.closedImmersion_power_quotient` provides the general
power-quotient transport (in namespace AlgebraicGeometry); applying it here still needs
the finite-map kernel equality and the tensor-pullback/unit comparison. The private
transport proofs in `ThickeningSystemPushforwardAdic` explain its implementation.
This is a partial proof delivery, not a decomposition: one hole closed, zero added.

## No longer needed

The original proof dependencies `lem-weil-pbc-quotient-base-change-closed-immersion-ideal`
and `lem-weil-pbc-closed-immersion-unit-quotient` are not needed by the closed-immersion
proof, and were removed from that node's proof_deps. They remain planned dependencies
of the unresolved quotient-isomorphism theorem in this same module. No import or whole
module is pruned, and no unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original closed-immersion node cites the closed-immersion unit quotient theorem,
which is not needed to show closedness. Pullback pasting and the surjectivity of the
ring quotient map suffice. Loogle's index did not recognize `IsPullback`; the semantic
search returned generic fibre and base-change lemmas. Repository/Mathlib searches found
`IsPullback.paste_vert_iff`, `MorphismProperty.of_isPullback`, and
`IsClosedImmersion.spec_of_surjective`, whose actual signatures were checked by Lean.

## Second reading by W4

1. Interface: compared the complete delivered Lean file with the repository using
   `diff -u`. Only the body of `formalFunctionsFiniteι_isClosedImmersion` changed.
   Both existing signatures, all definitions, visibility, and imports are byte-for-byte
   unchanged. No change record or forced adaptation is needed. Verdict: pass.
2. Proof: compiled the delivered module with `lcompile.py` successfully. A scratch copy
   with `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`
   for the closed-immersion theorem. The untouched quotient-isomorphism theorem also
   reports `sorryAx`, as expected. There is exactly one named theorem with `sorry`,
   no new holes, no hollow definitions, and no forbidden declarations. Read the defining
   pullback lift: the pasted outer square is the finite fibre square; cancellation of
   the local-base pullback gives precisely the square used for base-change stability.
   Quotient surjectivity supplies closedness without any assumption on `f`. The same
   argument applies at `n = 0` and to empty fibres. Verdict: pass.
3. Split statements: this delivery introduces no statements or nodes. The remaining
   original quotient-isomorphism hole retains its source, natural-language proof,
   signature, and existing node. Read `QuotientBaseChangeIdeal`,
   `ClosedImmersionUnitQuotient`, and the existing power-quotient applications: none
   directly supplies the required tensor-pullback and adjunction-unit transport, so
   this residual hole is not closable by a short application. Verdict: pass.
4. Route and pruning: independently searched the project and Mathlib for the finite
   map, quotient closedness, and pullback pasting. The proof already uses the short
   Mathlib route, with no project proof holes. Public imports support the existing
   signatures; the two plain proof-dependency imports remain for the unresolved
   theorem's documented route. Both old dependencies removed from the closedness
   node are listed under `No longer needed`; they still belong to the isomorphism
   node. Checked `dag/units/sk-thm-p1.json`: neither removed dependency realizes a
   statement or step there, and the unit route is preserved. Verdict: pass.
5. DAG: compared the delivered closedness node with the original. Only `proof`,
   `proof_deps`, and `proof_origin` change, and these describe the actual pullback
   pasting and Mathlib base-change proof. The unresolved node is untouched, and no
   new-node obligations arise. Verdict: pass.

Second reading changed only this report, adding the independent review. No Lean or
DAG repair was necessary. Counts remain one of two original holes closed, zero split
 off, and no whole module pruned.

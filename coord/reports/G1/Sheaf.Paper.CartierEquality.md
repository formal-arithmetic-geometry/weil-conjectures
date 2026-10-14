## What changed

Kept the repaired finitely generated field-extension hypothesis
`IntermediateField.FG (⊤ : IntermediateField k K)` and the complete Cartier
dimension proof.  Made the final finite-extension step explicit by binding the
`FiniteDimensional k K` implication hypothesis as a local instance before using
`trdeg_eq_zero`; this documents the dependency and compiles without changing the
public signature.

## Proved and sorry left

`cartier_equality` is fully proved (one of one declarations). No `sorry`s remain
and no new holes were introduced. Against the current repository baseline, it
was already proved: holes closed: none; holes added: none; net closure progress: 0.
This is a repair delivery for the queued upstream-review #1428 item, not a new proof.

## No longer needed

None.  All imports used by the complete-intersection and cotangent-model proof
remain necessary; no DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly identified the old `Algebra.FiniteType k K`
hypothesis as weakened for a field extension.  The repository's current module
already contains the required `IntermediateField.FG (⊤ : IntermediateField k K)`
repair, so this delivery retains that corrected statement.  The earlier
sandbox report incorrectly treated the item as redundant and did not provide a
repair delivery.

## Second reading by G1

1. **Visible declarations: PASS.** Diffed the delivered module against
   `lean/Sheaf/Paper/CartierEquality.lean`. The only difference is the proof-local
   `let _ : FiniteDimensional k K := hfinite`. The signature, docstring, visibility,
   universes and imports are byte-for-byte unchanged; no definitions are delivered.
   The current qualified `IntermediateField.FG` hypothesis agrees with the node
   and the landed change records. Stacks Tag 07E1 assumes finite generation as a
   field extension, not finite generation as an algebra.
2. **Proof and trust: PASS.** Compiled the delivered file through `lcompile.py`
   with no errors or warnings. A scratch copy with `#print axioms cartier_equality`
   compiled and reported exactly `propext`, `Classical.choice`, `Quot.sound`.
   There are no sorry holes, axioms, unsafe/opaque declarations, foreign-code
   attributes, or data definitions in this delivery. The existential models are
   eliminated only inside a theorem proof; no arbitrary witness defines data.
3. **Split-off statements: PASS (none).** No new statement, module, node or hole
   is delivered. Read the two existing model theorem signatures: the first gives
   a regular sequence with `f.length = c` and `n - c = s.card`; the second gives
   exactly the kernel and quotient equivalences used. No whole-statement
   restatement is introduced. For the boundary `s.card = 0`, the dimension formula
   reduces to equality of the two finite dimensions; for a rational transcendental
   extension it allows positive transcendence degree, unlike the rejected old
   algebra-finite-type hypothesis.
4. **Route and pruning: PASS.** Read the full proof and searched the library,
   upstream source, and Mathlib FieldTheory/RingTheory for the combined
   transcendence-degree/cotangent formula and `cartier_equality`; no shorter
   existing theorem was found. The proof already uses Mathlib's finite-basis
   theorem, rank-nullity and quotient dimension directly. The public imports
   provide notions in the signature; the four plain imports provide proof facts.
   Both Sheaf model dependencies remain used. Read `dag/units/sk-thm-p1.json`:
   its statement and all `realized` steps are untouched. No old dependency has
   become unused; `## No longer needed` is complete.
5. **DAG agreement: PASS.** Read `lem-weil-pbc-cartier-equality.json` and the
   finite-transcendence-basis dependency record. Step 1 matches the finite-basis
   enumeration and complete-intersection model; step 2 matches cotangent
   equivalences and transported finiteness; step 3 matches natural-number
   cancellation and the cardinal cast, then zero transcendence degree in the
   finite case. `proof_deps` and the Tag 07E1 `proof_origin` still describe the
   delivered argument, so no node edit is needed.

Second reading changed only this report: clarified that the baseline already
contains the proof and that this repair closes zero additional holes. Retained
all correct Lean code, including the explicit local finite-dimensional instance.

## What changed

Verified the existing repair of `cartier_equality` requested by upstream review #1428.
The repository and sandbox already assume `(⊤ : IntermediateField k K).FG`, rather
than `Algebra.FiniteType k K`. The proof now lets `omega` combine the sequence-length equality `hlen` directly
with the two rank-nullity equations, removing a redundant shadowing of `hker`.
This report replaces the earlier attempt’s stale change description and second-reading
section. A fresh second reader must verify this delivery.

The proof enumerates finite field generators and a finite transcendence basis, applies
`exists_completeIntersection_fractionField_model` and
`exists_fractionField_completeIntersection_cotangent_model`, and combines the kernel
and cokernel rank-nullity formulas. Its Cardinal equality avoids truncated subtraction.
The finite-extension consequence follows by substituting zero transcendence degree.
The existing node statement, Lean record, and proof dependencies match this route.
No statement, definition, import, DAG route, or target signature is changed.

## Proved and sorry left

`cartier_equality` has a complete proof and no local sorry. Holes closed in this
delivery: none. Holes added: none. Holes remaining in the assigned module: none.
This is verification of an already implemented repair, not new proof progress.
The sandbox module compiled cleanly with `lcompile.py` (exit code 0).
The unchanged caller `Sheaf.RingTheory.PthRootResidueDimensionBalance` also compiled
cleanly against the sandbox overlay (exit code 0); its temporary source copy was
removed from the delivery. The delivery dry run checks the assigned module’s axioms.

## No longer needed

None. Both complete-intersection model imports are used, as is Mathlib’s finite
transcendence-basis construction. No nodes or modules are pruned; the unit route stays.

## Where the brief, the DAG or earlier work was wrong

The repair queue is stale: the supplied repository already contains the requested
finite-field-generation hypothesis, the corresponding DAG statement and proof, and the
adapted call in `Sheaf.RingTheory.PthRootResidueDimensionBalance`. Its call supplies
`IntermediateField.fg_top K L` using the finite residue-field extension established
immediately above it. No further caller adaptation is forced or included.

The earlier sandbox report described a proof simplification that was already identical
to the repository and included an old second reading. That second reading was removed.
The first dry run refused a report-only delivery; the redundant proof binding above
was therefore removed and the resulting proof checked afresh.
Existing landed change records document the hypothesis repair. The dispatcher should
retire this repair once the second reader confirms the current version.

A fresh Lean Finder search returned standard-smooth differential criteria and
cotangent-space results, which do not replace the general Cartier equality. A local
search found no existing Cartier theorem in WeilConjectures or Mathlib. The two model
lemmas were read in full; their signatures supply exactly the objects and comparisons
used by this proof. The finite-extension edge case follows in Lean from `trdeg_eq_zero`;
the field-generation hypothesis also permits transcendental finitely generated fields,
so the reviewed degeneracy has been removed.

## Second reading by T4

1. **Interface preservation — pass.** Compared the complete delivered module with
   `lean/Sheaf/Paper/CartierEquality.lean` in the read-only repository. The sole diff
   deletes `have hker := hker.trans hlen` inside the proof. The existing theorem
   signature is byte for byte unchanged; no definitions, visibility, imports, or
   target signatures change. Existing landed change records already document the
   finite-field-generation repair.
2. **Proof and axioms — pass.** Independently compiled the delivered file with
   `lcompile.py` without errors or warnings. A scratch copy with
   `#print axioms cartier_equality` reports only `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. The delivered source contains no sorry, axiom,
   unsafe, opaque, implemented_by, or extern. The finite generating set is enumerated
   explicitly; the imported model constructions are proved, so there is no data
   chosen from an unproved mere-existence theorem.
3. **Split statements — pass, none.** No new declarations, split statements, nodes,
   or holes are added. Read both imported model theorems in full: one constructs a
   regular-sequence fraction-field model with `n - c = s.card`, and the other gives
   kernel and cokernel equivalences, without assuming the dimension conclusion.
   Checked the zero-transcendence-degree and finite-extension cases, including the
   empty generating set for the identity extension. The equations are valid also
   for zero coordinate dimensions; `c ≤ n` prevents truncated subtraction from
   weakening the rank-nullity argument.
4. **Route and pruning — pass.** Reviewed the finite-basis construction, both model
   applications, dimension transport, natural-number cancellation, Cardinal cast,
   and finite-extension consequence. `omega` uses `hlen` directly, so the deleted
   binding is redundant. An independent Loogle search for `Algebra.H1Cotangent`
   found presentation and smoothness criteria, not the general dimension balance;
   local searches likewise found no replacement formula. Each proof-only import
   is plain `import`; public imports supply vocabulary used in the signature.
   All existing proof dependencies remain used, so `## No longer needed` is complete.
   Read `dag/units/sk-thm-p1.json`: its realized statement and steps are unchanged,
   and this local simplification bypasses no unit.
5. **DAG consistency — pass.** Read the Cartier node and checked its Lean record,
   proof steps, proof dependencies, and source-based proof origin against the code.
   Its finite-basis Mathlib match and both model-node declarations are exactly those
   applied. The remaining dependencies describe transcendence bases and dimension.
   The node already records the actual route, so no node edit is necessary.

Second reading changed only this report by adding the independent review above;
no further Lean repair was needed. This delivery verifies one already proved theorem,
closes zero new holes, adds zero holes, and prunes no modules.

## What changed

Proved `Polynomial.completeLocalNonzeroFibreCharZero_reduction` in
`Sheaf.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZeroReduction`, with its
signature and public imports unchanged. Added the proved private helper
`geometricallyRegular_charZero`, which identifies base change along a purely
inseparable characteristic-zero field extension with the original regular ring.
The second reading removed redundant direct Mathlib imports; the retained
imports already expose the contraction, finite-type and tensor-product lemmas.

The proof eliminates the existing regular coefficient-subring existence theorem
only inside this proposition. It constructs the contracted ideals by comap,
proves all their properties, and applies the existing quasi-finite ascent theorem.
Polynomial integrality is proved coefficientwise; finite type and integrality give
finiteness. `Ideal.under_ne_bot` replaces the fraction-field norm argument.
The node's proof, proof dependencies and proof origin now describe this proof.
The unit `sk-thm-p1` route and all statements remain unchanged.

## Proved and sorry left

Closed the sole original hole:
`Polynomial.completeLocalNonzeroFibreCharZero_reduction`
(node `lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero-reduction`).
The private helper is also fully proved. No sorry remains in the delivered module;
no holes were added, and none were split off. This is a complete proof from
existing declarations, not a new decomposition. The existing dependency theorems
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite` and
`RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime` remain upstream work;
the coefficient-subring theorem likewise has its existing core/residue dependencies.

Validation: the module compiles through `lcompile.py` without errors or warnings.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.FibreRingNoetherian`
- `Mathlib.FieldTheory.PurelyInseparable.Basic` (already public through `GRing`)

Removed corresponding proof dependencies:
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-fibre-ring-noetherian`

Neither theorem is needed by this proof: the assumed `IsRegularRing` instance
already includes Noetherianity of the contracted fibre. They may still be needed
by other items; no claim is made that they leave the entire targets' closure.
The finite fraction-field extension and norm/denominator-clearing route is also
unneeded here; Mathlib's integral contraction lemma supplies nonzeroness directly.
No other planned dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan requested completion and fibre Noetherianity separately even
though the regularity hypothesis already supplies it through Mathlib's definition.
The old nonzero-contraction norm argument was valid but unnecessary. No statement,
definition, interface or unit-route defect was found. No forced adaptations or
change records are needed.

## Second reading by B3

1. **Interface unchanged — pass.** Compared the sole delivered module and node
   against the repository versions with `diff`. The existing theorem signature is
   byte for byte identical, as checked separately by a script; its visibility and
   sole public import are unchanged. There are no definitions, changed statements,
   change records or forced adaptations in this delivery. The coefficient-subring
   existence theorem is eliminated only inside a proof of a proposition: no data
   definition chooses an arbitrary witness from an unproved existence theorem.
2. **Kernel proof — pass.** Compiled the module locally through `lcompile.py`
   without errors or warnings. Scanned it for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern` and `sorryAx`: none occurs. A scratch copy with
   `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for the
   private helper; the main theorem additionally has `sorryAx` from its existing
   open upstream dependencies. No new axiom or hole was introduced.
3. **Split statements — pass, none.** No statement was split off and no new
   node was added. Checked the helper mathematically: in characteristic zero a
   purely inseparable field extension is separable and hence its structure map
   is bijective; tensoring the resulting equivalence preserves regularity. This
   also covers the zero algebra, and the identity field extension. Checked
   integral contraction against Mathlib `Ideal.under_ne_bot`: the target is a
   domain and the base is nontrivial, precisely the hypotheses used here.
4. **Shortest route and pruning — pass after import cleanup.** Searched the
   library with alternative regularity/base-change terms, inspected the related
   DVR helper and Mathlib's purely inseparable bijectivity and ideal contraction
   results, and ran Loogle via `msearch.py` with `IsPurelyInseparable, CharZero`.
   No reusable public theorem closes this item directly. The direct Mathlib
   contraction route is shorter than the planned norm argument. The retained
   three Sheaf dependencies are all applied explicitly. Inspected the unit
   `sk-thm-p1` and its `realized` statement/steps: none is bypassed or changed.
   Every old proof dependency omitted by the new proof is listed above.
5. **DAG agreement — pass.** The node's proof steps, dependency union and proof
   origin describe the Lean argument, with exactly the coefficient-subring,
   finite-map quasi-finiteness and formal-fibre ascent nodes. All other existing
   node fields are unchanged; there are no new node-field requirements to check.

**Second-reader changes:** removed four redundant direct imports:
`Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Mathlib.RingTheory.Ideal.GoingUp`, `Mathlib.RingTheory.FiniteType`, and
`Mathlib.RingTheory.TensorProduct.Maps`. The last three were first-worker
additions and hence are not imports pruned against the repository baseline.
Each removal was tested in a scratch copy; the combined cleanup was compiled
again. The mathematical proof and node needed no repair. Updated this report to
record the import cleanup and the independent checks.

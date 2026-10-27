## What changed

Replaced the hole in `WeilConjectures.PodCompletionScalar.completionUnitScalarIntertwining`
by a proof from three strictly smaller construction/descent statements. The original
statement and all existing signatures are unchanged. Three predicate bodies now factor
through shared generic definitions, with exactly the same formulas by definitional equality. The assembly proves quotient
transition compatibility, specializes finite-free arithmetic exchange with its representative
normalization, transports the entire same-index unit equation to the actual adjunctions,
and proves the conjugation and inverse-unit identity by naturality and cancellation.

The three new modules work over arbitrary schemes with independent coefficient universes.
Only quotient-adjunction realization requires the invertibility of the coefficient prime
on the scheme; the assigned theorem supplies it from the finite-field characteristic.
No data definition is chosen from a new unproved existence assertion: the proof eliminates
all three existentials inside the proposition being proved. Every remaining hole is the
whole proof of a named theorem in its own module.

Validation: all five modules compile cleanly through the remote compiler, below the
60-second limit: shared definitions 46.1 s, quotient realization 35.9 s, same-index
descent 35.3 s, multiplication realization 36.2 s, and the final parent 39.4 s.
No profiling or increased-heartbeat options remain. The temporary probe is removed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PodCompletionScalar.completionUnitScalarIntertwining` (1 original hole).
This is a decomposition, not a complete proof of the mathematical construction: three
lower holes are added, and there are zero holes in the assigned module.

- `WeilConjectures.PodCompletionScalar.quotientAdjunctionRealization`
  (`lem-pod-quotient-adjunction-realization`, `Sheaf.Paper.PodQuotientAdjunctionRealization`).
- `WeilConjectures.PodCompletionScalar.scalarMultiplicationRealization`
  (`lem-pod-scalar-multiplication-realization`, `Sheaf.Paper.PodScalarMultiplicationRealization`).
- `WeilConjectures.PodCompletionScalar.sameIndexUnitDescent`
  (`lem-pod-same-index-unit-descent`, `Sheaf.Paper.PodSameIndexUnitDescent`).

The private helpers `quotientTransitions`, `normalizedScalarModel`,
`sameIndex_actual_unit`, and `conjugated_unit`
are fully proved. Factoring the repeated normalization formulas reduced the parent
kernel-conversion time from about 48 s to under 5 s. The new lemmas handle different genuine parts of the construction;
none includes the complete-input equality with arithmetic exchange or the final beta
identity. These are derived in the assigned module using their entire unit equations.

## No longer needed

The following proof-only direct imports are removed from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` (the proof uses
  `Sheaf.AlgebraicGeometry.ProEtaleProductsExact` instead).
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients`.
- `Sheaf.Paper.CompletedIntegralFiniteFree`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Mathlib.CategoryTheory.Localization.Predicate`.

Their mathematics remains needed inside the three stated construction steps, and the
new node dependencies retain it. The assembly uses the existing finite-free quotient
Roos exchange constructor with its normalization and actual ramification data rather
than repeating the generic finiteFreeCompletionExchange wrapper.

The parent no longer directly calls these nodes: `lem-pur-derived-change-of-rings`,
`lem-pur-kflat-change-of-rings-all-independent`,
`lem-trf-completion-unit-strict-quotient-model`, `lem-weil-completed-integral-finite-free`,
`lem-weil-integral-scalar-extension-well-defined`,
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-site-derived-tensor-descent`, `lem-weil-proetale-countable-products-exact`,
and `lem-weil-strict-roos-comparison`. They are either statement dependencies or
construction dependencies retained under the new nodes; the countable-products result
is supplied by `det-pe-products-exact` in the parent.

The new construction modules import only the shared formula module; its public imports
provide the types in their statements. No existing Lean module or declaration is withdrawn. All original public imports remain.
No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The nine-step plan is mathematically consistent, but the generic declarations cited in
steps 2, 3, and 5--7 do not themselves state the needed simultaneous normalizations.
The missing quotient realization, multiplication normalization, and same-index descent
are now explicit independent items, each with its full formula and proof in words.

The completed scalar comparison implementation already supplies a counit-normalized
cochain model, a positive ramification exponent, and an exchange constructor for any
chosen quotient models. Reusing those proved helpers avoids reconstructing them.
The explicit quotient-unit criterion also supplies completeness without a fresh
isomorphism-invariance lemma for the concrete completeness predicate.

Edge cases checked in the statements: zero complexes; first positive quotient index;
identity coefficient extension; and ramification index greater than one. The same-index
map is not asserted to be an isomorphism on incomplete inputs. The multiplication
lemma assumes the counit-compatible sigma, and the quotient realization keeps both the
whole-unit normalization and every representative counit formula.

## New nodes

`lem-pod-quotient-adjunction-realization` realizes parent step 2: any normalized principal
quotient model is compared with an actual normalized simultaneous reduction-limit
adjunction, with compatible strict towers, augmentations and counits.

`lem-pod-scalar-multiplication-realization` realizes parent step 3: the target quotient
and specified scalar towers agree by multiplication, including both signed cone
coordinates, the derived counit square, and the already specified scalar comparison.

`lem-pod-same-index-unit-descent` realizes parent steps 5--7: the balanced same-index
strict tower map has its canonical product and signed cone maps, descends naturally,
and satisfies the whole-unit equation on every derived object. It does not identify
that map with arithmetic exchange; the parent proves that on complete inputs.

`def-pod-completion-scalar-formulas` factors the three existing normalization predicates
into shared definitions over an arbitrary scheme. The assigned module keeps all old
names and signatures, specializing these exact bodies to its point. The change record is
`coord/changes/pod-completion-scalar-formulas.md`. It adds no holes.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

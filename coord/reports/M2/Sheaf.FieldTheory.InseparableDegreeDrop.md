## What changed

Filled the proof of `FieldExtension.exists_inseparableDegree_drop` in
`Sheaf.FieldTheory.InseparableDegreeDrop`, preserving its complete existing signature and
public imports. Added one proof import of the existing source module
`WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure`, and one of the new module
`Sheaf.FieldTheory.CoefficientRootExtension`.

The proof now performs the shortest Frobenius-chain argument, excludes exponential
characteristic one, applies the coefficient-root construction to the minimal polynomial,
proves finiteness over the new rational function field, obtains the transcendence-basis
property, and proves finite generation over the new constants. It specializes the already
proved source theorem `IsSeparable.of_pow_of_coeffs` to show beta becomes separable. Finally,
it constructs the embedding of `K_s(beta)` into the new relative separable closure, proves
the required compositum equality, and combines a compositum finrank bound with Mathlib's
`IntermediateField.finrank_lt_of_gt` to obtain strict decrease.

The four private helpers are proved, not assumed: `beta_exists`,
`separable_of_coeff_root`, `compositum_finrank_le`, and
`insep_lt_of_new_separable_element`. The existing theorem's existential instance binder
names cause unused-variable warnings after filling its proof; a declaration-scoped
`linter.unusedVariables` setting preserves that exact signature. No other linter is disabled.

The remaining construction is a theorem about an arbitrary polynomial over k(s). It assumes
only algebraic independence of s and prime characteristic. It assumes neither finite
generation nor finiteness of K/k(s), and asserts no degree inequality, no transcendence-basis
property and no finite generation. Thus it is strictly the coefficient-root part of the
argument, not the original theorem under another name. Its docstring gives the explicit
constant-root and variable-root construction and a complete proof in words.

## Proved and sorry left

Closed the original hole in `FieldExtension.exists_inseparableDegree_drop`
(node `lem-weil-pbc-inseparable-degree-drop`). No `sorry` remains in the item's module.

Added exactly one hole: `FieldExtension.exists_coefficientRoot_extension` in
`Sheaf.FieldTheory.CoefficientRootExtension`
(node `lem-weil-pbc-coefficient-root-extension`). Its whole proof is exactly `:= by sorry`.
There is no hole in a definition or private declaration.

This is a decomposition: one upper hole closed, one strictly smaller construction hole added;
net holes closed minus added is zero. All the connecting mathematics listed above is proved
in Lean. The other new node records the already proved source declaration
`IsSeparable.of_pow_of_coeffs` and adds no Lean declaration or hole.

The sandbox's two modules compile together without errors or warnings using `lcompile.py
--all`. Edge cases for the new construction were checked mathematically: P=0 and constant P
have zero or finitely many constant roots; s empty requires no rooted variables and remains
valid even when K/k is not algebraic; perfect k needs no nontrivial constant extension; and
finite-field/perfect-field cases do not assert a degree decrease. No assumption of a positive
transcendence degree is used. For the source lemma, e=0 and exponential characteristic one
reduce to ordinary separability under base extension. No nonseparable-extension assumption
is attached to that lemma.

## No longer needed

Removed the proof import `Sheaf.FieldTheory.SeparableRootPthPower`. A search of the current
library imports found the item was its only direct importer, so this module is pruned from
this route. Its node `lem-weil-pbc-separable-root-pth-power` is no longer a dependency of the
item. The existing source coefficient criterion proves the needed conclusion directly.

Removed `def-kun-transcendence-degree` from the item's proof dependencies: neither the proof
nor the new construction uses `Algebra.trdeg`. No other original Lean import was removed.
The temporary development imports `Mathlib.FieldTheory.IntermediateField.Algebraic` and
`Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure` were also removed as redundant;
the necessary declarations are already available through the retained public Mathlib import.

The item's old direct dependencies `def-pc-separable-polynomial`,
`def-weil-algebraic-closure`, and `lem-weil-pbc-algebraic-generators-finite-extension`
are now needed only inside the recorded source lemma or the new construction; they are
not claimed to be globally pruned. All other original mathematical dependencies are retained
where used, and `proof_deps` is the union of the updated proof steps' dependencies.

## Where the brief, the DAG or earlier work was wrong

The original plan's separate application of the p-th-root theorem is unnecessary:
`IsSeparable.of_pow_of_coeffs` already proves the needed separability implication in the
adopted source library. The new node records that existing declaration rather than
restating it. The original reference to `def-kun-transcendence-degree` was unnecessary:
that node records `Algebra.trdeg`, whereas this argument uses algebraic independence.

The original theorem's statement is unchanged and no mathematical error was found in it.
The construction and the degree argument remain below the unit level. None of the
`sk-thm-p1` realized unit statements or proof steps is bypassed or changed. No other group's
module was edited, and no interface change or forced adaptation was needed.

Searches included LeanFinder, Loogle, Mathlib grep and source-library grep. LeanSearch
returned an Internal Server Error and is recorded as unavailable without an absence verdict.
Mathlib provides the pure-inseparability power criterion, relative separable closure,
compositum rank bound, strict finrank inequality, and the algebraicity/basis criteria.
The source supplies `IsSeparable.of_pow_of_coeffs`. The source's
`MvPolynomial.exists_mapExpand_eq_pow` assumes an already given constant extension, and
`Field.exists_finiteDimensional_pow_eq` does not assert pure inseparability or compatible
rooted variables, so neither discharges the remaining construction by specialization.

The local literature checkout lacks `literature/stacks-project/algebra.tex` and `fields.tex`.
The actual source paragraphs were read at [Stacks 04KM](https://stacks.math.columbia.edu/tag/04KM)
and [Stacks 031V](https://stacks.math.columbia.edu/tag/031V); the coefficient-root details
omitted by 04KM are expanded in the new node and docstring. The node proof origins are
marked agent-written. WANTED: local copies of Stacks Algebra Tag 04KM and Fields Tag 031V
for the new nodes' source files.

## New nodes

`lem-weil-pbc-coefficient-root-extension` is the sole new open construction, in
`lean/Sheaf/FieldTheory/CoefficientRootExtension.lean`. It isolates the finite constant-root
and variable-root construction for arbitrary P. The parent proves its finiteness-over-E₁,
transcendence-basis, finite-generation and strict-degree consequences. Its source is the
coefficient-root paragraph of Stacks 04KM, with the rational-function and algebraic-
independence details written out. It creates one hole.

`lem-weil-pbc-separable-of-power-coefficients` records the exact existing source theorem
`IsSeparable.of_pow_of_coeffs` in
`WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure`. Its signature is copied
verbatim from the source. The proof uses coefficientwise iterated Frobenius and polynomial
separability and has no `sorry`. This node creates neither a module nor a hole. Its source
is the coefficientwise Frobenius argument of Stacks 031V and the proved source-library
minimal-polynomial variant. There are no change records because no existing signature or
public import changed.

## Second reading by M2

1. Compared both delivered modules against the repository versions. The existing theorem signature is byte-for-byte unchanged; the only added declaration is the separately stated coefficient-root construction, and no target or existing declaration was weakened.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no errors or warnings. The original theorem has no `sorry`, and the only remaining `sorry` is the named public construction theorem, with its matching node and complete proof docstring. No forbidden declarations or hollow definitions occur.
3. Checked the new construction statement against edge cases (empty and constant tuples, zero and constant polynomials, perfect fields, and finite fields). It asserts only the finite purely inseparable construction and coefficient property, without importing the parent theorem's finiteness or degree conclusions. Searched the source and library for duplicates; none exists. The recorded source and node agree with the declaration.
4. Read the proof from the target downward. It uses the shortest Frobenius-chain argument, the existing source separability criterion, and Mathlib rank and separable-closure results. The obsolete separable-root import and transcendence-degree dependency were removed; the coefficient-root theorem is the sole deliberate split-off. The unit `sk-thm-p1` route and realized steps remain intact.
5. Compared the item node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof and checked the new node's required metadata, Lean record, source, and proof steps. The updated dependencies exactly match the declarations used by the proof.

I changed only the report by adding this second-reading record; no proof or statement changes were needed after compilation.

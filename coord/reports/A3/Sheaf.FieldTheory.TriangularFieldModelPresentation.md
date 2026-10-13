## What changed

Wrote a reduction of `FieldTheory.exists_triangularFieldModel_presentation` to
`FieldTheory.exists_triangularFieldModel_evaluation_kernel` in a new proof-only import
`Sheaf.FieldTheory.TriangularFieldModelEvaluationKernel`. The new statement is about an
arbitrary finite family, without a hypothesis that it generates K; it only constructs
relations and identifies their evaluation kernel. The original module supplies the
quotient map, proves its injectivity, and derives all fraction representations from
Mathlib `IntermediateField.mem_adjoin_iff_div`. Existing signatures, definitions,
visibility and public imports are unchanged. Updated the original node's proof route.

The Mathlib-only scratch checks `scratchpad/Fractions.lean` and
`scratchpad/Assembly.lean` validate the quotient/fraction argument and the assembly
against an abstract equation list. Earlier actual module compiles were blocked:
the shared last-green build lacks
`Sheaf/FieldTheory/TriangularFieldModelEquations.olean`. No missing library source was
copied or built as a workaround.

## Proved and sorry left

One original hole is closed by a compiled reduction:
`FieldTheory.exists_triangularFieldModel_presentation`
(node `lem-weil-pbc-triangular-field-model-presentation`). This is a decomposition,
not an unconditional proof or a positive net reduction of holes. Both actual modules now compile through lcompile.py against the published library.
The following earlier retry notes are historical; the missing dependency is now available.

One new hole remains:
`FieldTheory.exists_triangularFieldModel_evaluation_kernel`
(node `lem-weil-pbc-triangular-field-model-evaluation-kernel`). It retains the tower,
denominator clearing and injectivity portion of the source argument, with its complete
proof in words. No holes occur inside definitions or the original theorem's proof.

## No longer needed

No imports or dependency modules are pruned. The original public imports are needed
for the signatures: in particular `RegularSequence` supplies `Ideal.ofList`.
The original top node no longer directly calls the minimal-polynomial, monic-quotient,
tower-basis and localization lemmas; those remain needed by the new evaluation-kernel
node and are not claimed as pruned. The final expansion of arbitrary z in the monomial
basis and a second common-denominator construction are unnecessary; Mathlib's field
adjoin fraction characterization supplies that part.


Old direct proof dependencies removed from the top node (retained in the new
kernel node, so no dependency module is claimed pruned):

- `def-weil-algebraic-element`
- `def-weil-pbc-free-module`
- `def-weil-pbc-transcendence-basis`
- `def-weil-pbc-triangular-field-model-equations`
- `def-weil-ring-localization-away`
- `lem-weil-pbc-localization-away-polynomial-quotient`
- `lem-weil-pbc-minimal-polynomial-quotient-field-iso`
- `lem-weil-pbc-monic-quotient-free`
- `lem-weil-pbc-polynomial-ring-domain`
- `lem-weil-pbc-tower-product-basis`

## Where the brief, the DAG or earlier work was wrong

The source and compiled last-green library differ: `TriangularFieldModelEquations`
is present in the repository but absent from the shared compiled library. Both actual
compile attempts fail at that import before elaborating any declarations.
The process requires waiting for the next green build instead of recreating it.

Dispatcher retry on 2026-10-13 reproduced the same missing-object error with both
`lcompile.py --all` and `deliver3.py A3
Sheaf.FieldTheory.TriangularFieldModelPresentation --no-push`. The dry run stopped
at local compilation and pushed nothing. The existing reduction and node files
remain saved for the next retry after the compiled dependency is published.

The kernel lemma was checked on m = 0 (h = 1, T = 1), d = 0 (base field k), repeated
or zero generators (linear minimal polynomials), and inseparable extensions (no
separability enters division or the power basis). Since it is about arbitrary finite
families, the final tower need not equal K; the original generating-family hypothesis
is used only in the proved fraction argument.

Read Stacks Tags 07BV and 08JZ online because the local algebra.tex is absent.
The existing source annotation incorrectly calls 08JZ `lemma-localize-at-element`;
the displayed localization presentation itself is the part used. Whole-blueprint
search for triangular found no matching statement. LeanFinder and grep found only
ingredients; LeanSearch was unavailable and is recorded as unavailable.

## New nodes

`lem-weil-pbc-triangular-field-model-evaluation-kernel`, in
`Sheaf.FieldTheory.TriangularFieldModelEvaluationKernel`, isolates the evaluation kernel
of an arbitrary finite algebraic tower. It gives no field-wide fraction conclusion,
and the original theorem constructs the quotient injection and fraction witnesses
in approximately sixty lines of Lean. It is sourced to the minimal-polynomial and
localization portions of Stacks 07BV/08JZ and keeps the blueprint unit route unchanged.
No statement, definition or interface change records are needed.

Retry verification (2026-10-13, third dispatcher attempt): the dependency source
`lean/Sheaf/FieldTheory/TriangularFieldModelEquations.lean` compiled as a single file
through `lcompile.py` (exit 0), but this does not publish its object into the shared
last-green library. Both sandbox `lcompile.py --all` and the required
`deliver3.py --no-push` still fail at the missing shared
`Sheaf.FieldTheory.TriangularFieldModelEquations.olean`, before proof elaboration.
No dependency was copied into the sandbox, no shared build was changed, and nothing
was pushed. The preserved reduction still awaits publication of the dependency.

Fourth dispatcher retry (2026-10-13): reviewed the preserved Lean reduction and
re-ran `lcompile.py --all` and `deliver3.py A3
Sheaf.FieldTheory.TriangularFieldModelPresentation --no-push`. Both exit 1 before
proof elaboration because the published shared build still lacks
`Sheaf/FieldTheory/TriangularFieldModelEquations.olean`. The dry run reports
"COMPILE FAILED (local), nothing pushed". Per roles/worker.md §2.2, the missing
compiled dependency is not recreated or copied into this delivery. No proof or
node changes were made in this retry; the reduction remains unverified against
the actual dependency pending its publication.


## Second reading by A3

1. Compared every delivered existing Lean module with the repository by diff and
   checked the original theorem signature byte for byte: identical. Only its
   proof, docstring, and a plain proof-only import change. No definitions or
   target interfaces change; no change record is required. Verdict: pass.
2. Both actual modules compiled with lcompile.py --all. A scratch copy with
   #print axioms for both declarations compiled and printed exactly propext,
   Classical.choice, Quot.sound, and sorryAx. The latter is from the single
   named kernel theorem. No forbidden declarations or data from an unproved
   existence theorem occur; all quotient data is constructed with liftₐ.
   Verdict: pass as a decomposition, not an unconditional proof.
3. Read the kernel theorem, its full word proof, and its node. Tested m = 0
   (h = 1, T = 1), d = 0 (base field k), zero/repeated generators (linear
   polynomials), and inseparability (power bases do not require separability).
   The arbitrary family need not generate K. The lemma omits the field-wide
   fraction conclusion and isolates the tower/kernel portion; the original
   theorem proves the quotient and fraction argument in Lean, so this is a
   strict part of the argument rather than a renamed original theorem.
   Fresh LeanFinder search for kernels of algebraic-element evaluation found
   localization and presentation ingredients, including
   Algebra.Generators.ker_localizationAway, but no whole kernel lemma. Loogle
   confirmed IntermediateField.mem_adjoin_iff_div; rg on the library and
   Mathlib found no duplicate triangular kernel theorem. Read Stacks 07BV
   and 08JZ online and checked the source argument. Verdict: pass; the kernel
   proof is substantial and cannot be closed in a few minutes.
4. The proof uses Mathlib's fraction characterization directly and needs no
   extra denominator statement. All public imports supply signature notions;
   the kernel module is imported plainly for the proof. No module is pruned;
   every old direct proof dependency removed is listed above and remains in
   the kernel node. Checked dag/units/sk-thm-p1.json realized: neither the
   original nor the new node realizes a unit statement or step, and no route
   at the unit level is changed. Verdict: pass.
5. Parsed the old and new original node records: exactly proof, proof_deps,
   and proof_origin differ. The new node has its source, full proof steps,
   dependency union, searches, created record, chapter, unit, blueprint, and
   verbatim Lean statement. Checked these against both Lean modules.
   Verdict: pass.

Second reading changed the report to record successful actual compilation,
explicitly enumerate all removed direct proof dependencies, and add this review.
Corrected the new kernel module and node's inaccurate name for Stacks Tag 08JZ
(the cited localization presentation itself is correct). The proof and all
statements are unchanged. One original hole is closed and one named kernel
hole is added: net zero holes, one decomposition, no pruned modules.

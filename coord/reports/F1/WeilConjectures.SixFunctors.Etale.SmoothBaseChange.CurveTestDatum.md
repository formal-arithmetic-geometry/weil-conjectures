## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.exists_not_isZero_higherDirectImage_constantModSheaf`
with a proof combining prime cyclic detection and ring-quotient detection. Its signature and
all other declarations in the assigned module are unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection` and
`Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection`.
Each new module contains one public intermediate theorem. Updated the proof route and
proof dependencies of `sbc-lem-bc-universal-test`; the normalization, integral transport,
injectivity and final datum construction are retained.

Validation: all three sandbox modules compile together using lcompile, with no errors or
non-sorry warnings. The parsed module diff reports one original sorry closed and no
interface change. The delivery dry run supplies the local axiom probes and server checks.
Mathlib searches ran through msearch: LeanFinder, Loogle and source grep, plus LeanSearch
which returned Internal Server Error and is recorded as unavailable. The source-library and
Sheaf searches found related cohomology/base-change comparisons, but none states the two
coefficient steps at these signatures. Read Stacks 0F08, 03FD and 0739 online; the local
literature checkout on this machine contains citation metadata rather than their full text.

## Proved and sorry left

Proved from the two intermediate declarations:
`AlgebraicGeometry.Etale.exists_not_isZero_higherDirectImage_constantModSheaf`.
The assigned module has zero direct sorries, compared with one before. Its proof obtains
`r`, primality, divisibility, noninvertibility and prime-field nonvanishing from the first
lemma, chooses `d = r`, and contradicts a putative zero Lambda-quotient image by applying
the second lemma. This is a reduction, not a claim of a sorry-free transitive axiom closure.

Two sorries remain in newly added modules, exactly as whole named theorem proofs:

- `AlgebraicGeometry.Etale.exists_prime_cyclic_higherDirectImage`
  (`lem-sbc-prime-cyclic-detection`): forget the Lambda-action, identify the sheaf on the
  geometric point with a constant module, use finite primary cyclic decomposition and qcqs
  filtered colimits, and detect nonvanishing over a prime field. It does not produce the
  desired Lambda/rLambda coefficient; that is the second step.
- `AlgebraicGeometry.Etale.isZero_prime_cyclic_higherDirectImage_of_quotient`
  (`lem-sbc-prime-quotient-detection`): Lambda/rLambda is a nonzero F_r-vector space because
  r is not a unit, so F_r is its additive retract; pass the retract through abelian higher
  direct image and the module/abelian comparisons. It does not find a prime or reduce an
  arbitrary sheaf on a geometric point.

Edge cases: the zero ring makes the first premise impossible; a prime that is a unit must
not be used in the second step (the quotient would be zero). For n = 1 the first premise
is likewise impossible. For negative q all the images vanish, making detection vacuous.
For q = 0 the same coefficient/retract argument uses ordinary direct image. Empty Y or X
forces vanishing. No nontriviality, degree positivity or invertibility-on-the-base assumption
was added to the original signature. Neither new theorem requires smoothness or properness;
qcqs is required only by the colimit/detection step.

## No longer needed

None. No existing import was removed. Both new imports are used in the final proof. No
geometric node or unit step is pruned: field failure, integral surjective extension,
normalization, integral base transport and injectivity are kept. The proof does not require
an asserted Lambda-linear decomposition of an arbitrary module into Lambda/dLambda.

## Where the brief, the DAG or earlier work was wrong

The repository has no node whose lean.module records the assigned source module; the
blueprint reference in its docstrings leads instead to `sbc-lem-bc-universal-test`, whose
lean_audit and lean attachment do not currently name these declarations. Its proof route
was updated without changing its statement or adding a potentially mismatched attachment.

The source and existing docstring distinguish abelian cyclic coefficients from the
Lambda/dLambda coefficients of the general-ring Lean formulation. A decomposition as
Lambda-modules into such quotients would be unjustified; the reduction now explicitly
forgets coefficients and transfers through a prime-field retract. Also the old DAG text
invokes only finite sums and retracts for an arbitrary bounded-torsion module; the detection
step records the required qcqs filtered-colimit argument. The original docstrings and
signatures were preserved. No statement is disputed.

The planned proofs use the existing generic tools
`lem-sc-coprime-torsion-decomposition`,
`lem-weil-pbc-injective-module-direct-image-acyclic`,
`lem-weil-pbc-derived-functor-long-exact`,
`lemma-weil-pbc-direct-image-filtered-colimit`, and the constant-sheaf comparisons.
These are tools for the coefficient subargument, not replacements for the universal-datum
unit's geometry. Their Lean encodings do not directly match the present ModuleCat bounded
below functors, so the new intermediate declarations record the missing comparison/glue.

## New nodes

`lem-sbc-prime-cyclic-detection`, in
`lean/Sheaf/AlgebraicGeometry/SmoothBaseChange/PrimeCyclicDetection.lean`, records the
underlying-abelian prime detection step. Its source is the cyclic-coefficient sentence in
0F08, with 03FD and qcqs colimits; its docstring and node give the full mathematical proof.

`lem-sbc-prime-quotient-detection`, in
`lean/Sheaf/AlgebraicGeometry/SmoothBaseChange/PrimeQuotientDetection.lean`, records the
nonzero vector-space retract and coefficient-comparison step. This is the explicit
arbitrary-Lambda completion of that source sentence. Its docstring and node give the full
mathematical proof. No change record is needed: the existing interface is unchanged and
the new modules are imported only for proofs.

## Second reading by F1

1. **Interface check.** Compared `CurveTestDatum.lean` with the repository version. Existing
   declarations and signatures are unchanged byte-for-byte; only the target proof and two
   proof-only imports differ. Verdict: pass.
2. **Proof check.** Compiled all three delivered modules with `lcompile --all`; compilation
   succeeds. The target theorem has no direct `sorry`; the only remaining sorries are the two
   explicitly named split-off theorems, each public, documented, and matched by a DAG node.
   Verdict: pass, subject to those stated open lemmas.
3. **Split statements.** Checked both new theorem signatures against their docstrings and DAG
   nodes. They are coefficient reductions strictly below the target and preserve the required
   hypotheses (including primality and noninvertibility); no duplicate library declaration was
   found. Edge cases are recorded above. Verdict: pass.
4. **Pruning and route.** The proof uses both new declarations and retains the normalization,
   integral transport, injectivity, and final datum construction. No prior proof dependency or
   import is unused, and the unit route remains intact. Verdict: pass.
5. **DAG agreement.** Updated target proof/proof_deps and supplied matching new-node `lean`
   records, statements, sources, and proof routes. Verdict: pass.

Changed during second reading: no Lean declarations or statements; added this review record only.

Additional second-reading evidence: explicitly ran `#print axioms` for the closed coefficient
statement and both split statements through an lcompile scratch probe. Each reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; there are no additional axioms.
Read Stacks [0F08](https://stacks.math.columbia.edu/tag/0F08),
[03FD](https://stacks.math.columbia.edu/tag/03FD), and
[0739](https://stacks.math.columbia.edu/tag/0739). The first supplies the cyclic reduction;
the second compares module and abelian cohomology on every object; the third supplies
filtered-colimit commutation under finite-cover hypotheses, applicable to the qcqs etale
sites here. For prime detection, the exact degree-q segment with vanishing outer terms gives
vanishing for each prime-power coefficient; no vanishing in adjacent degrees is needed.
For quotient detection, noninvertibility makes the quotient proper and its unit vector
nonzero, and a field-linear coordinate projection provides the additive retract.

Independent searches used different wording: LeanFinder for cohomology preserving additive
retracts and filtered unions of finite torsion subgroups returned group-cohomology results,
none matching these etale coefficient comparisons; Loogle could not resolve
`CategoryTheory.IsZero`; source grep for retract/cohomology and prime/constant returned no
matching theorem. Repository searches located
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists` in
`HigherDirectImage/CohomologyPresheaf.lean`, but it assumes local annihilation of every
cohomology class for every divisor, rather than providing either new implication. The
upstream CurveTestDatum likewise leaves the original coefficient theorem open. Thus neither
split statement can be closed by a direct application of a declaration found in this review.
The unit record's `realized` lists are empty in the repository; they were not changed, and
the written geometric route is preserved. All old `proof_deps` remain in the new route.

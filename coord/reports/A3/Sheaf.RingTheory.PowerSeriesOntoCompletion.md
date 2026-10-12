## What changed

Proved `MvPowerSeries.exists_surjective_toAdicCompletion` in
`Sheaf.RingTheory.PowerSeriesOntoCompletion`, without changing its signature.
Added proof-only imports of `Mathlib.RingTheory.MvPowerSeries.Equiv` and
`Mathlib.RingTheory.MvPolynomial.Homogeneous`. The existing public imports remain needed
by the statement. A proved local fact `eval_mem_pow` sends powers
of the variable ideal into powers of I. Quotient truncation ring maps lift to the
completion; homogeneous polynomials for successive Cauchy-sequence differences
assemble into a series, and a finite telescoping sum proves surjectivity.
Generator and constant images are proved by projection extensionality.
The node proof now records this implementation, including the degree-zero correction
and the initial constant r(0). The unit route is unchanged.

## Proved and sorry left

Closed: `MvPowerSeries.exists_surjective_toAdicCompletion` (1 of 1 original holes).
Added holes: none. Remaining holes in the delivery: none. No new nodes or modules.
The local fact `eval_mem_pow` is also fully proved.
Local compilation is clean. The required delivery dry run checks the axioms of all file declarations.
The current delivery tool skips server compilation by default; the global build
verifies the delivered module after landing.

## No longer needed

None. No existing import, DAG dependency, node, or module is pruned.
No proof uses an intermediate Sheaf declaration. Both existing proof dependencies
are the Mathlib-backed definitions of completion and multivariate power series.
An exploratory sandbox module was removed and is not delivered.

## Where the brief, the DAG or earlier work was wrong

No statement error. The five-step plan is realizable entirely from Mathlib.
Its explicit multiplicativity calculation is supplied by `truncTotalAlgHom`.
For surjectivity the implementation uses all differences starting at m=0,
and adds C(r(0)); this gives the same telescoping series as the planned
initial constant r(1). It works for n=0, the zero ring, I=0, and I=top.
Level zero is handled by the trivial quotient and the variable at level one by
membership f_i in I. No target signatures, definitions, or existing statements change.
The local literature copy is absent; the sources were read at
https://stacks.math.columbia.edu/tag/0316 and https://stacks.math.columbia.edu/tag/05GH.
Searches via msearch leanfinder, loogle, and grep found the Mathlib ingredients,
but no existing theorem with the full statement. Library text searches found only
this statement and its callers.

## Second reading by A3

1. **Existing statements and definitions — pass.** Read the full module and its
   diff against the repository. The existing theorem signature is byte-for-byte
   identical, its docstring is unchanged, and no definition or public import
   changes. The two added imports are proof-only. No change record is needed.
2. **Proof and axioms — pass.** Local compilation is clean. A scratch copy with
   `#print axioms MvPowerSeries.exists_surjective_toAdicCompletion` reports only
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, axiom,
   unsafe declaration, opaque declaration, extern, implemented_by, or kernel-check
   bypass. Read compatibility, homogeneous coefficient assembly, telescoping,
   and the images of variables and constants in full. The degree-zero correction
   together with C(r(0)) evaluates to r(1), as required.
3. **Split-off statements — pass (none).** No new holes or modules are added.
   Checked the local power-membership argument at m=0 and the construction at
   n=0, I=0, I=top, and for the zero ring: the degree-zero quotient is trivial;
   positive degrees in zero variables vanish; no nontriviality, Noetherian, or
   completeness assumption is used. Repeated searches with different wording
   through msearch LeanFinder, Loogle, and grep, plus rg in Sheaf and the upstream
   library. No theorem with the whole statement or exact helper was found.
4. **Route and pruning — pass.** Read the two Mathlib-backed proof dependencies,
   the Mathlib truncation quotient homomorphism and homogeneous-evaluation lemma,
   and dag/units/sk-thm-p1.json including its realized fields. The proof implements
   the five mathematical steps and bypasses no unit. Equiv provides
   truncTotalAlgHom and truncation compatibility; Homogeneous provides the
   homogeneous representatives. Both public imports occur in the statement.
   The old proof_deps are both retained and used; No longer needed is complete.
   An alternative through completion of polynomials would require extra
   change-of-ideal transport, so it does not simplify this proof.
5. **DAG agrees — pass.** The only node changes are proof and proof_origin;
   proof_deps is unchanged and equals the union of the steps' uses. The new proof
   record accurately describes the quotient homomorphisms, all successive
   differences starting at zero, addition of C(r(0)), telescoping, and generator
   and constant images. Statement, source, lean signature, and unit are retained.

Second-reading repairs: moved the fully proved private eval_mem_pow helper into
exists_surjective_toAdicCompletion as a local fact, so no separate declaration
without its own node is introduced. Its argument and all uses are unchanged.
Corrected the report's server-compilation claim: deliver3.py currently skips that
compile by default and the global build verifies landings. No mathematical proof,
statement, definition, import, or dependency was otherwise changed.

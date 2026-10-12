## What changed

Proved `Rep.exists_finite_primary_decomposition` in
`Sheaf.RepresentationTheory.FinitePrimaryDecomposition`, preserving its signature and visibility.
Added proof-only imports of `Mathlib.Algebra.Module.PID`,
`Mathlib.Algebra.DirectSum.Decomposition`, and `Mathlib.RingTheory.Int.Basic`.
Mathlib gives a finite internal decomposition into prime-power torsion submodules.
The proof constructs their restricted continuous actions, proves canonical projections
are equivariant by checking each summand, and proves the required finite sum pointwise.
The existing proof-only `AdditiveFunctor` import is used to pass sums through the
full-subcategory inclusion. Updated the existing node's proof and proof_origin to this route.

Searches: LeanFinder found `Submodule.exists_isInternal_prime_power_torsion_of_pid`;
Loogle confirmed its signature; msearch grep found this theorem and
`DirectSum.decompose_lhom_ext` / `DirectSum.sum_support_decompose`.
Local searches of both library roots found no existing representation-level result.
The unit `sk-prop-cd-affine` has no realized node that this route bypasses.

## Proved and sorry left

Closed the sole original hole: `Rep.exists_finite_primary_decomposition`
(node `lem-sc-finite-discrete-rep-primary-decomposition`).
No holes added, no statements split off, and no sorry remains in the delivery.
This is a complete proof from Mathlib, not a decomposition into unproved statements.
Local compilation passed without warnings. The delivery dry run checks its axioms.
The construction handles arbitrary representation universe v and group universe u;
empty index families, zero modules, and zero exponents require no extra hypothesis.
The submodules and actions are concrete. The decomposition inverse is chosen only
from a proved bijectivity theorem, which uniquely determines it.

## No longer needed

None of the existing imports, nodes, or modules were removed.
The explicit exponent factorization and CRT coefficient construction from the old
proof plan are unnecessary: Mathlib's proved internal decomposition supplies their result.
No Sheaf proof-dependency modules are imported, and no additional DAG work is left.

## Where the brief, the DAG or earlier work was wrong

No statement or interface error found. The DAG's original one-paragraph proof had
no recorded proof dependencies. Mathlib already supplies its algebraic decomposition,
so the delivery uses that API and records the representation and categorical glue explicitly.
The original source path in the node is not present in this local literature checkout;
the node and declaration docstring contain the source's primary-decomposition argument.
The existing declaration docstring is retained as its original CRT proof explanation.

## Second reading by M3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-only imports and the theorem proof changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly with no warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only original hole is closed. Verdict: pass.
3. Read each proof step and checked the edge cases, including empty index families and the zero representation. The Mathlib internal decomposition theorem is applied to the finite torsion module, and the restricted actions and projections are explicitly constructed. No new statement was split off, and the existing statement is unchanged. Verdict: pass.
4. Checked the proof route and imports. The route uses Mathlib's PID internal primary decomposition and retains the full-subcategory additive-functor glue needed by the categorical sum. No old proof dependency or import is unused, and no unit step is bypassed. Verdict: pass.
5. Checked the DAG node against the Lean proof. Its proof steps and proof origin describe the internal decomposition, invariant restrictions, equivariant projections, pointwise sum, and categorical reindexing used in the module. The unit `sk-prop-cd-affine` route remains represented. Verdict: pass.

Changed after reading: added this second-reading record only; no Lean statements, definitions, or proof content required repair.

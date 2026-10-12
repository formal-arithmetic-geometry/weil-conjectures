## What changed

Proved `MvPolynomial.graded_submodule_finite` in
`lean/Sheaf/RingTheory/GradedSubmoduleFinite.lean`, without changing its signature or docstring.
Added proof-only imports `Mathlib.RingTheory.Polynomial.Basic` (Hilbert basis theorem) and
`Mathlib.RingTheory.PrincipalIdealDomain` (the Noetherian instance for the field).

The proof follows the existing two-step DAG plan. Forgetting homogeneity in `hN` gives
`Module.Finite`; `IsNoetherian.noetherian` gives a finite generating finset for `K`.
Take the finite union of the supports of the generators' direct-sum decompositions, mapped to
components. Every resulting element is homogeneous and lies in `K` by `hK.mem_iff`.
Conversely `DirectSum.sum_support_decompose` expresses each original generator as a sum of
these elements, proving the opposite span inclusion. This argument includes zero submodules
and empty generating finsets. The scalar-grading compatibility is retained in the signature;
it is unnecessary for this argument because component closure is already assumed by `hK`.

Searches: LeanFinder for finite homogeneous generating sets found the analogous finite-type
algebra result but no submodule result. Loogle `Submodule.FG` found `Submodule.fg_def` and
`Module.Finite.of_fg_top`. The launcher grep query `sum_support_decompose|IsHomogeneous.*FG`
found the direct-sum recomposition theorem. Local searches of both library roots found no
already-proved replacement. Read the ungraded dependency's Mathlib specialization and used it
directly. The node proof, dependencies, and unit route remain unchanged.

Validation: compiled the delivered module through `lcompile.py` with no warnings.

## Proved and sorry left

Closed one hole: `MvPolynomial.graded_submodule_finite`
(node `lem-sc-p1-graded-submodule-finite`).
No `sorry` remains in the module; no holes or new declarations were added.

## No longer needed

None. No original imports or planned dependency nodes were removed. The ungraded dependency
`lem-sc-p1-ungraded-submodule-finite` is a Mathlib leaf and is realized using its recorded
Noetherian instances and `IsNoetherian.noetherian` directly, without a wrapper module.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The Mathlib instances needed for the ungraded step require
proof-only imports absent from the original module. In particular, the field's Noetherian
instance is supplied through `Mathlib.RingTheory.PrincipalIdealDomain`.


## Second reading by K3

1. **Visible declarations: pass.** Read the complete delivered module and compared it with
   `lean/Sheaf/RingTheory/GradedSubmoduleFinite.lean` using `diff -u`. The sole existing
   declaration, `MvPolynomial.graded_submodule_finite`, has a byte-for-byte unchanged signature
   and docstring. Only its proof and two plain, proof-only imports differ. No definitions,
   public imports, new declarations, or change records are delivered.
2. **Proof: pass.** Independently compiled the module through `lcompile.py` without errors or
   warnings. A scratch copy with `#print axioms MvPolynomial.graded_submodule_finite` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`. The delivered module contains no
   `sorry`, forbidden axiom declaration, unsafe implementation, or definition with missing
   data. `chooseDecomposition` constructs the inverse of the bijection certified by `hℳ`;
   this uniquely determined decomposition is not an arbitrary existential witness.
   `hN` supplies finite generation of the ambient module, and the Noetherian instances give
   the finite finset `s` spanning `K`. Each member of `t` is a component of a member of `s`:
   its subtype property proves homogeneity, and `hK.mem_iff` proves membership in `K`.
   Conversely, `sum_support_decompose` expresses each member of `s` as a sum in the span of
   `t`. Thus both span inclusions are justified. Empty finsets, `N = 0`, and `K = 0` require
   no nonzero hypothesis. The unused scalar-compatibility hypothesis stays in the signature.
3. **Split-off statements: pass (none).** No holes or statements were added, so there is no
   restatement, new node, or split-off theorem to validate or close. Independently searched
   both library roots for homogeneous finite generation and used launcher grep with
   `IsHomogeneous.*(fg|finite)|(fg|finite).*IsHomogeneous` (zero hits). Read the nearby proved
   `exists_finite_homogeneous_generators`: it constructs a surjective graded free cover of a
   finite ambient module, rather than directly providing finite homogeneous generators of
   a submodule. Using it here would require constructing the submodule's internal grading;
   it offers no shorter route than the component argument already written.
4. **Route and pruning: pass.** Read the graded node, its ungraded Mathlib leaf, and
   `dag/units/sk-thm-picard-duality.json`. The proof realizes the existing two-step node plan
   without changing the unit route or its `realized` fields. The sole old proof dependency,
   `lem-sc-p1-ungraded-submodule-finite`, is used through the Mathlib instances and
   `IsNoetherian.noetherian` recorded on that leaf. Therefore `No longer needed: None` is
   complete. Each original public import supports notions in the unchanged signature.
   Scratch copies deleting either added proof-only import fail to synthesize
   `IsNoetherian (MvPolynomial (Fin 2) k) N`, confirming both are needed for this proof.
5. **DAG consistency: pass.** The existing `proof`, `proof_deps`, and `proof_origin` describe
   precisely the Noetherian finite-generation step followed by collecting components.
   No node update is required, and there are no new nodes. The cited blueprint file is not
   present in this machine's repository; this review checked the unchanged source-bearing
   docstring, node proof and source record, and unit record, without claiming a fresh check
   of that absent source document.

Second reading changed only this report, adding the independent review and validation
results. The Lean proof was correct and was retained without rewriting.

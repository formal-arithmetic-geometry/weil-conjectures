## What changed

Proved `KaehlerDifferential.D_eq_zero_iff_exists_pow_of_perfectField` with its signature
and public imports unchanged. The private `adjoin_pow_eq_range` proves kK^p=K^p over a
perfect base. Transported `Field.exists_p_basis` from the prime-field coefficient
subfield using `Module.Basis.mapCoeffs`, applied the existing differential-basis lemma,
and reconstructed a from its sole constant coordinate. The reverse implication is
Leibniz in characteristic p.

Added `Sheaf.FieldTheory.PBasisZeroDifferentialCoefficients`, containing the fully proved
`KaehlerDifferential.pBasis_repr_eq_zero_of_D_eq_zero` and its private Euler-monomial
helper. The partial derivation dual to dt_i, multiplied by t_i, acts diagonally on
monomials with eigenvalue E_i; basis extensionality and scalar cancellation prove that
nonconstant coefficients vanish. This avoids reindexing reduced exponents. Updated the
parent proof node and added the node for the proved coefficient lemma. All new proof
imports are non-public. No definitions, existing signatures, or targets changed.

## Proved and sorry left

Closed the one original hole:
`KaehlerDifferential.D_eq_zero_iff_exists_pow_of_perfectField`
(node `lem-weil-pbc-differential-zero-iff-pth-power`).
Also fully proved `KaehlerDifferential.pBasis_repr_eq_zero_of_D_eq_zero`
(node `lem-weil-pbc-p-basis-zero-differential-coefficients`).
No sorry remains in either delivered module; no holes were added or split off.

The main theorem still uses the existing named statements `Field.exists_p_basis` and
`KaehlerDifferential.exists_basis_differentials_of_pBasis`. At second reading,
`Field.exists_p_basis` has a proof using `FieldTheory.exists_pBasis_extension`; the
differential-basis theorem still has its original sorry. Their remaining proof
dependencies are the responsibility of their own items. The new coefficient theorem uses only its stated
basis hypotheses and Mathlib. Its explicit `#print axioms` check reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. Both modules compile together through
`lcompile.py --all` without errors or warnings.

## No longer needed

None: both original proof-dependency imports and all three original proof-dependency
nodes remain needed. No existing module is pruned. The Euler argument replaces only
the reduced-monomial reindexing calculation within step 4, not a blueprint unit or
an existing dependency node. Every import retained is used by a statement or proof. Second reading removed the
unused proof-only `Mathlib.Algebra.CharP.Algebra` import from the new coefficient
module; it remains needed in the main module. No DAG dependency is removed by this
Mathlib import cleanup.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned coefficient calculation had no separately
stated Lean declaration; it is now a proved generic theorem over arbitrary base fields
of characteristic p. Checked its edge cases: empty I has no nonzero exponent E;
p=2 permits scalar E_i=1; infinite I is covered by finite supports; exponent zero is
excluded as required because constants can have nonzero coordinates. The blueprint
unit `sk-thm-p1` and its realized steps remain unchanged.

LeanSearch returned an Internal Server Error; LeanFinder, Loogle, and local source
searches were available. Read the Stacks 07P1/07P2 source in the local literature cache
and used its dual partial derivations, multiplied by t_i.

The prescribed delivery dry run failed before preflight: `deliver3.py` calls
`check_import_sources`, which imports `refuse_missing` and `source_roots` from
`tools/import_cycles.py`; the repository version does not export `refuse_missing`.
Python raises `ImportError: cannot import name 'refuse_missing' from 'import_cycles'`.
No delivery was pushed, and no project/tool files were edited to bypass this failure.
The sandbox proof and DAG files are complete for a second reader once the tool is fixed.

## New nodes

`lem-weil-pbc-p-basis-zero-differential-coefficients` records the proved coordinate
calculation in `Sheaf.FieldTheory.PBasisZeroDifferentialCoefficients`. It requires
specified monomial and differential bases, assumes no perfection, and contains no
sorry or data selected from an unproved theorem. No change records are needed.

## Second reading by A4

1. **Visible interfaces: PASS.** Compared the main module with the repository by
   `diff -u`: its existing theorem signature, universes, public imports and docstring
   are byte-for-byte unchanged. The additions are private helper/proof code and
   proof-only imports. The coefficient module is new. No definitions or target
   statements changed, and no change record or forced adaptation is needed.
2. **Proof and axioms: PASS.** Read both complete proofs and compiled both modules
   in import order with `lcompile.py --all`, without errors or warnings. Neither
   delivered module contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`
   or `extern`. Explicit scratch `#print axioms` reports only `propext`,
   `Classical.choice`, `Quot.sound` for the coefficient theorem, and those plus
   `sorryAx` for the main theorem, through existing dependency statements. All
   chosen bases occur locally in proposition proofs; no data definition selects
   an arbitrary witness from an unproved existence theorem.
3. **New statement: PASS.** No statements were split off with sorry. The fully
   proved coefficient lemma is strictly one part of the main argument: it assumes
   specified monomial and differential bases, makes no perfection assumption, and
   concludes one nonconstant coordinate vanishes. Checked empty index type
   (no nonzero exponent), p=2 (the only positive exponent is 1), infinite index
   types (finite Finsupp supports), and exponent zero (correctly excluded).
   Independently searched LeanFinder for diagonal derivations/monomial kernel
   coordinates and Loogle for `KaehlerDifferential.D, Module.Basis.repr`; their
   polynomial results do not replace this field theorem. Local `rg` searches of
   Mathlib FieldTheory/Kaehler and project FieldTheory/RingTheory/WeilConjectures
   found no duplicate. Read the cached Stacks `more-algebra.tex` proof of 07P2:
   its dual derivations kill kK^p and give the partial-derivative calculation
   used here after multiplication by t_i.
4. **Route and pruning: PASS, import cleanup applied.** The original three DAG
   proof dependencies all remain used. Frobenius identifies kK^p with K^p,
   `Basis.mapCoeffs` transports the existing p-basis, the differential-basis
   theorem supplies the dual derivations, and coordinate reconstruction gives
   the constant coefficient. The Euler computation avoids lowering/reindexing
   exponents and uses Mathlib basis extensionality directly. The unit
   `dag/units/sk-thm-p1.json` and its realized route are unchanged. Removed
   `Mathlib.Algebra.CharP.Algebra` from the coefficient module after a scratch
   compile without it succeeded; the main module uses its characteristic-transfer
   theorem. All public imports of the new module supply objects used in its
   statement. No existing project module or DAG dependency is pruned.
5. **Nodes and report: PASS.** Diffed the existing node: only `proof`,
   `proof_deps`, and `proof_origin` changed. The new dependency is the proved
   coefficient calculation. Checked its source, complete proof steps, dependency
   union, three kinds of search records, creation/blueprint/chapter/unit fields,
   and verbatim Lean statement. Its hypotheses match the Lean declaration, and
   it introduces no deferred proof. Added its blueprint tag to the new module
   docstring. Updated the report to distinguish current p-basis dependency status
   and record import removal. No mathematical proof repair was needed.

Second-reading changes: removed one unused proof import, added the new module's
blueprint tag, and clarified this report. The original delivery-tool ImportError
reported above is historical; the prescribed dry run is retried below.

Second-reading delivery dry run: OK; commit d1b0cbe740 compiles and passes
preflight. The historical ImportError is resolved. Review class CODEX because
the delivery adds a proved public lemma/module and its DAG node.

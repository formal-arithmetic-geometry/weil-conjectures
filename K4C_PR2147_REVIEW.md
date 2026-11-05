# PR #2147 statement-fidelity review

Reviewed commit `b75dbf2f920dd39ba7a011149241206426dc6b8f` (three new files, 529 lines).
Result: **PASS — no statement-fidelity blocker found.** This is a source review, not a new
independent compilation or axiom audit. K4/C9 own the integration builds under LEAD01:55.

1. `SmoothPurityOrientationOfTateEncoding` has a conclusion byte-for-byte identical to
   `WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso` in K4's
   `SmoothPurity.lean`. The sole added input is the Tate encoding alpha. Its type matches
   `WeilSheaf.purity_nonempty_toCondensedTateDescentIso k0 l X d`; extracting that `Nonempty`
   and applying the new theorem discharges the original statement. The finite-field,
   characteristic, finite-type, separatedness, smooth-dimension and `HasUpperShriek`
   assumptions match the original context. There is no new smoothness assumption on Y.
2. `SmoothPurityDescendedVerdierUnit` proves A1' for an arbitrary relative f:X→Y, without
   properness or smoothness of f. The theorem uses the actual `descendedShriekGeometricExchange`
   and the chosen `compactificationOverField f` together with its geometric fibre. Its
   `IsIso e` input is discharged in the orientation by the monoidal unit isomorphism.
3. The proper factor is the specified library `upperShriekBaseChangeOfMap` at the unit.
   The endomorphism criterion converts an abstract duality isomorphism into invertibility
   of that specified map. No claim identifying an arbitrary isomorphism with the canonical
   comparison is used. The geometric-fibre compactification structure map is transported
   through an explicitly proved equality, not assumed definitionally equal.
4. `SmoothPurityVerdierUnitIso` uses absolute biduality on arbitrary Y, existing exceptional
   internal-Hom exchange, weakly-etale internal-Hom compatibility, and the checked point
   theorem for both X and Y. It keeps the distinction between the abstract unit isomorphism
   and the specified proper comparison explicit.
5. All three added files contain no admissions, axioms, native decision procedures,
   kernel bypasses, opacity tricks, or resource-limit increases. A comment-aware import
   traversal of all 15,109 repository modules reachable at the reviewed commit finds no
   path to `WeilSheaf/SmoothPurity`, `VerdierDual`, `VerdierExchangeNatural`,
   `ProperProjectionFormula`, or `AffineLineBundle`. It does import the native tensor-swap
   module through existing native-model support; an import alone is not a declaration
   dependency. The final printed-axiom audit remains the integration check for that issue.

Minor documentation issue only: `SmoothPurityVerdierUnitIso`'s introduction still names
`isIso_upperShriekBaseChangeOfMap_app_unit_geometricFiber` and
`SmoothPurityVerdierUnitBaseChangeRelative`, which are not declarations/files added by this
PR. The actual exported relative theorem is in `SmoothPurityDescendedVerdierUnit`.

The mirror exposes this PR as `refs/pr/2147`, not `pull/2147/head` or a branch head named
`houyi/subc-dual2`.

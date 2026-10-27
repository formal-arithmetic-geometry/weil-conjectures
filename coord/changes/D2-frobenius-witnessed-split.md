# Witnessed finite-origin extraction and coefficient invertibility reduction

The optimized complete `FrobeniusSquareExchange` compiled locally in 42.7 seconds,
but delivery preflight still took 63 seconds. Local opacity was first added to
large exchange/scalar constructors and tensor composition; the private localized
composition proof was rewritten by tensor induction. To obtain timing margin,
move its independent finite-origin section to the new module
`Sheaf.Paper.FrobeniusWitnessedCompactification` and publicly reexport it.

The 34 public declarations retain their exact names, signatures, attributes and
construction formulas. Existing private helpers and completed normalization
proofs move with the section. The named `intrinsicCompactificationCoherence`
hole also moves unchanged: it is not claimed as closed, and no replacement
statement or comparison is introduced. Original public imports are retained.
The corresponding new DAG node owns these declarations; the original node keeps
its remaining 40 declarations and depends on the new extraction node.

The only mathematical reduction closes `modelScalarMap_isIso` by case analysis:
the existing compact-support coefficient component theorem proves the compact
branch, and one new direct-image component theorem isolates the direct branch.
The new statement is strictly one branch; the full-subcategory and natural
transformation assembly is proved. No target statement changes, no axiom is
introduced, and all definitions retain their actual data.

No existing module besides the assigned module is edited. Its two direct
importers are `Sheaf.Paper.FrobeniusGeometricExchange` and
`Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence`. They are checked from
unchanged source against this packet, then their temporary copies are removed.
Validation results are recorded in report.md.

Final verification: the extracted module and assigned module compiled with both
unchanged direct importers in a single `lcompile.py` request, exit code zero, no
warnings. Both temporary consumer copies matched the current source and were
removed. No consumer adaptation is included.

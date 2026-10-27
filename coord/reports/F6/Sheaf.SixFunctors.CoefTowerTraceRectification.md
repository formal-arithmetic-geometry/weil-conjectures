## What changed

Filled the exactness proofs for actual constant-scalar restriction, restriction of
quotient-semilinear systems to constant-scalar towers, and open extension of towers.
Filled additivity of point sections and the quotient-composition and quotient-linearity
proofs. Every existing declaration signature and every public import is unchanged.
The proof of scalar exactness forgets to abelian sheaves: that forgetful functor
preserves sheafification and finite limits and colimits, and reflects finite limits
and colimits.
The tower exactness proofs then use pointwise preservation.

Repair of returned delivery `1ba79db67e2`: removed the inherited
`set_option warn.sorry false` command. Its option name was scanned as an
unattributed hole at line 47, offset 2164. This removes that false marker; the
three genuine remaining holes are still whole named theorem proofs. Compared
with the current shared source, the six proof replacements remain applicable
without further adaptations.

## Proved and sorry left

Closed six of the original nine holes, without adding any holes:

- `WeilConjectures.coefTraceConstantScalars_exact`
- `WeilConjectures.coefTraceSystemRestriction_exact`
- `WeilConjectures.coefTraceSections_additive`
- `WeilConjectures.coefTraceOpen_exact`
- `WeilConjectures.coefTraceQuotient_comp`
- `WeilConjectures.coefTraceQuotient_linear`

The original, unchanged remaining statements are:

- `WeilConjectures.coefTraceSheafTowers_kInjectives`
- `WeilConjectures.coefTraceTargetTransition_quotient`
- `WeilConjectures.coefTowerTraceRectification`

All three retain their existing attachment to
`lem-coef-tower-trace-rectification`. No decomposition or new statement is introduced.
The quotient proofs also cover equal levels; the exactness proofs impose no nonempty
scheme or boundedness assumption and apply to the empty scheme and identity open immersion.

## No longer needed

Removed the unused proof import `Sheaf.Paper.SemilinearDerivedSections`.
No public imports, modules or mathematical dependency nodes are withdrawn.
In particular the two main proof dependencies, `lem-coef-dualizing-support-evaluation`
and `lem-coef-finite-counit-restriction-square`, remain needed by the unfinished assembly.

## Where the brief, the DAG or earlier work was wrong

The existing main proof dependencies use a different support presentation from this
module: `DualizingSupportEvaluation.B` first applies varying-ring support and then
completed restriction, whereas `coefTraceCompactSections` first restricts to constant
scalars and derives its constant-scalar proper and section functors separately.
Thus the main assembly needs a comparison of those presentations; it is not a direct
application by definitional equality. Likewise the finite-counit dependency uses the
pro-etale point presentation, while this module specifies the ordinary-etale one.
This delivery preserves both statements and makes progress on the supporting holes.

Searches used the required msearch leanfinder, loogle and grep modes, supplemented by
local searches of Mathlib, WeilConjectures and Sheaf. The useful existing interfaces
were finite-limit reflection by the sheaf inclusion, sheafification descent of colimit
preservation, exactness of `SheafOfModules.toSheaf`, pointwise preservation under
whiskering, and `Ideal.Quotient.mk_surjective`. No shorter theorem matching the full
rectification statement was found.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

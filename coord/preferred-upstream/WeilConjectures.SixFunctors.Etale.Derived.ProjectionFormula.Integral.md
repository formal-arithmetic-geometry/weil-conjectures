## Our previous version of this upstream file (upstream sync 34248f3e4, 2026-10-24)

The upstream sync could not merge our version of `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral` with upstream's new text: does not compile (exit 1): t 1 (17.9 s)
/home/ubuntu/cc1/rset-tmp/c-vbx9xhw5/lean/WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/Integral.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/RestrictScalars.olean' of module WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars does not exist


The file now has upstream's text; our version is kept in `coord/preferred-upstream/WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral.lean`. Re-apply our work on top of the current upstream text: keep upstream's statements and text, bring back our proofs, fills and helper declarations (adapting them to the new context), and deliver as usual. Do not restore the old file wholesale.

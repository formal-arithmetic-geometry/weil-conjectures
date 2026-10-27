## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.pullback_of_ctf_eq`
in `Sheaf.SixFunctors.IntegralCompactSupportPullback` with its statement unchanged.
Added proof-only imports `all Sheaf.Paper.UnboundedLocalizingPullback` and
`Sheaf.Paper.LocalizingClosureCtfEqualsBc`. The former exposes the already proved
qcqs helpers, which do not need the public theorem's characteristic hypotheses.
The standing structure morphisms give qcqs source and target schemes. Bounded
constructible preservation follows directly from the existing helpers; the
localizing assertion follows from their finite-Tor version by transporting
membership through the existing integral ctf=bc closure equality. Updated the
item node's proof steps and proof origin to describe this assembly.
The final server compile passed cleanly in 8.2 seconds, with no warnings.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.pullback_of_ctf_eq`
(node `lem-sfb-total-derived-pullback`). No holes remain in the item module.
Zero holes added; zero split-off statements. This is a proof from existing
project declarations, not a claim that all transitive dependencies are sorry-free.

## No longer needed

None. No original imports were removed, and both declared proof dependencies
remain used: `det-proper-base-change-unbounded-pullback` through its general
proved helpers, and `det-def-localizing-closure-ctf-equals-bc` through its
localizing-closure equality. No modules or nodes are withdrawn. The separate
Dctf=Dbc transport for the generator clause is unnecessary because the existing
bounded-constructibility helper already proves that clause directly.

## Where the brief, the DAG or earlier work was wrong

The public `unboundedLocalizingPullback` theorem has distinct positive-prime
and characteristic assumptions absent from this item. Its proved private
helpers have the required generality, so no statement repair or additional
lemma is needed. The assembly works for characteristic zero and characteristic
ell as well, and uses no nonzero-object or nonempty-scheme hypothesis. No target,
definition, existing declaration signature, or source-library module changed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

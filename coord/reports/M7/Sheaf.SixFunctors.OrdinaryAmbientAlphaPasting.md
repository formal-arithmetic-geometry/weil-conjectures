## What changed

Filled `AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaPasting`
without changing its signature. The proof imports `AmbientUnderivedClopenPasting`,
`AmbientOrdinaryClopenLocalization` (including its existing private compositor
comparisons), and `ExactDerivedTransformationPasting` only for proofs.

Two private generic lemmas encode the vertical and horizontal ordinary equations
as finite exact-functor pasting expressions and localize them. Two proved
categorical transport calculations cancel the total/exact inverse-image
comparison isomorphisms, using naturality. The ordinary localization theorem
identifies the three square cells in each equation with the intrinsic alpha.
The existing normalized open-compositor identification handles horizontal
composition; the definition of the total-derived pullback compositor and its
existing localization equation handle vertical composition. The final proof
applies both results to the ordinary positive coefficient ring and the
underlying schemes of `Spaces`.

The node's proof and proof dependencies now describe this implementation.
No definition, public import, existing declaration type, or other module changed.

The complete proof compiled through `lcompile.py` in 36.1 seconds. Temporary
profiling options were removed before delivery. Local irreducibility attributes
keep the concrete alpha, adjunction and pullback compositor definitions from
expanding during comparison; no shared definition or transparency setting changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaPasting`
(node `lem-sf-ordinary-ambient-alpha-pasting`).

Added zero holes. There are no `sorry`s in the delivered Lean module and no
split-off statements. All proof helpers are proved.

## No longer needed

No original import was removed: the public `AmbientProperOpenCalculus` import
is required by the statement. The direct proof dependency
`lem-sf-ambient-exact-clopen-comparison-localization` was replaced by its proved
ordinary component, `lem-sf-ambient-ordinary-clopen-localization`; the proof does
not use the system, beta, or proper-mate clauses of the larger theorem.
`AmbientExactClopenComparison` remains a transitive dependency of the underived
pasting theorem, so this delivery does not claim that module is globally pruned.
Both other declared proof dependencies are used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The plan's references to
private compositor-localization lemmas were usable through a proof-only
`import all`. The supplied ordinary comparison theorem already isolates the
localization identification needed here, so invoking the larger ordinary/system
comparison theorem directly was unnecessary. The unit has no realized proof
steps to bypass; its route and all hypotheses are preserved.

The search was made through `msearch.py` using LeanFinder for exact derived
pasting, Loogle for `CategoryTheory.Localization.liftNatTrans`, and grep for
proper/open alpha composition and derived pullback compositors. Searches of the
shared source library found no existing theorem with this complete conclusion.
The generic exact-derived pasting theorem and existing ordinary compositor
comparisons were reused.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

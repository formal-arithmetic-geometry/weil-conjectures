## What changed

Replaced the hole in `WeilConjectures.sfPackageBaseChangeDomainRealization` by assembly
of the existing geometric, finite-mate, completed-mate and exchange-coherence declarations.
For proper rational coefficients the proof applies completed proper exchange to the supplied
integral lattice, localizes the invertible arrow, and transports it along the lattice
rationalization. The constructible representation uses the actual integral endpoints and
its equation follows from naturality after an explicit pure-tensor calculation.
Proper common stages use `qbar_properBaseChange`. Smooth rational exchange and finite-stage
constructible representations use `eCoefficientSmoothBaseChange`; common-stage smoothness
comes from `exchangeFunctoriality`.

Compact support uses the existing finite etale isomorphism instance,
`ProEtale.isIso_csAuxiliaryExchange`, `completeCompactSupportProetale_isIso`, and
`qbarCompactSupportBaseChange`, together with the support laws of `exchangeFunctoriality`.
The proof imports the canonical finite proetale theorem and the finite etale instance module
privately. Existing statements, definitions, and public imports are preserved.
The existing DAG node's proof and proof dependencies record the actual argument.
The resumed attempt also controls local transparency of the completed operations and
common-stage functors, gives the lattice endpoints explicit types, and uses proved
private lemmas for localization of a functor and naturality. These changes avoid
repeated unfolding of the underlying derived-category and sheaf constructions; all
public definitions retain their existing bodies. The proof also disables conversion of
local let-bindings to have-bindings during cleanup, following the existing coherence
module, so the large coefficient presentations retain their sharing. Explicit universe
arguments fix the otherwise unconstrained universe of an unused coherence conjunct.
The final common-stage support constructor checks its projections at reducible
transparency, avoiding expansion of the descended functors. The full module compiled
in 17.8 seconds through the required compile service before removing profiler options.

## Proved and sorry left

Closed: `WeilConjectures.sfPackageBaseChangeDomainRealization`
(lem-sf-package-base-change-domain-realization), the module's only original hole.
Added: none. Left in the item: none. Used dependency theorems may still depend on `sorry`;
this is a proof from their published statements, not a claim that all dependencies are proved.

## No longer needed

Removed the private import `Sheaf.Paper.SfBcAdicRingDomain`: the quotient and completed
coefficient hypotheses are already supplied at the finite and completed theorem interfaces.
Node lem-sf-bc-adic-ring-domain is consequently not a direct proof dependency here.

The proof does not import or use `Sheaf.Paper.SfFieldMateDomain`
(lem-sf-bc-field-mate-domain): its needed proper rational part follows from the completed
clause on the chosen lattice, and its other parts are direct applications of the published
proper common-stage and smooth rational theorems and exchange coherence.

The proof does not import or use `Sheaf.Paper.CompactSupportExchangeDomains`
(lem-sf-bc-compact-support-domain): the canonical finite etale instance, finite proetale,
completed and common-stage base-change theorems directly match the compact-support clauses.
No module is withdrawn and no upstream declaration is removed. These pruning statements
concern this assembly's direct dependencies; dependencies retained elsewhere remain needed.

## Where the brief, the DAG or earlier work was wrong

The DAG's domain wrappers were more than this assembly needs. In particular the field
wrapper's proper-rational assertion is about the localized exchange on an integral raw
representative, whereas this item asks for a chosen lattice presentation as well as a
constructible representation. Applying the completed clause to that lattice and using
naturality supplies both assertions directly. The compact-support wrapper has additional
bundled-square and boundedness requirements that the canonical underlying theorem APIs do
not impose on this item's bounded-below finite inputs. No statement correction was needed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

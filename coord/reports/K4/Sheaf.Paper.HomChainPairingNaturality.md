## What changed

Prove `WeilConjectures.HomChain.pairing_naturality` in
`lean/Sheaf/Paper/HomChainPairingNaturality.lean`, with its signature and all six
conjuncts unchanged. Private proved helpers derive naturality of the canonical
raw projection at each coefficient stage and transport it through the tensor
comparisons and faithful full inclusion. Ordinary, exceptional and tensor-Hom
counit naturality give the first three identities; functoriality and associativity
combine these with projection naturality to prove the remaining identities.
The DAG proof and dependency list record this argument. Existing public imports
and public definitions are retained. No source-library module is changed.

## Proved and sorry left

Closed: `WeilConjectures.HomChain.pairing_naturality`
(node `lem-pod-hom-chain-pairing-naturality`), the sole original hole.
Added holes: none. Remaining holes in the delivered module: none.
Remote single-file validation passed with exit code 0 in 14.4 seconds and no warnings.
The proof uses the existing projection-formula theorem; its upstream proof
obligations remain with their existing modules. This is a proof from existing
stated dependencies, with no split-off statements.

## No longer needed

The proof no longer calls `WeilConjectures.PodHomChainDomains.domains_and_bijections`
(`lem-pod-hom-chain-ctf-domains`, module `Sheaf.Paper.PodHomChainCtfDomains`):
all objects already belong to the recorded full domains by their types.
`lem-weil-pbc-adjunction-of-natural-bijection` is unnecessary: no adjunction is
constructed from a new bijection, and Mathlib's counit naturality applies directly.
`lem-pod-closed-uncurry-laws` is unnecessary for evaluation naturality: evaluation
is definitionally the supplied tensor-Hom counit.
The separate source-library adjunction theorem of `fix-prop-adjunctions` is not
called: the existing restricted adjunctions are already constructed in
`det-thm-sf-ctf-stability-adjunctions`. These unused proof dependencies are removed
from this node's proof route. No modules are withdrawn, and no existing public
imports are removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned domain and adjunction-construction steps were redundant for the
current Lean interface. The projection square does require transport through
both recorded tensor comparisons; this is included explicitly, using the actual
raw projection rather than choosing unrelated isomorphisms.
Searches used the required remote leanfinder, loogle and grep services, plus
local source search. They found Mathlib counit naturality and functor/natural
transformation laws, rather than an existing combined pairing theorem.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

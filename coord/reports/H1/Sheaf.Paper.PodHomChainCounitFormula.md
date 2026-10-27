## What changed

Proved `WeilConjectures.PodHomChain.counit_formula` from the existing
`PodHomChain.uncurried_transport` and `HomChain.pairing_naturality` declarations.
The fifth conjunct of transport gives the four-arrow pairing formula; source
naturality of the chosen target adjunction curries it to the requested formula.
Associativity proves test-object naturality. Currying the sixth conjunct of
pairing naturality with source and target adjunction naturality proves the last
clause. Both new proof imports are private imports. The mathematical statement,
all its binders, the five-arrow equivalence, and every canonical map are unchanged.

To permit this proof, adapted the unclaimed module
`Sheaf.Paper.PodHomChainUncurriedTransport`: replace its upward import of the
parent with the already existing `PodCtfPairingMaps`, use its definitionally equal
Hom and projection, and unfold the source functor value into the same direct
image. There were zero downstream importers of the adapted module. The import
cycle is eliminated without a new definition or a replacement theorem.
Change record: `coord/changes/H1-hom-chain-transport-import-direction.md`.

The existing node copy records that the finite-Tor memberships are already built
into the supplied full-domain data. No unit statement or realized unit proof
step is bypassed. The unit's realized statement and steps lists are empty.

Search: LeanFinder for composite-adjunction counit naturality returned the generic
Mathlib adjunction naturality laws; Loogle for
`CategoryTheory.Adjunction.homEquiv_naturality_left` returned the exact law used.
Source search found the pre-existing transport and pairing-naturality statements,
whose signatures were read before writing the proof. No new statement is needed.

## Proved and sorry left

Closed 1 existing hole:
`WeilConjectures.PodHomChain.counit_formula`
(`lem-pod-hom-chain-counit-formula`). The item has zero holes left.
Remote Lean compilation accepted the full proof; a formatting warning in the
first successful run was removed before the final check.
Added zero holes and split off zero statements.

The adapted child now has zero holes: its proof of
`WeilConjectures.PodHomChain.uncurried_transport`
(`lem-pod-hom-chain-uncurried-transport`), landed by A7 in `245f936e9c4`,
is preserved in full. The proof also uses the pre-existing
`WeilConjectures.HomChain.pairing_naturality`
(`lem-pod-hom-chain-pairing-naturality`), whose module is not modified.
These are the stated dependencies, not new split-off statements.

## No longer needed

`lem-pod-hom-chain-ctf-domains` / `Sheaf.Paper.PodHomChainCtfDomains` need not be
imported for this proof: all its domain memberships and bijections are already
constructed in the types of R, projectionIso, and homEquiv. Removed that proof
edge from the item's node; the lemma remains available to other consumers.

Removed the child module's public import of
`Sheaf.Paper.PodHomChainCounitFormula`, which produced an upward dependency.
The existing `Sheaf.Paper.PodCtfPairingMaps` supplies all definitions it uses.
No Lean module is withdrawn. No other declared proof dependency is pruned:
Mathlib's generic adjunction laws implement the closed-uncurry step directly.

## Where the brief, the DAG or earlier work was wrong

The planned uncurried-transport child imported its parent to reuse definitions,
so it could not originally be used as the parent's proof dependency. An existing
independent shared map module already contained the same constructions. Reusing
it repairs the import direction; the original theorem and all six child
conjuncts retain their mathematical meanings by definitional equality.
The initial source and claim records contained no quarantine for the item, and
no claim for either planned child. There is no definition chosen from
an arbitrary unproved existence statement, and no statement weakening.

Repair of the return on `3b6ae8c077c`: the landing tools found that A7 had
proved the transport module in `245f936e9c4` after the original delivery base
`ad146d138`. Started the adapted child again from the current repository file,
preserving all four proved private helpers and the complete public transport
proof. Reapplied only the shared-map import substitution, including qualifying
raw projection and projection-isomorphism references in those existing private
helpers. No A7 proof is replaced by a hole. Refreshed node copies against the
current records while retaining only this delivery's intended fields. This
repairs the sole returned point with a substantive integration of the current
proof, rather than a rebase of the old holed child.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

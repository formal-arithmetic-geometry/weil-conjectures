## What changed

Proved `WeilConjectures.finite_constructible_derivedHom_etale` in
`Sheaf.Paper.FiniteConstructibleHom`, preserving both public signatures. The proof
reuses `AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_isSeparated`
from the adopted source library. Proved private helpers compare the two bounded
constructibility conventions, establish the invertible exponent of the quotient
coefficient ring, and specialize the source theorem. Updated the node's etale
proof route; retained its pro-etale proof plan. No definition or consumer changes
are delivered.

## Proved and sorry left

Closed 1 of 2 original holes:
`WeilConjectures.finite_constructible_derivedHom_etale`.
The original hole in `WeilConjectures.finite_constructible_derivedHom_proEtale`
remains, with its original statement, source, docstring and node
`cor-weil-finite-constructible-hom`. Added 0 holes. All private helpers are proved.
The etale candidate compiled in 27.3 seconds. A complete pro-etale candidate was
also written, using etale origins, interval reflection/preservation, the site-Hom
comparison, and a proved K-injective bridge between the two Hom presentations;
complete-file verification exceeded the 60-second limit, so that candidate is
not claimed as proved or included in this packet.

## No longer needed

The original shared item has no private proof imports to remove. The delivered
etale proof adds only the stability theorem, the constructibility comparison,
and characteristic/cardinality facts. It does not directly need
`thm-fix-general-biduality`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-verdier-preservation-strata`, or `lem-sf-tensor-ctf`: the adopted source
stability theorem already proves their duality/tensor calculation. These nodes
are removed from the item's direct proof dependencies. Their transitive use by
other declarations is retained. The pro-etale origin, Tor comparison and finite
duality comparison remain in the retained proof plan. No module or declaration
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The etale assertion already has a fully proved adopted-source match. The fixed
coefficient and intrinsic constant-ring module presentations of internal Hom
are distinct, so pro-etale transport needs an additional comparison bridge.
Performance experiments reinstating the previously landed coefficient-ring
instance repair did not resolve the full-file timeout and exposed a newer
consumer's missing quotient topology instance; that experiment is excluded.
There are no statement changes, new assumptions, source-library edits, forced
adaptations, or new nodes in the delivery.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

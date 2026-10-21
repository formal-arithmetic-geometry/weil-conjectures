## What changed

Restored lean/Sheaf/Paper/IntegralResidueExchange.lean from its current quarantine archive
as required by coord/rework.tsv. The archived complete proof compiles against the current
restored IntegralResidueExchangeAlgebra. Rewrapped four long lines without changing any
non-whitespace character in the file. Preserved the theorem signature, public imports,
proof imports, local attributes, definitions and original DAG attachment. Updated only
the whitespace in the node's lean.statement to match the file.

The proof equips the actual reduction with bounded constructibility, obtains coherent
pull comparisons and invertible push mates, and constructs the two endpoint isomorphisms.
It rewrites the specified bounded exchange components to their ambient mates and applies
the proved coefficient-exchange square through Arrow.isoMk. All four recorded proof
dependencies are used. The finite-type hypothesis supplies the noetherian condition for
the constructibility theorem. There is no properness or Cartesian hypothesis, and no
assertion that exchange itself is invertible. The construction also covers zero complexes
and empty schemes without choosing an arbitrary existential witness for a definition.

Change record: coord/changes/H4-integral-residue-exchange-restoration.md.

## Proved and sorry left

AlgebraicGeometry.ProEtale.CondensedRing.integralResidueExchange_comparison retains its
complete archived proof. This is a zero-hole restoration: the archive has 0 sorries,
the delivered module has 0 sorries, 0 holes closed, 0 holes added, 0 split off. No other
Lean module is changed. No named declaration is left with sorry by this delivery.

The archived version compiled in 24.7 seconds, with only four existing long-line warnings;
these have been corrected. The final compile and delivery preflight validate the restored
module against the current library. The downstream source scan found the quarantined
IntegralFiniteExchangeComparison caller; its unchanged application matches the identical
restored signature.

## No longer needed

None. No imports, nodes, modules or unit steps are pruned. All four existing proof
dependencies remain needed. LeanFinder and Loogle both found Arrow.isoMk, which the
archived proof already uses; the library search found the existing coherent comparisons
and exchange-square theorem, so no replacement lemma or new node is needed.

## Where the brief, the DAG or earlier work was wrong

This assignment is the quarantine restoration recorded in coord/rework.tsv, rather than
an unproved theorem: the preserved module already has zero holes. Its absence from lean/
did not remove its attachment or its quarantined parent's dependency. The archive contains
four lines exceeding 100 characters, now wrapped. The original mathematical statement,
proof route and all dependency signatures fit the current library unchanged.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

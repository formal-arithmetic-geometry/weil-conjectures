## What changed

Proved `IsRegularLocalRing.iff_isDomain_and_isIntegrallyClosed_of_dim_one` in
`Sheaf.RingTheory.RegularLocalDimOneIffNormal`, without changing its signature.
The forward implication installs regularity, uses the source DVR theorem, and obtains
both domain and integral-closure instances. The reverse implication installs the two
assumed instances and applies `IsRegularLocalRing.of_isIntegrallyClosed` at dimension ≤1.
Only `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` is needed as a proof import.
Updated the item's node proof, proof_deps and proof_origin to reflect this route.
The public statement imports remain unchanged.

The existing nodes `lem-sc-regular-local-domain`, `lem-sc-regular-dim1-dvr`, and
`lem-sc-normal-dim1-dvr` are used as generic, already proved tools. The latter node's
`lean.declarations` includes `IsRegularLocalRing.of_isIntegrallyClosed`, which supplies
regularity directly. This item is absent from `dag/units/sk-thm-p1.json`'s realized
statement and steps, so the pruning changes only the supporting node-level argument.

LeanFinder returned Mathlib's DVR TFAE and Dedekind-domain results; Loogle returned no
match for `IsRegularLocalRing, IsIntegrallyClosed`; msearch grep returned no match for
the source theorem names. Direct rg of the source library found the three usable,
proved declarations in RegularLocalRing/Defs.lean. Local compilation is warning-free.

## Proved and sorry left

Closed the sole original hole:
`IsRegularLocalRing.iff_isDomain_and_isIntegrallyClosed_of_dim_one`
(node `lem-weil-pbc-regular-local-dim-one-iff-normal`).
No sorry remains in the item, and no new sorry or theorem was added.
This is a proof, not a decomposition.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`;
- `Sheaf.RingTheory.ValuationRingNormal`;
- `WeilConjectures.AlgebraicGeometry.Regular`.

The supporting nodes `lem-weil-pbc-principal-maximal-dim-one-regular` and
`lem-weil-pbc-valuation-ring-normal` are unnecessary for this proof. Mathlib already
supplies the DVR integral-closure instance, while the source directly supplies the
converse regularity theorem. This does not assert that other users no longer need them.
The definition nodes `def-weil-regular-scheme`, `def-weil-pbc-krull-dimension-ring`, and
`def-weil-pbc-normal-ring` are removed only from proof_deps; they remain statement
 dependencies. No unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned two extra helper lemmas were unnecessary because the source library
already proves the relevant stronger results. The original statement is correct and
unchanged. No definition, target, or dependent module needed adaptation.

## Second reading by B3

1. PASS: Compared the sole delivered Lean module with the repository using `diff -u`.
   The theorem signature, existing docstrings, namespace and public imports are byte-for-byte
   unchanged. Only its proof and three private proof imports changed; no definition changed
   and no change record is needed. No open change record names this module or theorem.
2. PASS: Compiled the module locally with `lcompile.py`, without errors or warnings.
   Compiled a scratch copy with `#print axioms` for
   `IsRegularLocalRing.iff_isDomain_and_isIntegrallyClosed_of_dim_one`: the complete list is
   `propext`, `Classical.choice`, `Quot.sound`. There are no remaining `sorry`s, forbidden
   declarations, or definitions in the delivered module. Thus the single closed hole is a
   genuine proof with no holes added, not a decomposition.
3. PASS: No statement or node was split off. Checked the upstream declarations and Mathlib's
   DVR and regular-local definitions, and independently searched the library and Mathlib.
   The forward direction obtains the domain instance from regularity before installing the
   DVR instance; the reverse direction installs exactly the two assumed instances. Fields
   and the zero ring cannot meet dimension one, so no missing edge-case hypothesis occurs.
4. PASS: The direct upstream converse avoids the two unproved Sheaf helpers. The upstream
   `IsRegularLocalRing.isIntegrallyClosed` also provides an alternative forward route, but
   saves no import and does not justify rewriting the correct DVR argument. All remaining
   proof imports are needed; public statement imports are preserved. Compared old and new
   `proof_deps`: all five removed nodes and all three removed modules are listed above.
   Read `dag/units/sk-thm-p1.json`: neither this item nor either removed helper realizes a
   unit statement or step. Its fixed route is retained; the generic tools remain recorded.
5. PASS: Compared the node JSON with the repository. Only `proof`, `proof_deps`, and
   `proof_origin` changed. The union of step uses equals the three recorded dependencies.
   Read each dependency's Lean record, including `IsRegularLocalRing.of_isIntegrallyClosed`
   under `lem-sc-normal-dim1-dvr`; the recorded steps match the actual proof and instance
   inference. No new node fields require review.

Second reading changed only this report by adding the independent checks and verdicts.
The Lean proof and node metadata needed no repair.

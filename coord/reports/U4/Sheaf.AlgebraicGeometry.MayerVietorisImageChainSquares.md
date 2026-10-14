## What changed

Repaired reviewer X-95278 point F: the change record now states that transparency
is relaxed only for the final instantiation of the abstract calculation. The
`schemeMVImageIso_eq` helper has no transparency override; the public theorem
contains the sole local override. This repair changes documentation only.

Proved `AlgebraicGeometry.schemeMV_image_chain_squares` without changing its
signature, visibility, docstring, definitions, or public imports. The second
reader found and reused the existing ordinary unit and nested-restriction lemmas
in `Sheaf.AlgebraicGeometry.OpenImageDirectImageComparisonRestriction` (a plain
proof-only import). A private proved equality identifies its comparison with
`schemeMVImageIso`: equality induction identifies `pushforwardCongr` with
`eqToIso`. This removes the candidate's duplicated generic adjunction calculation
and cancellation proof and shortens the file from 245 to 187 lines.
The existing degreewise naturality proofs and abstract additive biproduct helper
are retained. Seven private helpers are fully proved. The node now describes
this shorter route. No dependency module is edited or adapted.

Local irreducibility and transparency settings remain confined to this module;
`coord/changes/mayer-vietoris-image-chain-local-reducibility.md` documents them.
The complete revised module compiled cleanly with `lcompile.py` in 39.7 seconds.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeMV_image_chain_squares`
(node `lem-pc-mayer-vietoris-image-chain-squares`), one of one original holes.
Added holes: none. No sorry remains in the delivered module. No theorem was
split off. A scratch copy with `#print axioms` for all seven private helpers and
the public theorem compiled cleanly in 40.5 seconds: every declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The old report's
claim that `schemeMVOrdinaryOpenCounit_square_app` remained open was stale: its
current repository module has a proof, and the compiled dependency closure is
axiom-clean. This delivery changes no dependency proof.

## No longer needed

Neither original dependency node is removed: both
`def-pc-mayer-vietoris-image-chain-data` and
`def-pc-kinjective-mayer-vietoris-data` remain used. No baseline import or module
is pruned. Relative to the first worker's candidate, the direct proof imports
`Sheaf.AlgebraicGeometry.OrdinaryOpenCounitSquare` and
`all Sheaf.AlgebraicGeometry.OpenImageComplexComparisonRestriction` are replaced
by `Sheaf.AlgebraicGeometry.OpenImageDirectImageComparisonRestriction`.
The candidate's direct proof dependencies
`lem-pc-mayer-vietoris-ordinary-open-counit-square` and
`def-pc-derived-open-restriction-maps` are no longer direct dependencies; they
remain transitively used by existing comparison lemmas and definitions.
No whole-library pruning is claimed. The duplicated private
`unit_of_counit_square` and `cancel_into_right_adjoint` are removed.

## Where the brief, the DAG or earlier work was wrong

The previous reading missed reusable ordinary comparison lemmas already present
in the compiled library. Identifying their comparison with this module's fixed
comparison gives a shorter route and avoids repeating the adjunction proof.
The original candidate compiled cleanly in 54.6 seconds; the revised proof
compiled in 39.7 seconds. Timing observations do not replace delivery checks.
The unchanged theorem still permits arbitrary complexes and chain maps, empty
or repeated opens, and imposes no cover or injectivity hypothesis. Local
attributes affect elaboration only and require no downstream adaptation.

## Earlier second reading (a previous round; superseded)

1. **Interface — pass.** Compared the full module with the repository by `diff`
   and programmatically checked the existing public signature byte for byte.
   Arbitrary X, Y, h, opens U and V, complexes I and J, and chain map f are
   unchanged. Both the pair-of-units square and restriction-difference square
   retain their fixed components and signs. The public import and existing
   docstrings are unchanged. New helpers are private proved theorems; no data
   or definition is chosen. Local attributes have the supplied change record.
2. **Proof and axioms — pass.** The first worker's candidate compiled cleanly
   in 54.6 seconds; the shorter revised file compiled in 39.7 seconds. A scratch
   copy checked all eight declarations with `#print axioms` in 40.5 seconds:
   only propext, Classical.choice, and Quot.sound, with no sorryAx. No sorry,
   axiom, unsafe, opaque, implemented_by, or extern occurs in the final source.
   Read the equality-induction identification, both imported ordinary equations,
   their degreewise naturality lifts, and the signed biproduct calculation.
3. **Split statements — pass.** No new public statement, split-off theorem,
   unfinished helper, or node is introduced. The comparison equality identifies
   the same constructed isomorphism, not an arbitrary witness. Empty opens,
   U=V, identity h, and zero complexes do not require additional assumptions:
   the ordinary comparison identities and additive calculation apply uniformly.
4. **Route and pruning — repaired, pass.** Independent Loogle and LeanFinder
   searches found the generic adjunction API. Library search additionally found
   `schemeOpenImageDirectImageComparison_unit` and
   `schemeOpenImageDirectImageComparison_restriction`. Expanded their fixed
   construction, proved its equality with schemeMVImageIso, and reused them.
   Removed the repeated adjunction and cancellation arguments and their direct
   imports. The one public import supplies the target's definitions; the one
   plain added import supplies both reused proof lemmas. Neither original
   proof dependency is pruned. The unit `sk-thm-picard-semicon` has empty
   realized statement and step lists; no realized route is bypassed.
5. **DAG agreement — repaired, pass.** Only proof, proof_deps, and proof_origin
   change from the repository node. The unchanged node statement and Lean
   record match both squares. Revised steps cite the existing comparison nodes,
   construction definitions, degreewise naturality and additive argument.
   Checked proof_deps equals the union of step uses. No new nodes are needed.

Changes by this second reader: reused existing ordinary comparison lemmas after
proving equality of their comparison with the fixed one, removed 58 lines of
duplicated proof, replaced two direct proof imports by one, updated the node and
local-attribute change record, and corrected the stale counit-hole report.

## Second reading by U4

1. **Interface — pass.** The delivered module has the repository theorem
   signature byte for byte; its extra import is proof-only, and no public
   declaration or definition changed.
2. **Proof and axioms — pass.** `lcompile.py` compiles the module in 39.9
   seconds. The source has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`; the recorded scratch axiom check contains only the allowed
   axioms.
3. **Split statements — pass.** No statements were split off and no new holes
   or nodes were added. The proof applies uniformly to empty or equal opens and
   arbitrary complexes and chain maps.
4. **Route and pruning — pass.** The proof reuses the existing ordinary
   comparison unit and restriction lemmas, keeps both dependency nodes and the
   unit route, and removes only duplicated private calculations and their direct
   proof imports.
5. **DAG agreement — pass.** The node's proof steps and `proof_deps` equal the
   declarations used in the Lean proof; its statement and Lean record are
   unchanged.

I changed only the report wording, after the proof and metadata checks above.

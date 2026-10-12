## What changed

Replaced the only sorry in `lean/Sheaf/AlgebraicGeometry/HenselianClopenRestriction.lean`
with a complete Lean proof of `AlgebraicGeometry.Scheme.henselian_clopen_restriction`.
The signature, including its universe and all hypotheses, is unchanged.
Added proof-only imports of `Sheaf.Topology.SpectralClosedClopenDecompositionLift`
and `WeilConjectures.AlgebraicGeometry.HenselianConnectedness`.
The original public imports remain unchanged. Removed the original proof-only import
`Sheaf.Paper.ZariskiH0ProperHenselianPair`, which the new proof does not use.

The proof identifies the fibre image using the pullback range formula. Stein
connectedness gives the spectral hypothesis and connected intersections with point
closures. Nonempty closed differences meet the fibre, proving injectivity. Tag 0CAM
lifts the transported clopen/complement decomposition; the disjoint cover makes the
lift open and closed, and the homeomorphism onto the fibre image proves the required
preimage equality. The node's proof, proof_deps and proof_origin now record this route.

Read Stacks Tags 0A0B and 0CAM online, including their proofs. Neither scheme nor either
piece of the decomposition is assumed nonempty: empty spaces, the empty clopen, the
whole-space clopen and the ideal-zero case are covered by the unchanged statement
and the general decomposition lemma. Local compilation passed without warnings.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.henselian_clopen_restriction`
(node `lem-weil-pbc-henselian-clopen-restriction`): 1 of 1 original sorries removed.
No sorry remains in the delivered module, and no new sorry or module is introduced.

The proof uses existing unproved dependencies, as stage 3 permits:
`TopCat.spectral_closed_clopen_decomposition_lift`
(node `lem-weil-pbc-spectral-closed-clopen-decomposition-lift`) and the existing
`AlgebraicGeometry.Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`
(node `lemma-weil-pbc-stein-connectedness`), whose proof is complete but rests on
`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`
(node `thm-weil-pbc-stein-inputs`). Those modules are unchanged.

## No longer needed

The direct proof dependency `lem-weil-pbc-zariski-h0-proper-henselian-pair`, module
`Sheaf.Paper.ZariskiH0ProperHenselianPair`, is no longer needed by this theorem.
In particular the characteristic-function sheaf, inverse-image sheaf identification,
and adjunction-unit transport from the old planned proof are unnecessary here.
This is pruning from this node only, not a claim that no other target needs that module.

Removed the original proof-only import `Sheaf.Paper.ZariskiH0ProperHenselianPair`;
its node is the pruned dependency listed above. The two public Mathlib imports remain.
Two initially tried explicit proof imports,
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, were removed as redundant:
the retained imports already expose their declarations. The closed-immersion nodes
are still used, and the updated DAG also records the Mathlib fibre-product-points
leaf for its range computation.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old planned sheaf argument was valid but unnecessary:
the already stated closed clopen decomposition lift supplies its needed topological
consequence directly. The item does not realize any statement or step in its unit's
`realized` record, and no unit route is bypassed.

The existing Stein-connectedness node belongs to `sk-thm-iff` and is reused as a tool:
it states precisely the spectral and connectedness hypotheses needed here, with the
same proper henselian hypotheses and source Tag 0A0B. This replaces the old dependency
on the more general all-sheaves H⁰ comparison, which internally needs that same input.
No maintainer-owned `tool_uses` field was changed.


## Second reading by M1

1. PASS: Compared the entire delivered module with the repository using `diff`.
   The sole existing declaration's signature is byte for byte unchanged, including
   universe, hypotheses and conclusion. No definition, new declaration or change
   record is present. Only its proof, explanatory text and proof-only imports change.
2. PASS: Independently compiled the delivered file using `lcompile.py` (2.4 seconds,
   no errors or warnings). A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is from the
   existing open decomposition-lift and Stein-connectedness input, already listed
   above. The delivered module contains no sorry and no prohibited declaration or
   compiler escape hatch. Read the pullback range calculation, the closed-difference
   uniqueness argument and the homeomorphism transport independently; each proves
   the stated clause.
3. PASS: No statement was split off and no node or module was added. Checked the
   existing lifting hypothesis against Stacks Tag 0CAM, including its explicit
   nonemptiness requirement, and the geometric hypothesis against Tag 0A0B.
   Empty Y makes the pointwise hypotheses vacuous and yields the empty lift;
   empty/whole prescribed clopens and I=0 require no extra hypothesis. Independent
   Lean Finder search for extension from a closed subset meeting every point closure
   connectedly, Mathlib grep for clopen preimage/bijectivity, and repository searches
   found no shorter theorem applicable without Hausdorff or other added assumptions.
4. PASS: The proof uses the existing geometric input and topological lifting lemma
   directly, without restating the item. Both added imports are proof-only and used;
   both public Mathlib imports support the signature. The old proof_deps minus the
   new proof_deps consists exactly of the H⁰ henselian comparison node, now listed
   under No longer needed together with its removed import. Read sk-thm-p1's realized
   record: this item is not a realized statement or step, and its unit route is kept.
5. PASS: Compared the node JSON with the repository. Exactly `proof`, `proof_deps`
   and `proof_origin` change. The recorded steps match the Lean proof; their uses
   union equals proof_deps. Checked each dependency's declaration or Mathlib match,
   including the fibre-product-points leaf underlying `Scheme.Pullback.range_fst`.
   The statement, statement dependencies, source, unit and Lean signature stay intact.

Changed only this report: corrected the erroneous claim that no original import was
removed and clarified that the existing Stein wrapper is proved while its input is
still open. No Lean or node repair was needed.

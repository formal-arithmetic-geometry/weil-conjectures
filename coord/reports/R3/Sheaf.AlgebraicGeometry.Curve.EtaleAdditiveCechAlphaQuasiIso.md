## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_alpha_quasiIso` in
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaQuasiIso`, with its signature unchanged.
Added proved private helpers `restriction₀`, `restriction₀_naturality`, and `restriction₀_d`.
The construction and total-differential calculation follow the existing proof in
`Sheaf.AlgebraicGeometry.EtaleOpenCechResolutionTotal`, specialized to the prescribed maps.
Added the proof-only import `Sheaf.Paper.ZariskiEtaleCore` to supply site properties of the
canonical open inclusion by a natural isomorphism over X. The original two proof imports
are both used. Updated the item's node proof and dependencies to describe the actual proof.

The row comparison explicitly handles the distinction between the identity etale object
and the open inclusion at top: terminality gives an isomorphism, evaluation and the single
complex functor preserve it, and `quasiIso_iff_comp_left` cancels it after applying the
existing injective Cech augmentation theorem. The total map is constructed, rather than
chosen from an existence theorem. Its components equal `additiveCechAlpha` definitionally.
The proof assumes neither a nonempty cover nor affine intersections.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_alpha_quasiIso`
(node `lem-pbc-etale-additive-cech-alpha-quasiiso`).
No `sorry` remains in the item. No holes or public statements were added or split off.
The proof uses the existing named row and first-quadrant comparison declarations;
this report does not claim to close their transitive dependencies.
Single-file compilation passed with no warnings.

## No longer needed

None. Every original import and every original proof dependency is used.
No node or module is pruned. The existing total-homology existence theorem was read for
its proved calculations but is not imported, since its exposed conclusion does not fix
the augmentation components.

## Where the brief, the DAG or earlier work was wrong

The planned proof was valid but omitted the concrete site-data witness and the terminal
object comparison needed by the row theorem's interface. The existing
`lem-weil-pbc-zariski-etale-core` supplies the former; terminal uniqueness and generic
Mathlib isomorphism APIs supply the latter. No statement, definition, or unit route changes.

The earlier generated-probe warning is historical: the current delivery dry run passes. No tool was edited and no module option was added to work around the tool.

## Earlier second reading (a previous round; superseded)

1. The existing declaration signature is byte-for-byte unchanged, and the compiled proof establishes
   `etaleAdditiveCech_alpha_quasiIso` with the node's stated hypotheses and conclusion.
   Verdict: pass.
2. No new public theorem or split-off statement was added; the private helper constructions are
   concrete, and the proof introduces no hollow definition, axiom, or prohibited feature.
   Verdict: pass.
3. The proof follows the stated route through the canonical open inclusion, the injective Cech
   augmentation, and the first-quadrant column criterion. The unit route and its realized steps remain
   unchanged. Verdict: pass.
4. The node proof, proof dependencies, source, and Lean declaration agree with the delivered proof;
   no unused import or unreachable node was identified. Verdict: pass.
5. Local compilation succeeds without warnings without disabling the long-line linter. The generated-probe tool failure is reported above for maintainer repair.

I changed only the proof implementation, its proof-only import, the corresponding node proof metadata, and the report.

## Second reading by R3

1. Compared the delivered Lean file with the repository using `diff`: the existing
   theorem signature and docstring are byte-for-byte unchanged. Only its proof,
   three private helpers, and one proof-only import were added. There are no
   statement or definition changes requiring a change record. Verdict: pass.
2. Recompiled the module without warnings using `lcompile.py`, and compiled a
   scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_alpha_quasiIso`.
   It reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without
   `sorryAx`. No `sorry` or prohibited feature occurs in the delivered module.
   The total map is constructed from restrictions, with its prescribed components
   checked by `rfl`; no arbitrary existence witness supplies its data. Verdict: pass.
3. There are no split-off statements or new nodes to validate or close. The private
   restriction helpers prove naturality and cancellation of the two cofaces, rather
   than restating the item. Empty covers and empty or repeated intersections are
   covered by the general product and terminal-object arguments. Verdict: pass.
4. Read the normalization, injective augmentation, first-quadrant criterion, and
   Zariski-to-etale core interfaces; searched the existing total-resolution proof.
   Its private calculations cannot be reused directly, and its homology-existence
   conclusion does not prescribe the components needed here. All four imports are
   used; both original proof dependencies remain used, so `No longer needed` is
   complete. Read `dag/units/sk-thm-p1.json`: this reduction is below its realized
   steps and retains its route. Verdict: pass.
5. Compared the delivered node with the repository: only `proof`, `proof_deps`, and
   `proof_origin` change. The five steps match the site comparison, restriction
   construction, total differential, row comparison, and final criterion in Lean;
   their dependency union is exactly `proof_deps`. No new node is present.
   Verdict: pass.

Second reading changed only this report: added the required current review section
and recorded independent compilation and axiom verification. The first worker's
Lean proof and node metadata needed no repair. The delivery dry run passes.

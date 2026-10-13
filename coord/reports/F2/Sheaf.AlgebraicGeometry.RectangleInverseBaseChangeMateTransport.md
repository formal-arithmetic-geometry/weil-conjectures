## What changed

Replaced the only `sorry` in `RectangleInverseBaseChangeMateTransport.lean` with a
complete proof from the ordinary-pasting comparison theorem and the already proved
single-square inverse-mate identification. The private `mate_comparison` lemma proves
transport of mates under arbitrary natural comparison isomorphisms, by transposition
under the final adjunction and its counit. The final proof includes the categorical
identity in the ambient derived category and constructs the target isomorphism from
`t` and the base pullback comparison. Existing signatures and visibility are unchanged.

Added `Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons`, isolating ordinary
horizontal base-change pasting and the comparison adjunctions. This theorem has no
right adjoint `a` for the original morphism, no `adja`, no second mate and no component
`K`. Its conclusion supplies the ordinary identity and counit compatibility used in the
proved categorical argument; it is strictly the ordinary-square part of the argument.
It also pins the source comparison component to the existing canonical construction.
Updated the target node's proof and dependencies to this reduction.

## Proved and sorry left

Closed `AlgebraicGeometry.rectangle_inverseBaseChange_mate_transport`
(node `lem-sc-rectangle-inverse-base-change-mate-transport`). Proved private helper
`mate_comparison`. No `sorry` remains in the item's module.

Added one hole: `AlgebraicGeometry.rectangle_ordinary_pasting_comparisons`
(node `lem-sc-rectangle-ordinary-pasting-comparisons`). This is a decomposition:
one upper hole closed and one strictly lower ordinary-comparison hole added, net zero.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` from the item's
module. Both remain needed by the new ordinary comparison item; no global pruning
is claimed. The direct edges from the target node to
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-ringed-spaces-derived-direct-image-composition`,
`lem-cat-right-adjoint-composition`, `def-pc-derived-base-change-map`, and
`lem-pc-derived-base-change-pasting` move to the ordinary comparison node.
No module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing pasting theorem treats an upper-left morphism;
it is not itself the horizontal-pasting comparison between the rectangle and both
successive squares. The new theorem isolates the geometric ordinary comparison
needed in steps 1 and 2 of the plan. Step 3, the transport through second mates,
is now a real Lean proof using counits and naturality. The unit route is unchanged.

The first local compile lacked the recently landed `QCohInverseBaseChangeMate.olean`;
the shared cache subsequently refreshed. Temporary dependency copies were removed;
the delivery contains only the two intended modules.

## New nodes

`lem-sc-rectangle-ordinary-pasting-comparisons` in
`dag/nodes/sec-picard-framework/` states the ordinary horizontal-pasting identity,
its canonical source comparison, and the counit-compatible right-adjoint comparison.
Its source is Stacks Project, Tags 0ATR, 08HY and 0ATM. The docstring supplies the
complete argument by the pullback universal property, canonical composition,
uniqueness of right adjoints, and transposition of ordinary base change. There are
no definition changes, change records, or forced adaptations.

## Second reading by F2

1. Compared the delivered transport module with the repository version. The theorem
   signatures and existing definitions are unchanged; the only declaration change is
   replacement of the target proof and the proof-only import reduction. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; the transport theorem has
   no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The
   ordinary comparison theorem is the single named split-off hole and has its source,
   proof docstring, and DAG node. Verdict: pass.
3. Reviewed the split-off statement and its edge cases (including empty schemes and
   zero complexes as covered by the categorical formulation). It is strictly the
   ordinary comparison reduction and does not restate the target or introduce a
   middle right adjoint. Verdict: pass.
4. The proof uses the shorter generic mate transposition route and keeps the unit's
   ordinary-pasting step. The direct proof imports moved to the ordinary comparison
   module; no additional unused imports remain. Verdict: pass.
5. The target node proof and dependencies now name the ordinary comparison node and
   the inverse-square mate lemma, matching the Lean proof. The unit route and realized
   declarations are unchanged. Verdict: pass.

Changed the two α/δ component references in the private mate proof to
`natTrans.app`, which is required by the current `TwoSquare` API; this fixes the
compiler error without changing any public statement. No other changes were needed.

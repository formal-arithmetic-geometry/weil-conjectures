## What changed

Proved `AlgebraicGeometry.principalSubsetInsertion_differential` from the separate
horizontal and vertical components of Mathlib's total differential. The combining
proof expands `total_d`, uses additivity of the forgetful functor, applies both
component identities, and uses additivity of insertion to combine the coordinates.
The original theorem's signature and public import are unchanged.

Two new modules separate these components. The vertical component is proved:
expand the finite insertion sum, use `ι_D₂` and `d₂_eq`, identify the coefficient
map with `extendMap_f`, compute its action on `Pi.single`, and apply proved
section-transport naturality. The total sign is converted with
`Int.cast_negOnePow_natCast`. Only the horizontal component remains sorry.
The proof imports are private. No existing definition, statement, or visibility changes.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.principalSubsetInsertion_differential`
(node `lem-sc-principal-open-cech-subset-insertion-differential`).
Its combining proof compiles without a local sorry.
Also proved the new `AlgebraicGeometry.principalSubsetInsertion_vertical`
(node `lem-sc-principal-open-cech-subset-insertion-vertical`), including its private
sum-evaluation and section-naturality helpers, without adding a hole.

One hole is added and is the only sorry in the delivery:
`AlgebraicGeometry.principalSubsetInsertion_horizontal`
(node `lem-sc-principal-open-cech-subset-insertion-horizontal`).
It addresses only the signed face restrictions, with no coefficient-differential
term. This is a decomposition with one original hole closed and one smaller hole
added, hence zero net holes removed, plus a completed vertical calculation.
No data is chosen from an unproved existence assertion.

## No longer needed

None. The original public import defines the coordinate groups and insertion
used in the statement and remains necessary. Both private proof imports are used.
The unit record has no realized statement or steps for this subsidiary node;
its route is unchanged. The old direct proof dependency `def-sc-principal-open-cech-subset-insertion`
is now reached through both component nodes and is still used by the final
additivity step; its public module remains imported. No module is pruned.

## Where the brief, the DAG or earlier work was wrong

The first compile failed because the published cache lacked the original dependency
`Sheaf/AlgebraicGeometry/PrincipalOpenCechSubsetInsertion.olean`. The next cache
refresh supplied it, and all subsequent proof work used the published dependency.
No dependency was reconstructed or compiled independently as a workaround.

The source equation (the project server) is Tag 08C0, linked from 08C1. The actual ordered
face differential is in Tag 01FG preceding Definition 20.23.2; 01FM is the
ordered/alternating comparison homotopy. Those sources were read online because
the local Stacks source is absent. The parent coordinate verification remains
the argument being decomposed.

`blueprint_refs.py ancestor` returns None for this node because `created.item`
records a Lean module rather than a node id. New nodes retain the explicit parent
reference and exact component of its proof; no unrelated metadata was edited.
LeanFinder found total-inclusion component identities; Loogle found `total_d`;
grep read the concrete totalization definitions. LeanSearch returned HTTP 500 and
is recorded as unavailable. Blueprint searches for subset insertion, increasing
tuples, and principal open Cech found no matches.

Edge cases checked: empty cover (empty insertion sum), singleton subsets (vertical
sign one, horizontal empty deletion zero), zero coefficients, and arbitrary
negative total or coefficient degrees. The vertical proof treats all of these
uniformly without a boundedness assumption. The remaining horizontal statement
has the same boundary behavior as the explicit ordered face differential.

## New nodes

`lem-sc-principal-open-cech-subset-insertion-vertical` states only the action of
Mathlib's vertical total differential, with no face terms or restriction/erase
hypotheses. Its Lean proof is complete.

`lem-sc-principal-open-cech-subset-insertion-horizontal` states only the action of
Mathlib's horizontal total differential, with no coefficient-differential term.
Its proof docstring describes tuple deletion, subset erasure, restrictions, signs,
degree transports and regrouping. This is the single remaining proof item.
Both new modules have one public theorem. No change record is needed because
no existing interface changes.

## Second reading by V2

1. Interface preservation: PASS. Diffed the delivered differential module against
   the repository file and its node against the repository node. The existing
   theorem signature is byte for byte unchanged, including A, r, f, J, hle, he,
   every coefficient degree, and both terms of the conclusion. Its docstring,
   visibility, options and public import are unchanged. Only two private proof
   imports and the proof body are added. Both component modules are new; no
   definition or change record is introduced.
2. Proof and trust: PASS as a decomposition, not a completed target proof.
   Compiled all three modules in import order with lcompile.py: horizontal
   12.0 s, vertical 43.7 s, combined differential 11.8 s; no errors or warnings.
   Read both private helpers and the entire vertical and combining proofs.
   The vertical calculation uses the actual summand inclusions, extendMap_f,
   componentwise Pi.single calculation, proved transport naturality, and the
   conversion of the integer sign to the A action. No unproved witness is chosen.
   Explicit #print axioms in a scratch copy gave only propext, Classical.choice,
   Quot.sound for principalSubsetInsertion_vertical; the horizontal and combined
   declarations additionally use sorryAx, as expected. The sole textual sorry is
   the whole proof of the named public horizontal theorem. No forbidden trust
   declaration or sorry in data occurs.
3. Split statements: PASS. Read both new nodes, their complete Lean signatures,
   and their docstring arguments. The horizontal component omits the coefficient
   differential and the vertical component omits all face terms and erase
   hypotheses, so each is strictly part of the original calculation. The open
   component is not a renamed restatement. Checked the ordered face formula at
   https://stacks.math.columbia.edu/tag/01FG (before Definition 20.23.2), and the
   augmentation context at https://stacks.math.columbia.edu/tag/08C0. For r=0
   there are no nonempty subsets; for singleton targets the horizontal term is
   zero and the vertical sign is +1. For S={i,j}, i<j, the horizontal term is
   restriction(s_{j}) minus restriction(s_{i}), and the vertical sign is -1.
   Empty opens, zero coefficients, and negative n do not invalidate either
   argument. Independent msearch queries used 'ordered Cech cochain differential
   increasing enumeration erase finite set' (LeanFinder), Finset.orderEmbOfFin
   (Loogle), and succAboveOrderEmb/orderEmbOfFin_unique/card_filter (grep).
   Also searched lean/Sheaf, lean/WeilConjectures, and the upstream geometry
   sources. Sort uniqueness lemmas and private ordered_erase/ordered_position
   proofs in KoszulCechBoundaryEvaluation support the combinatorics but do not
   prove this total-insertion identity. PrincipalCechTotalRegroup_comm concerns
   a different bicomplex and assumes its horizontal comparison; it is no direct
   substitute. The remaining component needs a substantial tuple/total
   regrouping argument and cannot be closed by a few-minute specialization.
4. Route and pruning: PASS. The combined proof first uses Mathlib total_d and
   generic additivity, then exactly the two component identities, and finally
   additivity of insertion. All imports are used; component imports are private
   and their public import supplies their statement definitions. No import or
   module is pruned. The old definition dependency remains necessary, now
   reached through the components; clarified this in No longer needed.
   Read dag/units/sk-thm-picard-duality.json: realized.statement=[] and its sole
   realized step is []; none of this subsidiary node's route is prescribed there.
5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Its uses union is the two components actually applied. Each
   new node records the definitions used by its statement and calculation,
   its exact component, source, proof steps, searches, worker/item/group/date,
   blueprint parent, chapter/unit, and matching Lean declaration. The vertical
   proof narrative agrees with its finished Lean calculation; horizontal records
   the remaining signed-face and transport argument. No existing statement,
   stmt_deps, or unit record changed.

Second reading changed only this review and the report's explanation of the old
indirect dependency. The Lean proofs and node records required no repair. One
original hole is closed, one horizontal hole is added, and the new vertical
calculation is proved: zero net holes removed, no modules pruned.

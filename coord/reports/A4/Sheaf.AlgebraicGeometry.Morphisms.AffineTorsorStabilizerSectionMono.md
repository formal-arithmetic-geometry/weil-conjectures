## What changed

Proved `AlgebraicGeometry.Scheme.affine_torsor_stabilizer_section_mono` with its original
signature and visibility. Added the proof import for invariant-puncture etaleness. Mathlib’s
formally unramified diagonal and isomorphism APIs are already available from
the original public Etale import. Private proved helpers establish
split-section reconstruction, separation of labels at a field point, lying over on a
subalgebra puncture, and the rotation statement for field-valued puncture maps.
Updated the node proof and dependencies to match the diagonal argument.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.Scheme.affine_torsor_stabilizer_section_mono`
(node `lem-sbc-affine-torsor-stabilizer-section-mono`). Added zero holes. No sorry remains
in the delivered module. The proof uses the existing sorry in
`AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale`
(node `lem-sbc-affine-torsor-invariant-puncture-etale`); this delivery leaves that
separate module unchanged. No new definitions or public statements are introduced; the five new private helpers are proved.

## No longer needed

No original import was removed: all three public imports are used by the unchanged
statement. Removed the direct proof dependency on
`lem-weil-pbc-connected-torsor-subgroup-quotient` and avoided importing
`Sheaf.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient`. This dependency remains
in the existing invariant-puncture etaleness theorem's DAG proof plan; that theorem's
current Lean module has no subgroup-quotient import. No module is claimed pruned from
the entire targets closure. The current module does
not need a GaloisCover structure, the deck-graph isomorphism, a coset-indexed splitting
of U, or a separate faithfully flat descent theorem for monomorphisms.

## Where the brief, the DAG or earlier work was wrong

The original route is valid but more elaborate than necessary for the geometric step.
Finiteness over H already proves integrality over F and surjectivity of q, without
constructing a torsor quotient. Exact stabilizers can be used on residue-field lifts
and followed by the open-diagonal criterion. The unit record's realized statement
and steps are empty, and the unit route is unchanged. The new proof retains the
explicit descent action and does not assume p is finite, etale or separated.
The cases K=G, K trivial and an empty split cover were checked: the cancellation
argument applies to either subgroup, and Fin 0 has no selected x.

Source read: [Stacks 03SF](https://stacks.math.columbia.edu/tag/03SF) and
[Stacks 01S4](https://stacks.math.columbia.edu/tag/01S4). No source statement is changed.


## Second reading by A4

1. **Interface preservation — pass.** Read the complete repository/sandbox diff and
   checked the declaration table. The sole existing theorem's signature is byte for
   byte unchanged, including all ring, domain, finite, faithfully flat, group, etale,
   rotation, splitting and exact-stabilizer hypotheses and the two equations for f.
   Its visibility is unchanged. There are no definition changes or change records.
   The new etaleness import is plain `import`, used only by the proof.
2. **Proof and axioms — pass, conditional on the existing open dependency.** Compiled
   the delivered file with lcompile.py, without errors or warnings (5.9 seconds).
   A scratch copy with `#print axioms` for all six declarations compiled cleanly.
   Each private helper uses only propext, Classical.choice and Quot.sound. The main
   theorem additionally uses sorryAx through the unchanged existing theorem
   `AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale`. The delivered
   source has no sorry or forbidden declarations, and introduces no definitions or
   data chosen from unproved existence. Lying-over and point-lifting witnesses come
   from proved theorems, not the open etaleness theorem.
3. **Split statements and small cases — pass.** Zero new holes and zero split-off
   statements. Read all five private helpers: connectedness forces a single clopen
   coproduct label; equality at a field point separates labels; integral lying over
   restricts to the same basic open; hrot yields the required deck map. The two
   reconstructed-section helpers repeat inaccessible private proofs in SplitAction,
   not an available public declaration. Checked K=G, K trivial, d=1, and d=0 (no x).
   The denominator and domain hypotheses supply a real nonempty puncture. Empty T
   admits no k from this puncture. No characteristic restriction is introduced.
4. **Route, searches and pruning — pass.** Independently searched LeanFinder for
   formally unramified field-point injectivity, Loogle for Etale/Mono, and rg in
   Mathlib and both project roots. No directly applicable replacement was found.
   Mathlib's `tfae_universallyInjective` supplies the diagonal criterion, but applying
   it here still requires lifting two U-points along q to a common field extension;
   the iterated pullback W already gives this directly. The upstream invariant-ring
   APIs require localization identifications and do not shorten this proof. All
   three original public imports serve the unchanged signature; the added import
   supplies exactly etaleness of U. The only removed old proof dependency is
   `lem-weil-pbc-connected-torsor-subgroup-quotient`, completely listed above.
   No import or target-closure module is pruned. Read the unit record
   `dag/units/sk-prop-input-spreading.json`: its realized statement and step lists
   are empty, and neither its statement nor its route is changed by this local proof.
5. **Node consistency — pass.** Only proof, proof_deps and proof_origin differ in the
   existing node. The four proof steps match etaleness and the open diagonal,
   integral surjectivity and K-invariance of q, exact-stabilizer cancellation on
   field lifts, and residue-field factorization through the diagonal. proof_deps
   is exactly the union of their uses: invariant-puncture-etale and split-label-laws.
   No new nodes are needed for split obligations because none were introduced.

**Changes by this reader:** preserved the Lean proof. Corrected the report's claim
of no new statements to no new public statements, and clarified that the removed
subgroup-quotient dependency persists in the imported theorem's DAG plan rather
than its current Lean imports. Made the same public-statement qualification in
proof_origin. Closed 1 existing hole, added 0 holes; this remains a conditional
proof using 1 pre-existing imported hole, not an axiom-free final target proof.

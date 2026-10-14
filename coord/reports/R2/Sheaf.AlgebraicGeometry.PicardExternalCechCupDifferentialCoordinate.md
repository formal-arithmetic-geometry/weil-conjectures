## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι` with its
original signature. Its proof-only import is the new module
`Sheaf.AlgebraicGeometry.PicardExternalCechCupRefinement`. That module constructs the additive
scalar-to-module Cech comparison and uses the uniquely specified existing refinement map. Its
proved `externalCup_bidegree_refinement` identifies external bidegree coordinates with ordinary
cup of the projection-refined cochains. The assigned theorem then follows by tensor-total
inclusion equations, pure-tensor extensionality, cochain-map commutation and the already proved
`cechCupCochain_leibniz`.

Both files compile without warnings using lcompile.py --all (approximately 10 and 32 seconds).
Existing signatures, visibility, definitions and docstrings remain unchanged. The theorem-scoped elaboration
heartbeat allowances accommodate the scalar/product coercion transports; the wall-clock limit
is unchanged. The DAG records the actual proof route. No other existing module is adapted.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
(`lem-sc-picard-external-cech-cup-differential-coordinate`).

Also proved the new helper:
`AlgebraicGeometry.Scheme.Modules.externalCup_bidegree_refinement`
(`lem-sc-picard-external-cech-cup-refinement`). Its auxiliary lemmas are proved. The new data
are the composite of explicit Cech isomorphisms and the unique existing refinement cochain map;
no data are taken from an undetermined existential witness.

No sorry remains in either delivered module; no new holes are added. This is a proof, not a
hole decomposition. The delivery dry run checks the axioms of the delivered declarations.

## No longer needed

No original Lean import is removed. No whole module is claimed globally pruned.
The assigned node no longer needs a direct proof-dependency edge to
`lem-pc-module-pullback-adjunction` or `lem-sc-picard-external-cech-cup-bidegree`: their coordinate
work is used through the new refinement comparison and the existing refinement construction.
Both remain needed transitively. The separate signed-face expansion planned in the assigned
node is unnecessary: the existing `cechCupCochain_leibniz` supplies it.

The previous attempt's exploratory Probe.lean is outside lean/ and excluded from delivery.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-c7526 point B9: corrected the new refinement node's
`blueprint.from` to the nearest blueprint ancestor `thm-sc-theorem-of-cube`,
with the exact requested application place and all five intervening created nodes
in nearest-first order. The previous record incorrectly used the assigned helper
as the blueprint ancestor. No Lean file or proof-dependency record changed in this repair.

The earlier attempt incorrectly treated field-scalar and global-section-scalar Cech degree
objects as definitionally equal. Their categorical products differ. The composite of the two
explicit additive Cech isomorphisms supplies the correct transport. There is no statement
change or disputed statement. Degree zero, empty index families, repeated indices, zero
coefficients and characteristic two are covered without additional hypotheses by the existing
refinement and cup formulas. The blueprint unit's route is preserved.

## New nodes

`lem-sc-picard-external-cech-cup-refinement`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-external-cech-cup-refinement.json`, records the
fully proved comparison with ordinary cup after projection refinements. Its module is
`lean/Sheaf/AlgebraicGeometry/PicardExternalCechCupRefinement.lean`. Sources are Stacks Tags
01FD (refinement rule), 07MB (ordinary signed cup), and 0BED (external Cech pairing), read on
2026-10-14. The change record is `coord/changes/picard-external-cup-proof-elaboration.md`: the interface
scanner treats theorem-scoped local attributes as command changes. The record explains why
these settings do not change any signature or exported attribute; no user module needs adaptation.

## Earlier second reading (a previous round; superseded)

1. PASS. Read the complete diff against the repository module: all three existing public
   declaration signatures, the degree-map definition body, visibility and docstrings are
   byte-for-byte unchanged. The added refinement import is proof-only. The change record
   correctly documents theorem-scoped elaboration attributes; they export no interface change.
   No other existing Lean module is delivered.
2. PASS. Independently compiled both modules in import order with lcompile.py --all:
   refinement 10.9 seconds, coordinate 32.7 seconds, no errors or warnings. Neither delivered
   file contains a sorry or forbidden declaration. Read the scalar isomorphism construction
   and the refinement choice: the latter is chosen from an exists-unique specification
   determining every cochain coordinate, not arbitrary existence data. Separate scratch
   #print axioms checks on all six public declarations report exactly propext, Classical.choice
   and Quot.sound, with no sorryAx. The delivery tool also runs its per-declaration probe.
3. PASS. No statement is left split off with sorry. The new comparison theorem is strictly
   a coordinate identity without a differential assertion, and is fully proved. Its front/back
   restriction calculation is valid for p=q=0 (both factors use the same vertex), repeated
   indices, empty families (no tuples), zero modules and characteristic two. Repeated the
   search with LeanFinder query "Cech refinement pullback Alexander Whitney multiplication
   naturality" and Loogle query '"mapBifunctor", "comm"': only simplicial/refinement and
   homotopy results, no replacement. Local rg and inspection of CechCupPullbackCompat show
   its cup-refinement theorem concerns two modules on the same source scheme, whereas here
   the factors come from two different projections. The existing CechCupProduct Leibniz
   theorem and CechRefinementCochainMap uniqueness theorem are already used.
4. PASS. Followed the proof from the assigned hole through total differential inclusion
   equations, pure-tensor extensionality, additive Cech transport, the coordinate comparison,
   and existing cochain-map commutation and Leibniz. Every direct import is needed: Bidegree
   supplies the public specification, Refinement supplies proof data; both public imports of
   the new helper occur in its public statements or definitions. The two removed original
   proof-dependency edges are both explicitly listed in No longer needed. No module is
   globally pruned. Read dag/units/sk-prop-av-cube.json and its realized field: this is a
   calculation below its general-cube application, and changes no unit statement or step.
5. PASS after repair. Existing node changes are confined to proof, proof_deps and
   proof_origin. Their listed route agrees with Lean; the helper has its own node, source,
   natural-language proof, searches and creation/blueprint records. Replaced the helper node's
   whitespace-collapsed lean.statement with the verbatim multiline Lean signature, as the
   brief requires. Existing node statements and all unit records remain unchanged.

Second-reading changes: corrected the new helper node's verbatim Lean signature and added
this independent review. No Lean proof or interface repair was necessary. Holes closed: the
one original picardExternalCechCupDegreeMaps_comm_ι; holes added: none; split off: zero.

## Second reading by R2

1. PASS. Independently read the complete module diff. All three existing public signatures
   are byte-for-byte identical; the degree-map definition body and existing docstrings are
   unchanged. The only added import in the assigned module is proof-only. No other existing
   module is adapted. The change record correctly describes scoped elaboration settings.
2. PASS. Compiled both delivered files with lcompile.py --all: 9.8 and 29.7 seconds,
   without errors or warnings. Scanned both files: no sorry or forbidden declaration.
   Appended #print axioms to separate scratch copies for all six public declarations:
   each reports exactly propext, Classical.choice and Quot.sound, without sorryAx.
   The scalar comparison is explicitly composed from Cech isomorphisms; the refinement
   choice is determined uniquely in every degree by its coordinate specification.
3. PASS. No statement is split off with sorry. The fully proved new comparison is only
   a coordinate identity, strictly simpler than differential compatibility. Checked its
   front/back restriction argument for degree zero, repeated indices, empty families,
   zero coefficients and characteristic two. A fresh LeanFinder search for "Cech external
   cup tensor product projection refinement cochain identity" returned generic mapping-cone
   and Dold--Kan lemmas, not this comparison. Local rg and inspection of
   cechCup_refinement_naturality found that it requires two coefficients on the same source
   and quasicoherence; it does not replace this two-projection identity.
4. PASS. Followed the proof from the original hole through total summand formulas,
   pure-tensor extensionality, scalar transport, refinement coordinates, and the existing
   cechCupCochain_leibniz theorem. Imports supply either the public data/specifications or
   this proof route. The removed direct dependency edges are both named under No longer
   needed; their uses remain transitive. Read sk-prop-av-cube.json and its realized field:
   this local comparison changes neither its general-cube application nor its unit route.
5. PASS. Parsed the existing node comparison: only proof, proof_deps and proof_origin
   differ. The dependency lists equal the union of proof-step uses and match the Lean
   route. The new node has its source, proof, searches, creation, nearest blueprint ancestor
   and intervening path. Its multiline lean.statement matches the theorem verbatim.

Second-reading changes in this round: appended this independent review; no Lean proof,
interface or DAG repair was needed. Closed: picardExternalCechCupDegreeMaps_comm_ι (one
original hole). Added holes: none. Split off with sorry: zero. Pruned modules: none.

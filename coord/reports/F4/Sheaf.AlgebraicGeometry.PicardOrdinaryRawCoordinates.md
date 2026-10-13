## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_ordinary_raw_coordinates` with a
complete proof from explicit tensor coordinates, affine sheaf frames, and rank-one
residue naturality. Its signature and all original public imports are unchanged.

Added three modules:

- `Sheaf.AlgebraicGeometry.PicardOrdinaryAffineDifferentialFrames`: the affine
  sheaf-frame realization of the supplied section bases and differential column.
- `Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates`: explicit additive
  coordinate equivalences and a fully proved tensor-pullback column formula.
  The proof uses the pinned adjunction to compute unit endomorphisms, the free
  coproduct inclusions to compute coordinate projections, and linearity.
- `Sheaf.AlgebraicGeometry.PicardTensorFrameRestriction`: the remaining rank-one
  residue compatibility statement, using those explicit coordinates.

The main proof obtains the frames, builds all four coordinates, applies the
column formula, and transports scalars through the open-top and spectrum section
isomorphisms. The residue lift's ring map is proved to be evaluation by factoring
it through the stalk lift and residue quotient. No definition chooses a witness
from a mere existence theorem: all new definitions are explicit constructions;
the frames are eliminated only inside a theorem proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picard_ordinary_raw_coordinates`.
Also proved: `AlgebraicGeometry.Scheme.picard_ordinary_affine_differential_frames`,
`AlgebraicGeometry.Scheme.Modules.picardTensorFrame_map`, and all
coordinate constructions and private helpers in its module, including the
pinned tensor-unit conjugation computation.

Added hole, strictly a part of the argument:

- `AlgebraicGeometry.Scheme.picardTensorFrame_restriction`
  (`lem-sc-picard-tensor-frame-restriction`): residue compatibility of one given
  rank-one frame, without affine, perfectness or differential hypotheses.

No sorry remains in the item's module. This is a decomposition of one original
hole into one strictly simpler hole, not an axiom-free proof of the entire statement.
All four modules compile through lcompile.py. The delivery dry run printed OK
without pushing. Edge cases checked in the argument:
zero target rank gives an empty coordinate vector; V may be nonaffine or empty;
residue compatibility assumes w lies in V; no coefficient vanishing is used.

## No longer needed

Removed the direct private import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`. The proof no longer
needs `lem-weil-pbc-affine-tilde-gamma-adjunction`: the supplied bases are
realized by explicit generator maps, using the finite-free retracts already
present in strict perfectness. This node is pruned from this argument's route;
no whole target-closure pruning claim is made where other routes still need it.

Removed the main module's direct private import of
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`; it remains needed by
the tensor-coordinate module and is not claimed pruned. No original public
import was removed, and no unit statement or unit step is bypassed.

Old direct proof dependencies no longer listed on the parent node:
`def-pc-perfect-complex`, `def-sc-picard-ordinary-model-cycles`,
`lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-module-pullback-structure-sheaf`.
Only the affine tilde/Gamma adjunction is unused throughout this new argument;
the other four remain used through the frame, coordinate, or restriction nodes.
`def-weil-residue-field` remains a direct dependency. Thus this report claims
argument-level pruning of the affine adjunction only.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies supply ingredients rather than the simultaneous raw
coordinate theorem. The missing glue separates into frame realization
and rank-one tensor composition naturality. The frame realization has now been
proved by finite-free retract algebra; affineness is unnecessary for that step,
although the original hypothesis is retained in its signature. The tensor differential calculation
has been implemented directly rather than left as a further hole. No statement
was found false and no existing statement or definition was changed.

LeanSearch returned Internal Server Error; the actual unavailable search is
recorded, alongside successful LeanFinder, Loogle and source-grep searches.
The local literature checkout contains only indexes, so the cited Stacks pages
0096, 01I7, 01IB and 0BF2 were read online. Existing blueprint searches for scalar
coordinates, tensor pullback and affine basis found no exact duplicate.

## New nodes

`lem-sc-picard-ordinary-affine-differential-frames` records affine frame realization
and the differential column, now fully proved from the given section bases
and finite-free retracts, the first step of the parent plan.

`lem-sc-picard-tensor-frame-map` records the proved generic tensor column formula
and its explicit coordinate constructions, the second step of the parent plan.

`lem-sc-picard-tensor-frame-restriction` records rank-one residue naturality,
the third step of the parent plan.

The parent node's proof, proof dependencies and proof origin now follow the Lean
argument. No change record is needed: existing signatures and visibility are
unchanged, and all newly required imports in the original module are private.

## Second reading by F4

1. Compared every delivered module with the repository. Only
   `PicardOrdinaryRawCoordinates` existed there; its theorem signature is
   byte-for-byte identical, and its original docstring and public imports are
   unchanged. The additions are three new modules and one private evaluation
   helper. No existing definition, target, hypothesis, conclusion, or visibility
   was changed, so no change record or forced adaptation is required. Verdict:
   pass.

2. Compiled all four modules in import order using `lcompile.py --all`: no
   errors or warnings. The only delivered sorry is the named theorem
   `AlgebraicGeometry.Scheme.picardTensorFrame_restriction`. Searched the Lean
   sources for forbidden declarations and implementation overrides: none.
   A scratch copy with `#print axioms` checked the main theorem, the affine-frame
   theorem, the restriction theorem, the column theorem, and all six public
   coordinate definitions. Frames, column calculation, and coordinate data use
   only `propext`, `Classical.choice`, and `Quot.sound`; main and restriction also
   use `sorryAx`, exactly as the remaining restriction hole requires. In
   particular no coordinate data is chosen from that hole: the q0/q1 witnesses
   come from the proved frame theorem and are eliminated inside the parent
   theorem. Verdict: valid decomposition, not an axiom-free completed item.

3. Read the new theorem statements, docstrings, nodes, the definitions of raw
   restriction and pinned tensor-unit maps, and Stacks Tags
   [0096](https://stacks.math.columbia.edu/tag/0096),
   [0BF2](https://stacks.math.columbia.edu/tag/0BF2), and
   [01CA](https://stacks.math.columbia.edu/tag/01CA).
   The frame lemma isolates realization of the section bases; the column lemma
   isolates the differential calculation; the remaining rank-one lemma proves
   only compatibility of explicit coordinates under the specified raw
   restriction. It assumes neither strict perfectness nor an affine open nor
   a differential, and it does not assert existence of simultaneous coordinates.
   It is therefore strictly a part of the parent argument, not a restatement.
   Checked m=0 (empty vector), the zero morphism (both scalar sides zero), V=U
   (identity open map), and a nonidentity rank-one frame (naturality moves the
   frame through the target comparison). Empty V is permitted in the first two
   parent clauses; membership of w excludes it only in the residue clause.
   Independent searches used LeanFinder's composition-of-left-adjoints query,
   Loogle `conjugateEquiv_unit` (unknown identifier, recorded as such), and grep
   for `unit_conjugateEquiv`, `conjugateIsoEquiv`, and pushforward components.
   Also searched `lean/Sheaf`, upstream scheme modules, and the slopmaster2
   algebraic-geometry sources. Found Mathlib mate/unit identities and
   `etaleTensorUnitRestriction_equation`; the latter concerns an etale-site
   section restriction and cannot apply to a general residue lift. Its generic
   structure-composition calculation is private. No existing public declaration
   has the remaining theorem's statement. Verdict: true, needed, properly
   documented smaller statements; no short existing specialization closes the
   remaining hole.

4. Read the parent proof from its three final clauses upward. Frame realization
   explicitly constructs generators and proves their inverse using the supplied
   finite-free retracts, avoiding the affine tilde adjunction. The column formula
   uses the pinned adjunction and free-coordinate projections; residue evaluation
   factors through the stalk lift and residue quotient. All newly added parent
   imports are private; imports in the new modules supply their signatures or
   coordinate constructions. Expanded `No longer needed` to account for every
   removed direct old proof dependency, distinguishing indirect uses from the
   genuinely unused affine adjunction. The cube unit's `realized` arrays are
   empty in this checkout and no unit or chapter step is removed or bypassed.
   Verdict: route preserved and pruning report complete for this argument.

5. Matched each node's Lean declaration and statement to its module. Parent
   proof steps are the frame theorem, tensor column/evaluation calculation, and
   restriction theorem, and its `proof_deps` is their recorded union. The frame
   node uses strict perfectness; the tensor node uses the proved adjunction and
   pinned unit theorem; the restriction node uses these comparisons and the
   residue definitions. New nodes carry source, searches, blueprint ancestry,
   chapter/unit, creation, and Lean records. Added the independently executed
   composition searches to the restriction node and made its first two proof
   steps agree with the explicit normalization calculation below. Verdict: pass.

Changed in the second reading: made the remaining theorem's docstring proof
explicit. If A_g compares direct pullback with iterated pullback and epsilon_g
is the pinned unit map, its needed identity is
A_g.hom.app O followed by L_i(epsilon_g) followed by epsilon_i = epsilon_g'.
After naturality and cancellation, the normalized restricted morphism is
 epsilon_i inverse followed by L_i(n) followed by epsilon_i.
This states exactly what must be verified by the mate unit equation and makes
clear that different unnormalized source/target structure maps are not simply
being declared equal. Updated the node to match, added independent search
records, completed the direct-dependency pruning accounting, and appended this
review. No Lean statement, definition, import, or proof term was changed.

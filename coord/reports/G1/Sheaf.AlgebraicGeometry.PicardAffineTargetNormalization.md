## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.picard_affine_target_normalization by a
complete Lean proof from two smaller named statements. The original signature, universes,
visibility, and every existing public import remain unchanged.

The geometric step, PicardAffineStructureProjectiveModel, produces an unnormalized
bounded finite projective ring complex and its universal homology conditions. The algebraic
step, UniversalH0ProjectiveNormalization, normalizes an arbitrary such ring complex; it
contains no schemes, morphisms or coefficient sheaves. Neither restates the parent.

The parent explicitly constructs the sheafified normalized complex. Its proof maps finite
free retract equations through affinePerfectSheafification, using the tilde/free and
restriction/over-equivalence unit isomorphisms. It proves strict perfectness, negative-term
vanishing and zero differential, and transports the ring-derived isomorphism through the
affine derived comparison. No data-valued definition chooses a witness from an unproved
existence theorem: all existential witnesses are eliminated within this proposition proof.

Added private proof imports of the two new modules, AffineLocalizedDerivedSheafification,
and WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf. Updated the parent node's
proof, proof_deps and proof_origin. All three files compile with lcompile.py --all.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Scheme.picard_affine_target_normalization
(lem-sc-picard-affine-target-normalization). The item's module contains no sorry.

Added two holes, each in its own new module:

- AlgebraicGeometry.Scheme.picard_affine_structure_projective_model
  (lem-sc-picard-affine-structure-projective-model).
- CochainComplex.universalH0_projective_normalization
  (lem-sc-universal-h0-projective-normalization).

This is a decomposition, not a sorry-free proof: one upper hole closed and two lower holes
added, net minus one before any closure sharing. The complete combining proof is in the
original module. Existing imported dependencies may themselves still depend on sorry.

## No longer needed

No original public imports removed; all describe the unchanged signature. The parent no
longer directly uses or imports PerfectAffineMapRepresentative
(lem-pc-perfect-affine-map-representative). It transports a derived object isomorphism
rather than lifting a derived arrow to a chain map. This dependency is pruned entirely
from the delivered route.

PerfectAffineBoundedProjective (lem-pc-perfect-affine-bounded-projective),
PerfectDirectImageBaseChange (lem-pc-rf-perfect-base-change), and
FlatDerivedStructureUnit (lem-sc-flat-derived-structure-unit) move under the geometric
intermediate; they remain needed there and are not claimed as pruned.
AffineLocalizedDerivedSheafification remains directly needed. AffinePerfectModuleModel is
needed for its actual functor and explicit finite-free term transport, rather than for
its existential K-projective-model theorem.

## Where the brief, the DAG or earlier work was wrong

The original module contained statement imports only; its five planned proof dependencies
were not imported. Their signatures provide affine representatives or local models, but
none provides a globally normalized projective complex on the entire supplied U.
The fixed-affine cancellation argument in the parent docstring was not a theorem interface.
The two new statements expose the geometric conditions and that algebraic cancellation.
No statement is disputed and no target, definition or other module was changed.

The source Tag 0BF2 shrinks to finite-free models. Keeping the supplied affine requires
finite projective terms and global splitting of projective cokernels; this is the original
node's explicitly marked agent adaptation, not an assertion that 0BF2 directly states
global normalization. The new algebraic node records this expansion and the local
finite-projective residue criterion as its tool. Its proof uses no reducedness assumption.

Edge cases checked in words: over the zero ring both proposed statements use zero
complexes; empty U is its zero-ring case. A single R in degree zero already satisfies the
algebraic conclusion. A contractible negative pair cancels by the stated bottom induction.
Nilpotents cannot be dismissed by residue vanishing of matrix entries: the local
square-kernel argument uses universal H0 on the chart itself to prove d0=0.
The universal algebra hypothesis includes square-zero and identity base changes.

Searches: LeanSearch was attempted for each concept and returned Internal Server Error.
LeanFinder returned abstract projective-resolution, K-projectivity and Ext/Tor statements,
not global normalization. Loogle ModuleCat.extendScalars returned the scalar-extension
functor and adjunctions, not normalization. Mathlib grep found
IsLocalRing.split_injective_iff_lTensor_residueField_injective, which is only the local
linear-map criterion. Repository and blueprint searches found local bottom models,
finite-projective cokernel localization and affine projective representations; no new
statement duplicates those. The cube unit's realized lists are empty and its route is
unchanged. The generic affine and module results used in new-node proof plans are tools;
no alternative route for the cube theorem is introduced.

## New nodes

lem-sc-picard-affine-structure-projective-model:
lean/Sheaf/AlgebraicGeometry/PicardAffineStructureProjectiveModel.lean. It carries the
unnormalized geometric direct-image comparison and universal homology conditions, with
no negative-term or differential normalization. Sources: 0BF2, 0B91, 08EB, 06Z0.

lem-sc-universal-h0-projective-normalization:
lean/Sheaf/Algebra/Homology/UniversalH0ProjectiveNormalization.lean. It carries the
fixed-ring cancellation argument for bounded finite projective complexes, independently
of any geometry. Sources: 0BCD, 00O0 and the projective-affine adaptation of 0BF2.

Both nodes inherit sec-abelian-varieties and sk-prop-av-cube, and have full statements,
proof plans, docstrings, Lean records, and the three kinds of search. No change records.

## Second reading by G1

1. Interface: PASS. Compared every delivered module with the repository. Only the
   parent module already exists; its theorem signature is byte-for-byte identical,
   including universes, instance hypotheses, and conclusion. Its public imports and
   visibility are unchanged. No definition or target statement changes. The existing
   node changes only proof, proof_deps, and proof_origin. No change record is needed.
2. Proof: PASS as a decomposition. Independently compiled all three modules using
   lcompile.py --all. The parent has no sorry; the two new named theorems are the only
   delivered holes. Scratch-copy #print axioms checks for all three declarations show
   exactly propext, Classical.choice, Quot.sound, and sorryAx. No axiom declaration,
   unsafe, opaque, implemented_by, extern, hollow definition, or arbitrary data choice
   occurs. Existential objects from the open statements are eliminated only in a proof
   of a proposition. The actual sheafification functor is constructed upstream.
3. Split statements: PASS. Read both complete statements and their dependency
   interfaces. The geometric statement stops before normalization; the algebraic one
   is independent of schemes and supplies precisely the missing cancellation. Neither
   renames the original assertion. Checked the zero ring, empty affine, rank-one
   degree-zero complex, negative contractible pair, and nonreduced-ring case. In the
   last case the local kernel inclusion A→A is multiplication by a non-zero-divisor,
   which forces the outgoing differential to vanish; residue vanishing alone would
   not suffice. Clarified this step and the residue base-change justification in the
   algebraic docstring and its node. Each remaining hole has a source, proof in words,
   new module, and matching node. Repeated LeanFinder searches with different wording
   for affine structure direct images and constant-rank complex splitting, Loogle
   for CochainComplex with Module.Projective, and rg searches of Mathlib and lean/.
   Hits give adjunctions, single-complex splitting criteria with unsuitable bounds or
   injectivity hypotheses, and the local residue split-injection tool; none supplies
   either whole intermediate. Neither hole can be closed by those tools alone in a
   short proof. Sources checked directly: [0BF2](https://stacks.math.columbia.edu/tag/0BF2),
   [0BCD](https://stacks.math.columbia.edu/tag/0BCD), and
   [00O0](https://stacks.math.columbia.edu/tag/00O0). The global projective adaptation
   remains explicitly distinguished from the source's local finite-free construction.
4. Route and pruning: PASS. Read the proof from its conclusion backward through the
   affine comparison, explicit free-retract transport, algebraic normalization and
   geometric model. All new parent imports are private and used. Existing public
   imports serve the unchanged signature. All five old proof dependencies are
   accounted for in No longer needed: affine derived comparison stays direct, three
   move under the geometric intermediate, and the affine map representative is unused
   in the complete new route. Read sk-prop-av-cube and its realized fields; no unit
   statement or step is replaced. Generic affine and module results remain tools.
5. Nodes: PASS. Both new Lean statement records match their signatures exactly.
   Each proof_deps list equals the union of its proof-step uses. Checked required new
   node fields, provenance, sources, searches, chapter/unit and blueprint ancestry.
   The parent proof plan follows the actual two applications and sheafification glue.

Second reading changed only the algebraic proof docstring and corresponding node step
(to spell out the non-zero-divisor argument and homotopy-invariant residue comparison),
plus this report. No Lean proof term, signature, import, definition, or hole count changed.

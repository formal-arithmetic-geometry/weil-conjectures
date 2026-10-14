## What changed

Repaired reviewer X-41124 point C4: Descent proof step 2 now explicitly uses
the affine-open lower-truncation comparison and the left-exact upper-truncation
comparison. Its text is replaced verbatim as requested, and proof_deps lists
both comparison nodes instead of the upper-bound vanishing node. This repair
changes no Lean declaration, proof, signature, import, or hole count.

Repaired reviewer X-d9016 point E2/4. The component declaration no longer takes
an arbitrary epsilon. It uses `affineDerivedPushforwardSheafEdge_canonical`,
constructed independently of the component equation. Its proof now compiles
without a local sorry by cancelling the reverse comparison, applying the
reverse-unit lemma, cancelling the localization/homology isomorphisms, and
using the proved exact-family reverse homology comparison.

The canonical edge is the inverse of the unique natural reverse isomorphism
specified on every K-injective representative. Those specified components are
constructed using a preserved-kernel lift and homology cokernel descent, not
using the component equation. The unique descent theorem determines the entire
natural isomorphism up to equality, so Classical.choose here satisfies the
project's uniqueness rule for definitions. There is no arbitrary witness of
bare existence and no sorry inside any definition.

Claimed interface repairs are delivered together: Compatibility now states the
property of the canonical edge and applies Component; Existence supplies a
witness equal to that canonical edge, by reflexivity. Both modules are held by
G4. The current Edge assembly is held by N4, has its original signature and an
open proof, and needs no adaptation. It is not included in this delivery.

New modules: LeftExactHomologyComparison (all proved),
AffineDerivedPushforwardSheafEdgeDescent, AffineDerivedPushforwardSheafEdgeCanonical
(all declarations proved or constructed), and AffineDerivedPushforwardSheafReverseUnit.
The canonical module is publicly imported where the repaired statement needs
it; ReverseUnit is a private proof import of the component. Single-file local
compilation uses lcompile.py only. No target signature changes.
The unchanged N4 Edge assembly was also compiled separately against the
delivered sandbox overlay and passed (7.2 seconds), confirming that no
forced adaptation is needed. All seven delivery modules passed in import
order; the repaired component took 36.9 seconds, below the 60-second limit.

## Proved and sorry left

Item: repaired `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_component`
(node lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component).
The original arbitrary-epsilon statement is false and has not been proved:
0 of 1 original holes proved. Its hole is retired by the declared interface repair.
The corrected canonical-edge statement has a complete local cancellation proof,
conditional on two strictly smaller open statements. This is an interface repair
and decomposition, not an axiom-free proof of the item. Two new holes are added:

- `AlgebraicGeometry.existsUnique_affineDerivedPushforwardReverseComparison`
  (lem-pc-affine-derived-pushforward-sheaf-edge-descent): independent existence,
  uniqueness, and invertibility of the explicit reverse comparison on
  quasi-coherent derived objects, specified on K-injective representatives.
- `AlgebraicGeometry.affineDerivedPushforwardSheafReverse_unit`
  (lem-pc-affine-derived-pushforward-sheaf-reverse-unit): relation between the
  explicit reverse comparison and the derived unit for an arbitrary sheaf
  complex. It has no exact functor F, no ModuleCat complex C, and no forward edge.

Both holes are whole public named theorems in their own modules, with complete
proofs in words and Stacks sources in the docstrings and matching DAG nodes.
The exact-family identification and the cancellation combining the parts are
proved in Lean. LeftExactHomologyComparison also proves the cycle and homology
naturality formulas by kernel and cokernel cancellation. Canonical includes its
K-injective characterization and invertibility instance without local sorry.
Compatibility and Existence have complete proofs of their repaired interfaces;
neither previously had a hole on the current base. Local hole accounting: 1 false-statement hole retired, 0 original statements
proved unchanged, and 2 holes added. The source-level hole-count difference is
-1; retirement is not counted as mathematical proof progress. All affine results
still depend on `sorryAx`; no claim of complete axiom-free target proof.

## No longer needed

No module is pruned from the target closure. Removed the redundant direct public
import `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` from Component,
Compatibility, and Existence: each already publicly imports Canonical, which
publicly imports Descent, which publicly imports SchemeDerivedDirectImage.
The same declarations remain public through that chain.
No arbitrary-epsilon normalization assumption remains in Component or the
repaired parent Compatibility. The previous conditional cycle-normalization
proof of Compatibility is replaced by application of the repaired Component;
its old proof dependencies are superseded as recorded in the corrected node.
The component's direct planned proof dependency
`def-pc-ringed-spaces-derived-direct-image` is replaced by the canonical edge,
reverse-unit, and explicit left-exact-comparison nodes. It is still used below
those nodes and is not claimed as globally pruned. Zero-witness existence is
replaced with a pinned canonical witness. The unit's realized statements and
proof steps remain untouched.

## Where the brief, the DAG or earlier work was wrong

C4: The unbounded cohomological-bound node only states upper-bound vanishing
for upper-bounded inputs; it does not itself state both truncation comparisons.
The corrected Descent plan cites the two existing comparison nodes separately
and tracks their canonical maps through the explicit kernel/homology formulas.

The returned component's arbitrary epsilon was false: over a nonzero field,
the identity morphism in degree zero on k[0] gives a nonzero isomorphism on the
right, while epsilon=0 gives zero on the left. Removing epsilon and using the
canonical edge fixes that counterexample; no compatibility equation is added
as a hypothesis. For zero rings and zero complexes the construction uses the
same universal properties and has no nonzero assumption.

The repository advanced during earlier repairs: Compatibility now has a
cycle-normalization premise, and Edge's proof is `sorry`, rather than the old
application to a zero witness. This delivery corrects the canonical interfaces
against that current base. Because Edge currently has no invocation of the
changed declarations, editing it would not be a forced adaptation. Its source
is left to its holder N4. The change record lists all direct users and explains
the effect. No public signature of an unheld module is changed.

Read the cohomology display and K-injective computation in Stacks 0AVW and the
unbounded bound-one truncation comparison in 08D4. These justify the canonical
reverse comparison and its invariance under resolution; they do not justify
an equality for every natural transformation. Loogle, LeanFinder, msearch grep,
and local rg found kernel/cokernel, exact homology, and K-injective derived-unit
APIs but no pre-existing canonical affine normalized edge. Those APIs are used
for all construction and algebra implemented here. The new descent proof uses
sections on affine inverse images, where sections commute with products and
quasi-coherent higher cohomology vanishes. Source links:
https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/08D4.

## Statement corrected

Corrected nodes:
`lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component`,
`lem-pc-affine-derived-pushforward-sheaf-edge-compatibility`, and
`lem-pc-affine-derived-pushforward-sheaf-edge-existence`.
Their statement_change records preserve the old statements and enumerate every
DAG citer. On the current base those citer sets are empty: earlier repairs
removed these links from the component and parents. This delivery adds the
canonical Component link back to Compatibility. Edge remains semantically
a user of the canonical construction, but its current DAG proof describes
the original affine calculation without citing these auxiliary nodes. Its
compatible-edge existential statement remains valid and its open proof stays
open. The target statements and the Edge signature are unchanged.

## New nodes

`def-pc-left-exact-homology-comparison`: real preserved-kernel lift and cokernel
descent, with proved naturality and exact-family comparison. No proof hole.

`lem-pc-affine-derived-pushforward-sheaf-edge-descent`: unique natural
isomorphism descended from explicitly constructed K-injective components.
One open theorem, independent of exact-family compatibility.

`def-pc-affine-derived-pushforward-sheaf-edge-canonical`: inverse of that unique
natural isomorphism; choice is from unique data up to equality. No local hole.

`lem-pc-affine-derived-pushforward-sheaf-reverse-unit`: resolution naturality
for an arbitrary representative; one open theorem, strictly a part of the
component argument. It is combined with the independently proved exact-family
comparison and isomorphism cancellation.

Change record: coord/changes/affineDerivedPushforwardSheafEdge_canonical.md.

## Earlier second reading (a previous round; superseded)

1. Compared all seven delivered modules against the repository with diff. Four
   are new. Component, Compatibility, and Existence have exactly the interface
   changes declared in the report, node statement_change records, and change
   record; there are no undeclared signature changes. The arbitrary-epsilon
   counterexample is valid over a nonzero field in degree zero. No target or
   existing definition changes. Local rg confirms no current direct callers of
   the three changed declarations outside their defining modules. The unchanged
   N4 Edge assembly also compiled against this sandbox overlay in 7.0 seconds.
   Verdict: passes as a declared interface repair, not a proof of the old claim.

2. Compiled every delivered file through lcompile.py in import order: all seven
   passed without warnings, Component in 38.0 seconds. A scratch module printed
   axioms for all 19 explicitly named delivered declarations: only propext,
   Classical.choice, Quot.sound, and the reported sorryAx occur. The explicit
   kernel/cokernel comparisons and K-injective component construction use only
   the three allowed axioms. Exactly two local sorries remain, in the two listed
   public theorems; there is no hollow definition or prohibited declaration.
   Choice selects an iso from literal unique existence, fixing both its hom and
   inverse up to equality. Verdict: sound conditional construction; not complete.

3. Read both open statements and their entire docstring arguments and nodes.
   Descent fixes components independently on K-injectives; every derived object
   admits such a representative, so naturality determines the iso uniquely.
   Its invertibility is the affine acyclicity/truncation argument, not an
   exact-family compatibility assumption. ReverseUnit is the resolution
   naturality square for arbitrary sheaf complexes, with no F and no forward
   edge. Neither hole restates the item. Checked zero complexes, zero rings,
   the identity over a nonzero field, arbitrary degrees, and unbounded tails:
   there is no missing nonzero or boundedness assumption. Read Stacks 0AVW and
   08D4: sections on affine inverse images commute with products and have bound
   one on quasi-coherent sheaves. Independent msearch queries (LeanFinder for
   affine direct-image cohomology, Loogle for descHomology, grep for cohomology
   and pushforward), together with local rg and inspection of
   QCohAcyclicDerivedPushforwardCohomology and KInjective, found generic APIs
   already used here but no existing normalized reverse comparison. Verdict:
   true, needed constituent statements, with sources and matching nodes.

4. Traced the proof from the component down: cancel the inverse canonical iso,
   apply ReverseUnit, then use the proved exact-family comparison and functor
   composition. The generic kernel/cokernel API is reused rather than split
   into new holes. Removed three redundant direct SchemeDerivedDirectImage
   imports, retaining the same public exports transitively; the private
   ReverseUnit, Component, SingleHomology, and PullbackContinuous imports are
   proof-only. All old component proof_deps no longer used directly are named
   under No longer needed; no module is globally pruned. Read the unit
   sk-thm-picard-semicon realized record: it remains unchanged; this auxiliary
   repair does not bypass its route. Verdict: genuine reduction below the unit.

5. Compared the nodes' statements and Lean records with the actual signatures,
   and their proof/proof_deps/proof_origin with the definitions and cancellation
   argument. New nodes include source, searches, created, blueprint, chapter,
   unit, and Lean records. Existing statement changes have old statements,
   old dependencies, citer lists, and the shared change record. No DAG field
   outside the allowed delivery fields is altered. Verdict: agrees with Lean.

Second reading changed only redundant imports and this report: corrected the
progress claim to distinguish retirement of the false original statement from
proof of an unchanged statement, and recorded the independent checks above.
The two split-off holes remain open; the corrected component is locally proved
conditional on them. No original item theorem is counted as proved unchanged.

## Second reading by G4

1. Compared all seven delivered Lean modules with the repository using diff:
   four are new; Component, Compatibility and Existence have only the interface,
   proof and import changes declared in the change record. No target is edited.
   The old arbitrary-epsilon component is false for the identity over a nonzero
   field in degree zero with epsilon zero. The corrected theorem fixes the
   canonical edge rather than adding its desired equation as a hypothesis.
   Repository and upstream rg found no external direct applications of the three
   changed declarations. Verdict: declared intermediate-interface repair passes;
   zero unchanged original item statements are counted as proved.

2. Compiled all seven files through lcompile.py in import order, without warnings
   or errors; Component took 31.2 seconds. Inspected all definitions and all
   occurrences of sorry and prohibited constructs. The only two local holes are
   the whole public Descent and ReverseUnit theorems listed above. The kernel
   lift and cokernel descent are real constructions. Classical.choose selects
   from literal unique existence of the entire natural iso, fixing its hom and
   inverse up to equality. The delivery tool also runs its declaration-wide
   axiom probe. A scratch #print axioms check of all 19 named declarations
   also passed: only propext, Classical.choice, Quot.sound, and the reported
   sorryAx occur; the explicit kernel/cokernel construction has no sorryAx.
   Verdict: conditional proofs and permitted unique data, with the
   two reported holes; no complete axiom-free proof claimed.

3. Read both open theorem signatures, docstring proofs, and matching nodes.
   Descent specifies its map on every K-injective representative independently
   of F; uniqueness follows by naturality with representative isomorphisms.
   ReverseUnit is the naturality calculation for arbitrary D, requiring only
   invertibility of Q(q), not of termwise pushforward of q. Checked the identity
   over a field, zero complexes and zero rings, and arbitrary unbounded degrees.
   Read Stacks 0AVW's cohomology display and 08D4's two truncation comparisons:
   affine evaluation preserves countable products and has bound N=1 on QCoh.
   Read the statements of the affine-open lower comparison, left-exact upper
   comparison, and affine higher-direct-image vanishing nodes cited in Descent
   step 2; these supply the two tails and the affine vanishing, respectively.
   Independent msearch queries used LeanFinder (affine unbounded pushforward),
   Loogle (rightDerivedFunctorUnit), and grep (reverseComparison, descHomology,
   KInjective). Results were generic pushforward, cokernel and resolution APIs;
   no existing canonical normalized comparison was found. Verdict: true needed
   constituent claims, not a renaming of Component; their proofs remain open.

4. Traced Component's cancellation with the reverse iso, ReverseUnit, and the
   proved leftExactHomologyComparison_map. Generic kernel/cokernel lemmas do the
   algebra without additional holes. Public imports supply signatures or public
   definitions; ReverseUnit and Component are proof-only imports where used.
   The old component proof dependency def-pc-ringed-spaces-derived-direct-image
   is already named under No longer needed; old Compatibility and Existence
   proof_deps are empty. No global module pruning is claimed. Read the unit
   sk-thm-picard-semicon record: its realized fields are untouched, and the
   repair stays below the unit route. Verdict: genuine conditional reduction.

5. Compared each node's Lean record with its signature and each proof step's
   uses with proof_deps. Existing node edits are confined to the permitted proof,
   Lean and declared statement-change fields. New nodes carry sources, searches,
   created, blueprint, chapter, unit and Lean records. In particular Descent
   step 2 now explicitly cites both truncation comparisons, rather than taking
   them from an upper-bound vanishing statement. Verdict: DAG matches the code.

This reading changed the report only, adding the independent checks and their
limits. No Lean proof or statement needed further repair; the two split-off
holes remain open. Delivery is an interface repair and decomposition, not net
mathematical proof progress.

## What changed

Replaced the single hole in
`AlgebraicGeometry.koszulOpenHom_comparison_square` by a compiled reduction to two
strictly smaller statements. The original signature and public imports are unchanged. The only new direct proof
import is `KoszulOpenHomChainEvaluation`; its public signature already imports the
chain-representative module, so a redundant direct import was removed after validation.

`KoszulOpenHomChainRepresentatives` constructs three pieces of data without holes:
`AlgebraicGeometry.koszulHomChainClass` projects a Hom cocycle to module-valued homology;
`AlgebraicGeometry.koszulOpenHomTranspose` uses the ordinary tilde/sections adjunction
on complexes; `AlgebraicGeometry.koszulOpenHomStageClass` transports that class through
the specified stage iso and the derived homology factor iso. Its one open theorem
identifies stage Hom with these classes and supplies chain representatives. It says
nothing about restriction, the target equivalence, or the comparison map to U.

`KoszulOpenHomChainEvaluation` has one open theorem: evaluation at one is natural on
all derived sheaf objects and agrees with the fraction formula for sheaf chain maps
into F. It says nothing about the stage Hom equivalences or representability of
arbitrary derived arrows. In particular it is not the original square under a new
name: its right side is the explicitly constructed class of a chain map, and it has
no transported representative E or stage equivalence a.

The main proof defines a by the Hom transport along i.inv, pulls an arbitrary phi
back to Q(F), and uses a chain representative t. It pulls psi back by R(i.inv),
checks the augmentation equation by functoriality, applies the chain formula, and
uses naturality of evaluation to push forward by R(i.hom). H.map_comp finishes the
comparison with the specified c. All this combining argument is proved in Lean.
The stage classes are real constructions, not choices from unproved existence
statements. No definition, existing theorem signature, or other module was adapted.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.koszulOpenHom_comparison_square`
(node `lem-sc-koszul-open-hom-comparison-square`).
No sorry remains in the assigned module.

Added two named open statements, each with its full proof plan and source:

- `AlgebraicGeometry.koszulOpenHom_chain_representatives`
  (node `lem-sc-koszul-open-hom-chain-representatives`).
- `AlgebraicGeometry.koszulOpenHom_chain_evaluation`
  (node `lem-sc-koszul-open-hom-chain-evaluation`).

This delivery is a decomposition: one upper hole closed and two lower holes added,
so the immediate hole-count net is minus one, not a complete proof of the mathematics.
The three supporting definitions contain no sorry. The main module compiled after
repairing Hom transport simplification; it needs a documented local heartbeat limit
for its nested derived-functor expressions. All modules remain single-file compilations
under the wall-clock limit. The delivery tool performs the final compilation and probe.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
- `Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KProjective`.

Their node-level results remain planned dependencies of the two new nodes, whose modules
now import them privately for the open proofs:
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-derived-structure-sheaf-hom-hypercohomology`, and
`lem-sc-bounded-above-projective-kprojective`.
They have been moved below the smaller statements, not mathematically eliminated.
`def-sc-koszul-cech-comparison-construction` stays publicly imported for the signature
and the constructed stage class. No old mathematical node or module is claimed as
globally pruned. The unit record has no realized statement or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or source error was found. The original DAG's three steps
are substantial: the existing affine-equivalence theorem does not give the normalized
module-valued stage Hom comparison directly, and the structure-sheaf hypercohomology
statement does not give the fraction compatibility or restriction-of-scalars transport.
These missing glue arguments are now the two explicit smaller items above.

`KoszulOpenHomHomologyComparison` was also read. Its equivalences are specified only
by transition naturality and restriction-zero behavior; they have no chain-map
normalization, so they cannot justify the nonzero square here. Its module is not imported.

Checked r=0 (all positive exterior powers and sections on the empty open vanish),
the zero ring, F=0, zero chain maps, arbitrary unbounded F, and nonregular sequences.
The representation statement uses projective terms of the module tail, not the false
claim that finite free sheaves are projective in all sheaves. The evaluation statement
uses invertibility only after restriction to the union of principal opens.
LeanSearch returned Internal Server Error for both concept searches. Loogle found the
generic K-projective cohomology-class equivalence; LeanFinder found no fraction square.
Mathlib and both library roots were searched, and the ordinary complex adjunction was
used for the explicit transpose. Stacks Tags 08DD, 08D1 and 06Z0 were read online.

## New nodes

`lem-sc-koszul-open-hom-chain-representatives`, in
`dag/nodes/sec-picard-framework/`, records normalized stage Hom and representability
before restriction. Its module is `Sheaf.AlgebraicGeometry.KoszulOpenHomChainRepresentatives`.
Its canonical chain class is constructed from Mathlib's cycle/homology API. The
proof plan retains the affine derived equivalence and K-projective route.

`lem-sc-koszul-open-hom-chain-evaluation`, in the same directory, records natural
evaluation and the explicit chain-map fraction comparison. Its module is
`Sheaf.AlgebraicGeometry.KoszulOpenHomChainEvaluation`. It uses the constructed class
from the first node, but neither its stage equivalences nor its representation assertion.
The parent node now records only these two dependencies and the actual Lean transport
argument. No change record is needed because no existing public interface changed.

## Second reading by R3

1. **Visible interface: pass.** Diffed the assigned module against the repository:
   its existing theorem signature is byte for byte identical, and the original
   public import is unchanged. Only its proof, local elaboration option and private
   proof imports differ. The two supporting modules are new; no existing definition
   or theorem was adapted, and no change record is required.
2. **Proof and trust: pass as a decomposition.** Compiled all three modules with
   lcompile.py. The parent transport proof correctly uses i.inv to obtain a chain
   representative, applies the chain formula, and uses naturality along i.hom.
   Exactly the two reported named theorems remain sorry; no definition contains a
   hole or chooses a representative from an unproved existence theorem. Inspected
   the three definitions: they construct a cycle class, adjunction transpose and
   transport through specified isomorphisms. A scratch #print axioms check of all
   six declarations found only propext, Classical.choice, Quot.sound and sorryAx
   (the latter includes existing open construction theorems). No forbidden feature
   occurs. This closes one hole and adds two; it is not an axiom-free final proof.
3. **Split statements: pass.** Read both complete proof docstrings and their nodes.
   Chain representability is justified by projectivity in ModuleCat plus the affine
   derived equivalence, without assuming sheaves are projective. The evaluation
   statement is only a chain-map compatibility formula and natural evaluation;
   it asserts neither stage representability nor arbitrary stage identifications.
   Neither simply renames the original square. Checked r=0, the zero ring, zero
   complexes/maps, a one-generator unit (division by its stage power), a nilpotent
   generator (empty U), nonregular sequences and unbounded termwise QCoh complexes.
   No regularity or boundedness of F is needed. Independently read Stacks
   [08DD](https://stacks.math.columbia.edu/tag/08DD),
   [08D1](https://stacks.math.columbia.edu/tag/08D1) and
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0).
   Fresh Loogle search for CohomologyClass.equivOfIsKProjective found the generic
   localization equivalence only; a fresh LeanFinder search for structure-sheaf
   naturality with Koszul augmentation found Spec/Gamma naturality only. Read the
   existing KoszulOpenHomHomologyComparison and searched both library roots and
   Mathlib Hom-complex homology: no normalized duplicate or short closure found.
4. **Route and pruning: pass after import repair.** The parent follows the stated
   affine/K-projective and fraction/evaluation route, with a genuine Lean combining
   argument. The three removed direct proof imports and all four old proof_deps
   are accounted for: the comparison construction stays public, and the other three
   dependencies move below the new statements. No global module pruning is claimed.
   The unit sk-thm-picard-duality has empty realized statement/step lists; none is
   bypassed. Public imports of the new modules support their statements or public
   definition bodies; the restored planned theorem imports are private.
5. **DAG: pass.** Checked each lean.statement against its source text and verified
   that each proof_deps is exactly the union of proof-step uses. The parent records
   the two actually applied theorems and the transport argument. Both new nodes
   contain source, proof, origin, searches, split status, creation, blueprint, chapter,
   unit and Lean records; all three supporting definitions are listed by the
   representatives node. The descriptions match the actual constructions.

Second reading changed only the private planned-proof imports: added
AffineQCohDerivedEquivalence and Mathlib HomotopyCategory.KProjective to
KoszulOpenHomChainRepresentatives, and DerivedStructureSheafHomHypercohomology to
KoszulOpenHomChainEvaluation. This makes the dependencies recorded for the two
open proofs available where those proofs will be completed. Updated this report
accordingly; no signature, definition, proved argument, node or hole count changed.

## What changed

Closed the sole hole in `Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing`:
`AlgebraicGeometry.isZero_restrict_higherDirectImage_of_affine_basis`. Its statement,
universe, visibility, public imports and existing docstrings remain unchanged.

The affine-basis argument identifies the section-cohomology presheaf values with the
hypothesis, restricts every germ to an affine neighbourhood, and transports zero stalks
through `higherDirectImagePresheaf`. Mathlib's abelian-sheaf stalk criterion and faithfulness
of the forgetful functor give zero of the restricted-source higher direct image.

Repaired the earlier delivery's import cycle by constructing the open-restriction comparison
inside the proof. Source restriction preserves injectives by the existing
`RingedSpace.restrict_injectiveResolution` theorem and the over-site equivalence.
Exact restriction maps an injective resolution to a resolution of the restricted module.
A proved private helper constructs the termwise pushforward/restriction isomorphism from
Mathlib's cartesian open-image equality and the commutative square on scalar maps.
Homology comparisons then give the required isomorphism. Another proved private helper
checks limit preservation on underlying presheaves; additivity is checked pointwise.
These elementary helpers avoid importing the large quasi-coherent-kernel module merely
for its restriction-exactness instance. No new public declaration or interface is added.

Updated the existing node's proof, proof_deps and proof_origin to follow the Lean proof.
There are no interface changes, new modules, or forced adaptations.
The unit `sk-thm-picard-duality` has empty realized statement and step lists.
No realized unit step is bypassed. Degree zero and empty opens are included:
there is no positive-degree assumption and the germ argument is pointwise.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.isZero_restrict_higherDirectImage_of_affine_basis`
(node `lem-pc-higher-direct-image-affine-basis-vanishing`).
No sorry remains in the item. No holes were added or split off.
Axiom inspection of the theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` is reachable from its proof. The complete proof closes
the hole without adding any lower hole. Local compilation succeeds. The delivery dry run
compiles and passes preflight, pending the independent second reading; nothing was pushed.

## No longer needed

Removed original proof import `Sheaf.AlgebraicGeometry.SheafZeroStalks` and dependency
`pqf-lem-sheaf-zero-stalks`: Mathlib's abelian-sheaf stalk criterion and faithfulness
suffice. Its auxiliary ringed-space module-stalk interface is also unused here.

Removed redundant direct import `Sheaf.Topology.PresheafModuleStalkFunctor`.
Its declarations and node `def-weil-pbc-module-stalk` remain used through the public
imports of `Sheaf.Paper.HigherDirectImagePresheaf`; only the direct import is pruned.

Removed the earlier attempt's added import
`Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction` and dependency
`lem-pc-higher-direct-image-open-restriction`. Neither that module nor
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` is needed for this proof.
The restriction comparison is constructed from the original restriction-resolution
node instead. Retained `Sheaf.Topology.RestrictInjectiveResolution` and
`lem-sc-ringed-space-restrict-injective-resolution`, reversing the earlier attempt's
incorrect pruning of that edge.

These are dependency edges removed for this item; modules reached elsewhere are not
claimed to leave the global target closure. All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's report incorrectly claimed the open-restriction wrapper was
acyclic. The actual dependency path is HigherDirectImageOpenRestriction →
DirectImage.Sections → LocalUniformHigherDirectImageBound → this item.
Compiled artifacts alone did not reveal this source-level cycle. The repaired proof
imports neither of the first two modules and constructs the comparison locally,
using the existing restricted-resolution declaration exactly as the original DAG planned.

The earlier attempt's second-reading section was removed because this is the worker's
repaired handoff, awaiting a separate reader. No mathematical statement fault was found.
The prior LeanFinder, Loogle and grep searches remain recorded in searches.jsonl;
they found no direct affine-basis theorem. This repair also read the now-proved source
open-base-change argument and reused its Mathlib termwise comparison construction locally.

## Second reading by Q4

1. PASS. Compared the complete delivered module with the repository using `diff` and
   checked the existing theorem signature byte for byte. Its binders, hypothesis,
   conclusion, universe and visibility are unchanged. All original public imports
   remain; the two added Mathlib imports are proof-only. There are no interface
   changes, change records, or adapted modules.
2. PASS. Independently compiled the module through `lcompile.py`, with no errors or
   warnings. Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.isZero_restrict_higherDirectImage_of_affine_basis`: exactly
   `propext`, `Classical.choice`, `Quot.sound`. Inspected both private helpers and
   the resolution construction: no sorry, forbidden declaration, hollow definition,
   or arbitrary witness selected from an unproved existence theorem. The termwise
   comparison is an explicit composite of natural isomorphisms; J has the explicit
   restricted complex and augmentation. Zero stalks are transported in the correct
   direction, and faithful forgetting reflects the zero identity.
3. PASS (no split-off statements). No new public statements or holes are added.
   The local limit-preservation proof and cartesian pushforward/restriction helper
   have complete proofs. Checked degree zero, empty U, empty inverse images and the
   zero coefficient sheaf: the argument requires no positive degree or nonemptiness.
4. PASS. Searched the library with `restrict.*rightDerived`,
   `rightDerived.*restrict`, `isZero.*affine`, `affine.*isZero` and restriction-limit
   patterns, and read the matching ordinary restriction and unbounded affine-detection
   results. The ordinary restriction wrapper imports DirectImage.Sections, which
   imports LocalUniformHigherDirectImageBound and hence this item, so it is unusable
   here. The unbounded detection result uses different derived-category objects and
   does not provide a shorter ordinary comparison. The private square construction
   agrees with the explicit source-library proof, whose helper is private. The local
   limit proof agrees with the existing QuasicoherentKernel instance without importing
   that larger module. Mathlib's abelian-sheaf stalk criterion already supplies the
   final detection step. All proof imports serve the argument; `## No longer needed`
   lists every removed original dependency (only `pqf-lem-sheaf-zero-stalks`) and
   direct import. The unit's realized lists are empty (`statement: []`, `steps: [[]]`);
   no realized statement or step is bypassed.
5. PASS. Compared the node JSON: only `proof`, `proof_deps`, `proof_origin` change.
   The proof steps describe the actual evaluation, germ, stalk and restriction
   comparisons; their uses have union exactly equal to `proof_deps`. Read the
   existing restricted-resolution and higher-direct-image-presheaf declarations
   used by the proof and checked their application. No new nodes need checking.

Second reading changed only this report to record the independent review. The Lean
proof and node required no repair. One original hole is closed, zero holes are added;
this is a proof, not a decomposition. Local compilation and the independent axiom
inspection both pass.

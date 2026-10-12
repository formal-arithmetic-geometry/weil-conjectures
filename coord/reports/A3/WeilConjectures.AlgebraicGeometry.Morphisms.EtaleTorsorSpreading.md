## What changed

Replaced the one remaining proof gap in
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` by an explicit construction
of `Scheme.GaloisCover`. The theorem first chooses a finite étale surjective scheme extension
with a cartesian comparison, then extends the generic action to that chosen scheme, and
fills every field of the cover structure. The comparison and equivariance witnesses are
returned directly. All existing declaration signatures and docstrings are unchanged, and
the already proved abelian torsor corollary is unchanged.

Added two proof-only imports, each for a new intermediate theorem. The new statements
split cover existence from extension of the action and torsor identity. The action theorem
is about an arbitrary given finite étale extension; it has no rational point, section,
compactness, quasi-separatedness, or invertible-order assumptions. It cannot produce an
extension on its own. The cover-existence theorem supplies no group action. Neither is the
original conclusion under a new name.

Updated `sbc-thm-spreading-finite-etale-galois` in the sandbox to record its actual declaration
and the two dependencies used by the construction. The unit's trait, maximal-open,
depth-two and limit route is retained in the underlying-extension lemma's proof in words.
There are no definition changes, statement changes, or change records.

Validation: all three files compile locally in import order with no warnings. The delivery
dry run supplies the independent server checks and axiom probe. No agents were started.

## Proved and sorry left

The item's original one sorry is reduced, with a complete compiling proof of
`AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre` from the following
two inputs. This is a reduction, not an axiom-free proof of the mathematical theorem.
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre` remains proved from
it as before. No sorry remains directly in the item's module.

Exactly two new declarations retain sorry, each as its entire proof:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_finiteEtale_extension`, node
  `lem-sbc-underlying-finite-etale-extension`, module
  `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension`.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_action_on_finiteEtale_extension`, node
  `lem-sbc-generic-fibre-action-extension`, module
  `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`.

Both have source references, full proofs in words, exact Lean signatures in their nodes,
and no postponed data or proof inside any definition. Their grouped proof steps remain
substantial mathematical tasks, with the classical tags named explicitly for the next
worker. Nothing in the item claims those steps have been formalized.

Edge cases checked: a trivial group gives the identity cover; a nonconnected torsor is
handled by component stabilizers in the cover construction, while action extension uses
normalization componentwise. Geometrically connected fibres are nonempty in Mathlib, so
an empty total family is excluded by that assumption over the integral base. The action
lemma permits a noninvertible group order, since a finite étale extension is already given;
it never asserts that such an extension exists. The generic comparison makes that given
extension nonempty. No extra hypotheses are added to the original theorem.

## No longer needed

No original imports, modules or nodes are pruned. The original node had no proof
dependencies to remove, and its five public imports are required by its unchanged statements
and existing public interface. The two new proof imports are both used by the construction.
The action helper omits the quasi-separatedness import used by the cover-existence helper.
All steps of the spreading unit remain needed inside the underlying extension input.

## Where the brief, the DAG or earlier work was wrong

The requested module has one sorry, not two: the abelian corollary was already proved.
The only matching theorem node has no `lean` record and an empty `proof`/`proof_deps`;
its blueprint proof text records a classical input with no separate proof. The unit has
an extended proof sketch, but all its `realized` entries are empty. Thus there were no
existing step declarations to import for the advertised minimum assembly. Searches of
Mathlib, the two library roots, the DAG and blueprint found no declarations for the
needed cover extension or generic action extension. LeanFinder returned only ring-theoretic
étale results and elementary scheme étale facts; Loogle and Mathlib grep had no matches.
LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.

The literature tree named by the repository is not present on this machine. The source
proofs were read on the official Stacks pages for 0EZJ, 0EYJ and 0BQM. The original cover
structure deliberately permits disconnected torsors, whereas the classical terminology
sometimes requires a connected Galois cover; the component/stabilizer reduction is explicit
in the new proof sketch. No target statement or unit route was changed.

## New nodes

`lem-sbc-underlying-finite-etale-extension` records the existence of the underlying finite
étale surjective extension and cartesian comparison, without an action on it. Its module
is `lean/Sheaf/AlgebraicGeometry/Morphisms/UnderlyingFiniteEtaleExtension.lean`. Its proof
sketch retains the trait, depth-two maximal-open, and Noetherian approximation arguments of
the unit and Stacks 0EYJ/0EZJ; disconnected torsors use stabilizer covers and induction.

`lem-sbc-generic-fibre-action-extension` records the action and torsor identity on any given
finite étale extension. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/GenericFibreActionExtension.lean`. It uses full
faithfulness of generic restriction for normal finite étale covers (Stacks 0BQM) to extend
automorphisms, their laws, and the inverse of the torsor comparison. It has no cover-existence
conclusion and no invertibility or section assumptions. Both nodes serve the original
spreading theorem in the same chapter and unit. No change records are required.

## Second reading by A3

1. Interface comparison — PASS. Read the complete diff against the repository module.
   Both existing declaration signatures and their docstrings are byte for byte unchanged;
   the abelian corollary's proof is unchanged. Only the Galois-cover proof and two plain
   proof imports differ. Neither helper supplies a changed definition, and there are no
   change records or adaptations of other existing modules.
2. Proof and axioms — PASS as a reduction with two explicitly open inputs. All three
   modules compiled locally in dependency order, without warnings or errors. The only
   literal sorries are the entire proofs of the two public named helper theorems listed
   above. There are no hollow definitions or forbidden declarations. A scratch copy of
   the item, with `#print axioms` for both helpers and both spreading theorems, compiled;
   all four report exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Thus this delivery closes the item's direct proof gap but does not yet establish an
   axiom-free spreading theorem. The scratch module was removed before delivery.
3. Split statements — PASS. Read each signature, docstring, and node. Checked the
   trivial group, disconnected split torsors, and the action lemma with noninvertible
   group order. For the latter, a finite étale extension is assumed; uniqueness of
   extension from the generic point needs normality, not invertibility. Smoothness and
   geometrically connected fibres make the total family normal integral, and its generic
   fibre contains its generic point. The pullback witness identifies the given torsor
   with the generic restriction. These hypotheses exclude a hidden vertical component.
   The underlying-extension statement supplies no action; the action statement cannot
   produce an underlying extension. Each is strictly a part of the original argument,
   and the item assembles all cover fields explicitly. Checked the source arguments in
   [Stacks 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
   [0EZJ](https://stacks.math.columbia.edu/tag/0EZJ), and the fully faithful restriction in
   [0BQM](https://stacks.math.columbia.edu/tag/0BQM). Independent LeanFinder queries about
   extending morphisms from the function field and tame covers split along a section,
   Loogle searches for normalization isomorphisms, and Mathlib/repository grep found no
   replacement for either helper. Normalization's universal property is useful groundwork,
   but does not already give the required normal generic-restriction theorem. Also read
   NormalGenericConstant, EtaleNormalComponents, FiniteEtaleLiftingApproximation and
   ExtendOverInertia: their hypotheses or conclusions differ. Neither open helper can
   be closed in a few minutes from these declarations.
4. Route and pruning — PASS with the existing unit bookkeeping limitation recorded above.
   The proof starts at the original gap and combines the underlying cover with the
   action, without bypassing the trait, maximal-open, depth-two, or limit arguments:
   these remain explicitly in the underlying helper's proof in words. Read the unit's
   seven steps and `realized` record; all realization lists were already empty and none
   is removed or replaced by this delivery. There were no original `proof_deps` to prune.
   All five original public imports are needed to state the unchanged interface; each
   new helper import is plain and is used. No modules or nodes are newly redundant.
5. DAG agreement — PASS. The item's three proof steps match its actual construction;
   their used-node union is exactly its two `proof_deps`. The helper nodes match their
   Lean signatures, chapter, unit, blueprint ancestry and source. Both have complete
   creation and Lean records, three kinds of searches, and named docstring proofs.
   Their empty formal dependency lists describe open sourced inputs, not completed Lean
   proofs. No statement, target, or unit route was changed.

Second-reading repairs: expanded the new action helper's proof explanation to distinguish
restriction to the generic point of C from restriction to Cη: extend at the former, then
use faithfulness over the normal integral Cη to recover the entire given generic-fibre map.
Mirrored this in its node. Removed stray Lean comment terminators from the final proof
steps of both new node JSON files, and added the independent search results to both nodes.
The compiling proof terms and all signatures were retained.

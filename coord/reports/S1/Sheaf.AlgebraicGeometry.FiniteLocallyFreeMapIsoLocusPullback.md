## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback`
with a complete Lean assembly. At every source point, the existing natural
pullback-stalk comparison transports invertibility to the scalar extension of the
original stalk map. Two new, independent intermediate statements reflect that
invertibility to the original stalk and extend its inverse to an open neighbourhood.
The existing membership criterion puts the point into the constructed union.
All three added imports are proof-only. Existing signatures and definitions are unchanged.
The original DAG node now follows this assembly.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.range_subset_moduleMapIsoLocus_of_isIso_tensorPullback`.
This is a decomposition, not a complete proof from sorry-free dependencies: one
upper hole is closed and two lower holes are added, net -1. No sorry remains in the
item's module.

Added holes, each in its own public theorem and new module:

- `AlgebraicGeometry.Scheme.Modules.isIso_moduleStalkMap_of_isIso_extendScalars`
  (node `lem-sc-finite-locally-free-stalk-base-change-reflects-iso`). This is only
  local-ring reflection at one stalk; it makes no assertion about any open or locus.
- `AlgebraicGeometry.Scheme.Modules.exists_isIso_tensorPullback_of_isIso_moduleStalkMap`
  (node `lem-sc-finite-locally-free-stalk-iso-neighborhood`). This is inverse
  spreading from an original stalk; it has no base-change hypothesis or range assertion.

The main theorem and both statement modules compile through lcompile.py.
The delivery dry run printed OK; nothing was pushed. The only deferred preflight
requirement is the second reading, which the designated second worker supplies. The
premise of the first intermediate theorem is obtained by applying a genuine natural
isomorphism to a stalk of the pullback, not by assuming the desired conclusion.
Empty T is vacuous; zero ranks give empty matrix identities; unequal ranks make
invertibility impossible. Nonreduced schemes are allowed: the argument uses units
in local rings, not reducedness or flatness of the scheme morphism.

## No longer needed

No original imports, nodes, or modules are pruned. The original finite-frame and
open-immersion ingredients are still needed in the intermediate statements.
No claimed global pruning: the parent node's direct proof dependencies are now
its two intermediate nodes, the pullback-stalk comparison, and the locus definition.

## Where the brief, the DAG or earlier work was wrong

The original two steps call the finite matrix argument elementary but provide no
public intermediate declaration for either local-ring reflection or inverse
spreading. Existing matrix-lifting lemmas concern maps already pulled back to
Spec of a local ring, and do not directly accept a module-stalk inverse.
The exact Stacks tags are [00O0](https://stacks.math.columbia.edu/tag/00O0)
for Lemma 10.79.4 and [05GF](https://stacks.math.columbia.edu/tag/05GF)
for Lemma 10.79.2; 05GD is their section. The tensor-pullback stalk comparison is
[0098](https://stacks.math.columbia.edu/tag/0098).
The unit record sk-prop-av-cube has no realized statement or step at this lower level;
this decomposition preserves the original finite-matrix route.
LeanFinder, Loogle and grep were run; LeanSearch returned HTTP 500 and is recorded
as unavailable. Blueprint-wide searches for stalk/free and isomorphism/neighbourhood
found no statement of these two intermediate conclusions.

## New nodes

`lem-sc-finite-locally-free-stalk-base-change-reflects-iso` states local reflection
for a finite locally free stalk along the local ring map of a scheme morphism.
Its complete proof sketch reduces to finite matrices, residue-field extension,
and the adjugate over a local ring. Module: FiniteLocallyFreeStalkBaseChangeReflectsIso.

`lem-sc-finite-locally-free-stalk-iso-neighborhood` states extension of a stalk
inverse to a neighbourhood. Its proof sketch represents finitely many inverse
coefficients by sections, shrinks for both inverse identities, and transports
restriction to tensor pullback. Module: FiniteLocallyFreeStalkIsoNeighborhood.

No change records or forced adaptations are needed.

## Second reading by S1

1. **Visible declarations and statements:** I compared the delivered item module
   with the repository version. The existing theorem signature and all existing
   declarations are unchanged byte for byte; the two additional theorem
   signatures are recorded by their new DAG nodes. Verdict: pass.

2. **Compilation and proof status:** I compiled all three sandbox modules with
   `lcompile.py --all`; they compile cleanly. The item theorem has no `sorry`,
   while the two explicitly split intermediate theorems retain their named
   `sorry`s and have matching nodes. No forbidden declaration or hollow
   definition was added. Verdict: pass subject to the two documented split
   obligations.

3. **Truth and strength of split statements:** The base-change theorem is the
   local finite-free reflection statement needed at one stalk, and the
   neighbourhood theorem is exactly the local inverse-spreading statement
   needed for membership in the locus. Neither restates the parent target or
   adds extraneous hypotheses. Their docstrings give complete source-based
   proof sketches and edge cases. Verdict: pass.

4. **Pruning and route:** The proof uses the tensor-pullback stalk comparison,
   both split statements, and the existing locus membership criterion. The
   original imports and proof-dependency route remain needed; no unused import
   or node was found. The unit route is preserved. Verdict: pass.

5. **DAG agreement:** The parent node's proof and `proof_deps` name the two
   intermediate nodes and the declarations actually used. Each new node has a
   matching Lean declaration, source, proof sketch, chapter, and unit metadata.
   Verdict: pass.

I changed only this report section; no Lean proof, statement, definition,
import, or DAG node required repair during second reading.

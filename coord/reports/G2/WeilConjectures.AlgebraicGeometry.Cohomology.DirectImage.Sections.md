## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`
from the existing natural module/source cohomology comparison, affine quasi-coherent
vanishing, higher-image quasi-coherence, and the Leray edge isomorphism. Compose the
existing additive comparisons with the inverse Leray edge and use their naturality
to prove the required coefficient square. All existing declaration
signatures, visibility, definitions and other proof bodies are unchanged.

Moved the unchanged `isQuasicoherent_higherDirectImage` section before its use.
Added `open TopologicalSpace`, which also resolves the open-cover names in the existing
compact-base vanishing proof. The bookkeeping record is
`coord/changes/sections-existing-proof.md`; no interface meaning changes.

The second reader found the already proved
`AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_source_comparison` in
`Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`. The delivered proof uses
that module as a proof-only import. The redundant proposed new comparison module and
node were removed from this delivery.

## Proved and sorry left

One of the four existing item holes is closed:
`AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`
(node `lem-pc-cohomology-sections-affine-base`). Zero holes are added; zero are split off.
This is a proof from existing dependencies, not a decomposition into new holes.

The three unchanged item holes are:

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`
  (node `lem-pc-finite-support-hi`, blueprint unit `sk-thm-picard-coherence`).
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`
  (node `lem-pc-flat-rf-open`).
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`
  (node `lem-pc-finite-support-hi`, blueprint unit `sk-thm-picard-coherence`).

The private inverse-naturality helper is proved. Existing unfinished quasi-coherence
and imported Leray dependencies remain, so this is not an axiom-free completion of
the targets. No data is defined by selecting an arbitrary unproved existence witness.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.Paper.PQFCohomology`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums`
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`
- `Sheaf.AlgebraicGeometry.DerivedQCohDirectSums`
- `Sheaf.AlgebraicGeometry.ProjectionFormulaLocality`
- `Sheaf.CategoryTheory.DerivedModuleFreeGeneration`

These imports are unnecessary for the item proof bodies; PQFCohomology remains
available through the retained Leray import. No former DAG proof dependency is
removed: the actual argument retains the quasi-coherence, affine vanishing, separated
implies quasi-separated, and Leray route. The only added proof dependency is the
existing node `lem-sc-module-cohomology-source-comparison`.

The proposed new `Sheaf.AlgebraicGeometry.ModuleCohomologyNaturalComparison` and
`lem-pc-module-cohomology-natural-comparison` are not delivered, since the existing
comparison already supplies their content. This list records imports pruned from this
item; it does not claim all these modules become unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The first worker overlooked the already landed natural source comparison.
Reusing it removes duplicate construction and the need for a new node, while keeping
Stacks 01XK's Leray route. The returned attempt's compiler-limit issue disappears
because the proposed new comparison module is unnecessary. No target or intermediate
statement is weakened, and no definition or forced adaptation is needed.

## Second reading by G2

1. **Interfaces: pass.** Compared the entire item with the repository using `diff`
   and the declaration parser. Every existing signature is byte for byte unchanged;
   only the affine-sections proof body changes. The quasi-coherence section moves
   intact, and the bookkeeping record describes the namespace-opening command.
   Public imports and existing definitions are unchanged. No additional module is
   delivered, and no forced adaptation is involved.
2. **Proof and axioms: pass, relative to the existing open dependencies.** The final
   item compiles through `lcompile.py` in 13.2 seconds without errors or warnings.
   A scratch copy with `#print axioms` compiles in 15.7 seconds. The closed item hole,
   existing comparison, and three remaining item holes use only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The comparison's inherited
   `sorryAx` is reported explicitly: its proof body is closed, but its imported
   acyclicity dependencies are not all closed. The delivery introduces no new
   `sorry`, axiom, unsafe/opaque declaration, extern, or hollow definition.
3. **Split statements: pass, none delivered.** There are no new statements with
   `sorry`. Searches by terminal-open Ext and by module/source comparison found
   `exists_moduleCohomology_source_comparison`, already proved in the library.
   It supplies exactly the additive equivalences and naturality needed, without
   quasi-coherence assumptions. Its singleton free-group identification and
   coefficient naturality work at q=0, for zero modules, and for the empty scheme.
   Loogle for `cohomologyPresheafFunctor` confirms Mathlib's Ext model rather than
   an additional module/source comparison. Removed the redundant proposed module
   and new node rather than restating the item's conclusion.
4. **Route and pruning: pass.** The proof follows the prescribed Leray route:
   separated implies quasi-separated; higher images are quasi-coherent; positive
   cohomology on the affine base vanishes; the Leray edge is invertible; composing
   its inverse with the existing additive comparison gives the required natural
   equivalences. Inverse naturality is proved by cancellation, and coefficient
   naturality is exactly the existing comparison's square. Retained proof imports
   provide this route and the unchanged projection-formula proof. The eight
   removed imports are listed above. No former `proof_deps` entry is removed.
   Read `dag/units/sk-thm-picard-rr.json` and
   `dag/units/sk-thm-picard-coherence.json`: their `realized` entries are currently
   empty, and this delivery changes neither unit nor any unit step. The use of
   quasi-coherence is the existing accepted tool use, not a route replacement.
5. **DAG: pass.** Only the existing affine-sections node's `proof`, `proof_deps`,
   and `proof_origin` change. Its statement and Lean declaration record stay
   unchanged. The dependency list equals the union of the proof steps' `uses`,
   and now names the existing `lem-sc-module-cohomology-source-comparison`.
   No new node is needed. The remaining item holes keep their existing nodes.

Second reading changed the affine-sections proof to use the already landed additive
comparison directly, removed the redundant comparison module and node, made the
subsingleton instance explicit in the source H model, and updated the DAG and report.
The first attempted packaging as a whole natural isomorphism timed out; the final
argument composes additive equivalences directly and requires no option changes.

Delivery validation: `deliver3.py G2 WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections --no-push` printed OK: compilation and preflight pass. The review class is CODEX because the existing node, declaration-order commands and change record change, and this repairs a returned delivery.

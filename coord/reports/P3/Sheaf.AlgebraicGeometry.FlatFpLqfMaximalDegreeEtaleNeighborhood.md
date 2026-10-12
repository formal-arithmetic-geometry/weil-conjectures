## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree`
without changing its signature or existing docstring. The proof follows Stacks Tag 07RY:
use the existing elementary etale splitting; make its finite part locally free;
shrink to its degree-m locus; use additive fibre degrees and the bound to eliminate
the complement; transport to the specified pullback projection.

Five private helpers are proved in the item module: finite global sections over a
field, finite-fibre base change, additivity on complementary opens for a finite
fibre, finiteness of a clopen fibre part, and emptiness of a finite degree-zero fibre.
In particular, base change is proved directly from the source library's affine
scalar-extension comparison and Mathlib's `Module.finrank_baseChange`, avoiding the
holed `FiniteFiberDegreeBaseChange` interface. The node's proof and proof dependencies
were updated to match this argument. No new modules, nodes, or statement changes.

Local compilation is clean. The argument includes m=0, empty fibres, and empty
bases; the distinguished-point premise makes the empty-base case vacuous. Only the
etale splitting and local-constancy proof imports remain.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree`
(node `lem-weil-pbc-flat-fp-lqf-maximal-degree-etale-neighborhood`).
No sorry remains in the delivered module and no holes are added. This is a proof
from existing declarations, not a decomposition into new holed statements. The
existing splitting declaration may still depend transitively on unfinished work;
this delivery does not claim to close those dependencies.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange` and removed
`lem-weil-pbc-fibre-degree-base-change` from this item's proof dependencies. Neither
`finite_fiber_degree_pullback` nor `boundsFiberDegrees_pullback_snd` is used here.
This module may remain needed by other parts of the target closure.

Removed redundant proof import
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; its definitions and proved
API are already publicly available through `FiberDegreeBound`. Its module and the
finite locally free definitions remain mathematically needed; this is import
cleanup, not a claim to prune that module from the target closure.

No other planned nodes are pruned. The etale splitting, degree local constancy,
finite-fibre finiteness, flat/presentation permanence, and open restriction steps
are all retained. No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The general affine-morphism theorem `fiberDegree_of_isCompl` cannot be applied
directly to the pullback projection, whose affineness is not known. The proof
instead applies it to each finite fibre, then transports the result along
`fiberRestrictIso`; this needs no affine-morphism hypothesis on the projection.

The supplied `h_lqf` is redundant for this proof because `BoundsFiberDegrees`
includes finiteness of every scheme fibre, and local finite presentation supplies
local finite type for the splitting theorem. Its binder is preserved unchanged;
the unused-variable linter is disabled locally for the existing theorem only.

The local literature source file is absent; the exact cited paragraph was read
from the primary Stacks source at https://stacks.math.columbia.edu/tag/07RY.


## Second reading by P3

1. **Visible declarations: pass.** Compared the complete delivered module with the
   repository using `diff -u`. The original theorem signature and docstring are
   byte-for-byte unchanged. No definition, public import, or existing declaration
   was changed. The only Lean changes are its proof, five proved private helpers,
   two local options, and removal of two proof-only imports. The node changes only
   `proof`, `proof_deps`, and `proof_origin`; no change record is needed.

2. **Kernel proof: pass, with existing open dependency.** Recompiled the delivered
   file through `lcompile.py` without errors or warnings. Compiled a scratch copy
   with `#print axioms` for all five helpers and the main theorem. Each helper uses
   only `propext`, `Classical.choice`, and `Quot.sound`. The main theorem also uses
   `sorryAx` through existing imported work: the splitting theorem reaches
   `AlgebraicGeometry.exists_etale_splits_off_isolated_points`, which is still
   open in the repository. There is no `sorry` in this delivery, no new axiom,
   no forbidden declaration, no definition change, and no data definition chosen
   from an unproved existence statement. The delivery closes the item's one local
   hole; it does not certify the entire transitive proof as sorry-free.

3. **Split statements and edge cases: pass.** No new holed statement, module, or
   DAG node is introduced. Read all five helper proofs: the finite-fibre assumption
   supplies affineness and finite-dimensional sections where required; clopen
   restrictions are closed immersions; zero finite dimension makes the section
   ring subsingleton and its affine spectrum empty. Additivity is applied to the
   finite fibre, not to the possibly non-affine original map. Checked degree zero,
   empty fibres, and the vacuous empty-base case. No positivity or nonemptiness
   hypothesis is hidden in the argument.

4. **Route and pruning: pass.** Read Stacks Tag 07RY, proof, second paragraph, and
   the two imported Sheaf interfaces. The proof retains the splitting and locally
   constant degree route. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this supporting node's replacement does not bypass any realized unit step.
   Re-searched with LeanFinder for finite flat morphisms and bounded fibre length,
   with Loogle for scalar-extension dimension, and with `rg` for finite sections,
   empty degree-zero fibres, and existing maximal-degree neighbourhood results.
   No shorter applicable theorem was found. In particular the source library's
   `fiberDegree_of_isPullback` requires an affine original morphism, which is not
   available here. The five helpers use proved existing APIs instead of importing
   the holed general base-change interface. Both retained proof imports are used;
   the public imports supply the unchanged signature. The sole old DAG dependency
   removed is `lem-weil-pbc-fibre-degree-base-change`, already listed under
   `## No longer needed`; the redundant direct FiberDegree import is also listed.

5. **DAG agreement: pass.** Compared the old and new node records and read every
   proof dependency's Lean or Mathlib record. The updated four steps describe the
   actual splitting, restriction, finite-fibre calculations, complement removal,
   and final pullback transport. `proof_deps` is exactly the union of their `uses`.
   The new base-change and affine-spectrum dependency references have existing
   Mathlib records. The statement, statement dependencies, unit, and chapter are
   unchanged, and there are no new nodes requiring metadata.

Second reading changed only this report: added the five-point review and made the
axiom limitation explicit. The reviewed Lean proof and node record needed no repair.

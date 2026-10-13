## What changed

Replaced the sorry of `AlgebraicGeometry.Scheme.perfect_relativeTensor_locally_bounded`
with a compiling reduction, without changing its signature or existing visibility.
Added two proof-only imports and two new statement modules:
`Sheaf.AlgebraicGeometry.StalkTorDimensionLocallyUniform` and
`Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound`.

The Lean proof obtains the geometric neighbourhood U and bound d, extracts the
strictly perfect neighbourhood V and model L from hE, and extracts its degree
bounds r,s. It maps the given QK ≅ E through open restriction and composes the
isomorphism with the local representative. It takes U ∩ V and the ordered
interval [min (r-d) s,s], then proves the two outside-degree cases from the
pointwise stalk bound. The DAG proof and dependencies now record precisely this
argument. No definitions, target signatures, or other existing modules changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.perfect_relativeTensor_locally_bounded`
(node `lem-pc-perfect-relative-tensor-locally-bounded`). The assigned module has
no remaining sorry.

Added exactly two holes, each in a new module with its source and complete
natural-language proof:

- `AlgebraicGeometry.stalkTorDimension_locally_uniform`
  (`lem-pc-stalk-tor-dimension-locally-uniform`): geometric spreading of the
  structure-stalk Tor bound, independently of any complex or representative.
- `AlgebraicGeometry.Scheme.strictlyPerfect_relativeTensor_stalk_bound`
  (`lem-pc-strictly-perfect-relative-tensor-stalk-bound`): pointwise algebraic
  amplitude and representative comparison with an explicit [r-d,s] bound,
  assuming the local Tor bound and a specified strictly perfect model.

This is a decomposition, not an unconditional proof: one upper hole closed,
two strictly smaller lower holes added (net -1). The first lower statement has
no E, K, P or tensor homology. The second has no Noetherian, finite-type, or
perfect-morphism hypothesis and makes no claim about a uniform neighbourhood.
The neighbourhood and interval choices and the representative-isomorphism
composition are proved in the assigned module, not hidden in either hole.
All three sandbox modules compile with lcompile.py; the delivery dry run checks
the declarations with its axiom probe as well. No extra axioms or holed definitions.

## No longer needed

The main module no longer uses the direct proof dependencies
`def-pc-kflat-complex`, `def-pc-perfect-morphism`, `def-pc-quasi-iso-modules`,
`lem-pc-kflat-stalk-criterion`, `lem-pc-kflat-tensor-quasi-iso`,
`lem-pc-stalk-tensor-complex`, and `lem-weil-pbc-module-stalk-exact`; the
corresponding imports remain because the two split lemmas use those concepts
and the item statement exposes them. The split pointwise node retains the
K-flat comparison nodes, including `lem-pc-kflat-resolution`, so they were
not incorrectly deleted from the DAG. No unit statement or step is bypassed;
`dag/units/sk-thm-picard-duality.json` has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

The original plan's geometric step is substantial but names only the definition
of stalkwise finite Tor dimension. That definition alone does not supply a
uniform neighbourhood. The second step likewise has only the definition of
perfectness, not a theorem propagating the structure-stalk Tor bound to the
specified K-flat representative. The two new statements expose these gaps.
The mathematical statement itself was not changed or disputed.

Sources checked online: Stacks Tags 069C (stalkwise criterion), 0B6G (condition
(3)), 08CG (amplitude convention), 09U9 (stalk detection), 06YB (K-flat stalk
criterion), and 064L (K-flat model invariance). The local literature checkout
lacks more-morphisms.tex. The upstream more-morphisms.tex was also read to verify the labels
`lemma-check-perfect-stalks` and `lemma-perfect-proper-perfect-direct-image`.
The geometric proof follows 069C's polynomial
presentation argument; the pointwise proof expands 0B6G's finite-term argument.
The existing K-flat invariance theorem is for the one-point-site presentation,
so the new pointwise theorem explicitly retains that presentation transport
as part of its remaining proof, rather than claiming it already applies directly.

Searches were run with msearch.py and recorded in searches.jsonl. LeanSearch
was unavailable (HTTP Internal Server Error) for both statements. LeanFinder
returned finite-type/Noetherian instances for the geometric statement and
projective Tor vanishing/Ext dimension results for the algebraic one, neither
an exact match. Focused Mathlib grep found no geometric Tor-amplitude theorem;
its homology hits were generic isZero/homology functor facts. Searches of both
library roots and DAG nodes found no existing uniform structure-stalk theorem
or pointwise relative [r-d,s] theorem. The absolute O_X tensor bounds use a
different scalar ring and cannot replace the relative statement. Whole-blueprint
searches for finite tor, strictly perfect, and perfect morphism found no exact
statement. The original node's blueprint.from chain is retained for the new nodes.

Edge cases checked before stating the lemmas: an empty X has no x; flat structure
stalks allow d=0; a one-term model in degree t gives [t-d,t] with the expected
cochain sign; zero L has vanishing in every degree, including when r>s; a zero
test sheaf gives zero tensor. The pointwise lemma requires y ∈ V and the Tor
bound for every target-stalk module, not only those arising as a particular F's
stalk. In the combining proof, min (r-d) s handles all possible endpoint orders.

## New nodes

`lem-pc-stalk-tor-dimension-locally-uniform` is the geometric part of the original
first step, in `Sheaf.AlgebraicGeometry.StalkTorDimensionLocallyUniform`. Its
statement gives an open and one natural Tor bound for every stalk in that open;
its source is Stacks 069C and 09U9. It is a strictly smaller geometric statement
with no input derived complex or tensor representative.

`lem-pc-strictly-perfect-relative-tensor-stalk-bound` contains the bounded-model
and K-flat-comparison parts of the original second and third steps, in
`Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound`. The model,
its degree bounds, the point, and the structure-stalk bound are inputs; it gives
the explicit pointwise [r-d,s] vanishing, with no geometric spreading conclusion.
Its sources are 0B6G, 08CG, 09U9, 06YB, and 064L. No change record is needed:
all existing statements and definitions are unchanged.

## Second reading by B3

1. **Statements and interfaces.** I compared the delivered item module with the
repository version byte for byte above each proof body. The target signature,
visibility, definitions, and all existing declarations are unchanged. Verdict:
pass.

2. **Proof and trust.** I compiled all three sandbox modules with
`lcompile.py --all`. The item has no `sorry`, and the only remaining `sorry`s
are the two named split theorems, each with a docstring and matching DAG node.
The axiom probe reports only the standard axioms plus `sorryAx` from those open
nodes. There are no axioms, unsafe, opaque, extern, or hollow definitions.
Verdict: pass.

3. **New statements.** I checked the two split statements against Stacks Tags
069C and 0B6G and searched the repository and Mathlib for duplicates. The first
is the strictly smaller geometric uniformity result; the second is the
pointwise bounded-model comparison. Neither restates the item, weakens its
conclusion, or adds an unnecessary hypothesis. Edge cases (empty and zero
models, flat bound d=0, and unordered r,s) are covered by their stated forms.
Verdict: pass.

4. **Pruning and route.** The main proof uses the shortest available reduction:
the two split lemmas, the existing perfect-complex definition, intersection of
opens, and elementary integer inequalities. Removed direct proof dependencies
are listed above; their lower K-flat nodes remain where the pointwise split
lemma's proof requires them. No public import was removed, and no unit route is
bypassed. Verdict: pass.

5. **DAG agreement.** I checked each new node's Lean statement and verified its
`proof_deps` equal the union of the proof-step uses. The item's DAG proof and
dependencies match the Lean proof, and all node metadata, sources, and
blueprint links are present. Verdict: pass.

I changed only the item proof, the two proof-only split modules and their DAG
nodes, and this report. The second reading corrected the report's pruning entry
to distinguish removed direct dependencies from dependencies retained by the
split pointwise proof.

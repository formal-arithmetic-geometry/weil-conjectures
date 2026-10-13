## What changed

Reduced `AlgebraicGeometry.exists_finitePresentation_overlap_eventual_chart_equations`
without changing its statement. The proof applies persistent eventual equality separately
for each diagonal and each triple, chooses a common directed upper bound of the finite
families of stages, and constructs the chosen pairwise and threefold pullbacks explicitly.

Added two one-statement modules:
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually` and
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually`.
Their conclusions concern one test each and persist at every later stage, so they
can be used independently and combined by the finite upper-bound argument. The original
node now records this proof route. All proof-only imports are non-public. Three proved private helpers construct the
pullbacks and assemble the equations with abstract chart maps; the triple helper is
instantiated and its local let bindings reduced before applying it. This avoids
expensive elaboration of the concrete refinement maps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_finitePresentation_overlap_eventual_chart_equations`
(node `lem-pc-fp-overlap-eventual-chart-equations`). This is a decomposition, not an
unconditional proof: one upper hole closed and two lower holes added.

The two remaining holes added by this delivery are:

- `AlgebraicGeometry.finitePresentation_overlap_diagonal_eventually`
  (`lem-pc-fp-overlap-diagonal-eventually`), eventual identity of one chart transition.
- `AlgebraicGeometry.finitePresentation_overlap_triple_eventually`
  (`lem-pc-fp-overlap-triple-eventually`), eventual composition equality on one triple.

Each is in its own module with a source and full proof in words. The target module
has no remaining `sorry`. Neither helper constructs module data from an unproved
existence statement; the assembly chooses only proof-witness indices, while its
pullback objects are the actual categorical pullbacks.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent`
from the target module; it remains needed through the two helper modules. The target
node no longer directly depends on `lem-pc-fp-zero-map-descent`, but that node and
module are still reached by the helpers. No module is pruned from the transitive closure.
No other dependency of the old plan is discarded.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's claim that the defect argument could not be reduced is resolved
by separating one diagonal defect and one triple defect, with persistence at later
stages. The substantial transport from scheme zero-map descent to the prescribed
refinement transitions is explicitly left in these named smaller statements, rather
than hidden in the assembly proof. No existing statement or definition was changed.

The source cited by the node, `literature/stacks-project/limits.tex`, is absent on this
machine; the official Stacks Tag 01ZR page was read instead. Its clause (3) is eventual
equality of finitely presented module maps, and its first proof reduces to the affine
case and Zariski gluing. The helpers follow that same route via the project's existing
zero-map descent theorem.

Edge cases: the assembly includes k in the finite upper-bound set, so the empty cover
requires no chart or triple witness. Zero modules and empty chart schemes have zero
defects. Repeated indices are permitted in the triple statement. A singleton diagram
reduces to transport along identity-base-change comparisons. The arbitrary choices of
universal pullbacks in the triple helper are equivalent by the projection-compatible
canonical isomorphism, so the stage can be chosen independently of those choices.

## New nodes

`lem-pc-fp-overlap-diagonal-eventually` isolates the identity defect for one chart and
its persistence at later stages. It uses the existing finite-type zero-map descent
clause and transition naturality. Its Lean module is
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually`.

`lem-pc-fp-overlap-triple-eventually` isolates the composition defect for one triple
and its persistence, including transport to any chosen universal threefold overlap.
It uses the same existing zero-map clause. Its Lean module is
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually`.

Blueprint searches for overlap diagonal and overlap cocycle found no existing node
for these module-transition defects. The other overlap cocycle results found concern
Nagata gluing of schemes. Mathlib searches were recorded in `searches.jsonl`; LeanSearch
was unavailable, LeanFinder found scheme gluing statements rather than this equality,
Loogle did not know ChosenPullback, and grep found the universal-pullback structures
and descent-data transport lemmas. No change record or forced adaptation is needed.

## Second reading by P2

1. I compared the delivered target module with the repository version. The existing
   declaration signature is byte-for-byte unchanged; only its proof and proof-only imports
   changed. The two added helper modules and their node records are the only new files.
   Verdict: pass.

2. I compiled all three modules with `lcompile.py --all`. The target has no remaining
   `sorry`; the two explicitly named helper theorems retain their documented `sorry`s and
   matching split nodes. No forbidden declarations or hollow definitions occur. The target
   proof uses actual categorical pullbacks and only chooses stage indices. Verdict: pass.

3. I checked both split statements against their docstrings and node records. Each is a
   strictly smaller one-chart or one-triple eventual equality, with the same hypotheses as
   the target and no weakened target conclusion. Searches recorded in `searches.jsonl` and
   repository grep found no existing declaration duplicating either result. Verdict: pass.

4. The proof follows the stated finite-family route: persistent diagonal and triple
   lemmas, a common directed upper bound containing `k`, then explicit pairwise and
   threefold pullbacks. The target's pullback and finset imports used only by the proof are
   private imports; no unused target dependency was retained. Verdict: pass.

5. The target node proof and proof dependencies match the proof, and both new nodes have
   matching Lean declarations, sources, proof plans, and split status. The unit route remains
   realized through the target node. Verdict: pass.

I changed the target's `Mathlib.AlgebraicGeometry.Pullbacks` import from public to
proof-only, and appended this second-reading record. No statements or definitions were
changed.

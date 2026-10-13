## What changed

Decomposed the single hole in
`AlgebraicGeometry.finitePresentation_one_chart_map_lift_eventually` without
changing its signature or public imports. Its Lean proof obtains a stage and its
chart recovery assertion, chooses that same stage as the eventual bound, and
applies a persistence theorem separately at each later index.

Added `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage`, which
asserts existence only at one stage, and
`Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport`, which transports an already
supplied chart lift. The latter assumes neither finite presentation,
quasi-coherence, affine charts, directedness, affine cone vertex nor a limit
universal property. Both are proof imports. Updated the original node's proof
route and added the two corresponding nodes. The unit route is preserved:
its `realized` lists contain no binding nodes for this below-unit argument.

The final application uses reducible transparency to keep Lean from unnecessarily
unfolding the chosen pullbacks and the canonical adjunction comparisons while
comparing these large recovery statements. Disabled the unused-variable linter
only on the original theorem: once its proof is no longer `sorry`, it flags the
original statement's unused existential proof binder `hjk` and unused let-bound
functor `B`. Both binders are preserved. No statement or definition was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.finitePresentation_one_chart_map_lift_eventually` by a
compiling reduction to two strictly separate parts of its argument. This is a
decomposition, not a sorry-free proof of the mathematical result.

Two new named holes remain:

- `AlgebraicGeometry.finitePresentation_one_chart_map_lift_at_stage`
  (`lem-pc-fp-one-chart-map-lift-at-stage`): affine chart/ring identification and
  use of the algebraic map-descent clause to find one stage. It asserts no
  eventual persistence.
- `AlgebraicGeometry.openCover_map_lift_transport`
  (`lem-pc-open-cover-map-lift-transport`): transport of the supplied stage's
  recovery assertion to later stages, through the canonical restriction and
  tensor composition comparisons. It makes no assertion that such an initial
  lift exists. Its hypothesis is recovery at a specified k; its conclusion is
  recovery after each further base change.

No hole remains in the item's module. One upper hole closed, two lower holes
added; the delivery does not claim a decrease in the closure's hole count.
There are no new definitions or arbitrary witness choices in definitions.

## No longer needed

No node or module is pruned from the import closure. The direct proof import
`Sheaf.Algebra.FinitePresentationColimit` is removed from the item's module,
because the algebraic step now belongs to the one-stage lemma; that lemma still
imports it. In particular `lem-pc-fp-module-map-descent-affine` remains needed,
through the one-stage node. The canonical composition and cover comparison
modules remain public imports because the original statement uses them.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original node's single proof step combined
substantial affine chart-to-ring identifications with persistence and comparison
coherence. The ring-level theorem is available and already reduced to lower
algebraic lemmas, but does not itself supply these geometric identifications.
The new nodes expose the two parts independently, and the original module proves
how to combine them. The four transition/cone triangles and comparison-coherence
argument are described explicitly in the persistence theorem's proof docstring.

Checked edge cases: j supplies a nonempty upper tail; a supplied chart index
excludes an empty cover index set but permits an empty chart; zero sheaves are
allowed; equivalent indices of the preorder require no strict inequalities;
identity factorizations and a singleton index system are included. The transport
lemma is independent of all finiteness and limit-universality hypotheses.

LeanSearch returned an Internal Server Error on both new-statement queries.
LeanFinder and source searches found no matching geometric theorem. Existing
ordinary pullback associativity supports the transport proof plan but is not
itself the chart recovery statement. The referenced Stacks tags 01ZR, 05N7,
0095 were read online because the cited local `.tex` files are absent on this
machine. Comparison-coherence details are explicitly marked as expanded by C4.

## New nodes

`lem-pc-fp-one-chart-map-lift-at-stage` corresponds to the first-stage existence
step of the original proof, retaining its ring-colimit dependency. Its module
contains one named theorem with exactly `:= by sorry` and a proof docstring.

`lem-pc-open-cover-map-lift-transport` corresponds to functorial persistence of
an already supplied chart lift. Its module contains one named theorem with
exactly `:= by sorry` and a proof docstring explaining the over-base transition
triangles, chart refinement, conjugation and coherence argument. No change
record is needed: no existing statement, definition or public interface changed,
and there are no adaptations.

## Second reading by C4

1. **Statements and interfaces.** Compared the delivered main module against the repository version. The theorem signature and all existing declaration statements are unchanged byte for byte; the two added declarations have independent, strictly smaller interfaces. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py`. The main theorem is proved; the two explicitly named split-off theorems remain the only `sorry`s. No forbidden declarations or hollow definitions occur. The remaining holes are recorded by their DAG nodes, and the main proof uses only the split-off statements. Verdict: pass (decomposition with two lower holes).

3. **Search and truth of split statements.** Checked the new theorem names and statements against the library and search tools. No existing equivalent declaration was found. The stage theorem asserts only one-stage existence, while transport assumes a supplied lift and asserts only persistence; neither adds hypotheses to or weakens the original target. Verdict: pass.

4. **Pruning and imports.** The original proof-only `Sheaf.Algebra.FinitePresentationColimit` import is removed from the main module; it remains used by the one-stage module. The canonical comparison imports remain required by the public target signature. No proof dependency node is otherwise pruned. Verdict: pass.

5. **DAG and unit route.** The original node records the new proof route and dependencies, and both split-off nodes match their Lean declarations and docstrings. The unit's `realized` route is unchanged because these are below-unit reductions. Verdict: pass.

Changed only the main proof/imports, added the two split-off modules and matching nodes, and appended this review.

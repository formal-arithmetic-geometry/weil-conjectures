## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.iso_of_finite_depth_two_extensions`
with a compiling inverse-map construction. Its signature and existing docstring are unchanged.
The proof imports DepthTwoFiniteHomExtension and DepthTwoFiniteHomEquality privately.
The former extends arbitrary open morphisms into affine targets; the latter detects equality
of morphisms from their agreement on the source open. Neither assumes an open isomorphism,
and neither concludes a global isomorphism. Only the source has a boundary depth hypothesis.
The target applies extension twice, uses equality twice to verify both inverse identities,
and packages the resulting isomorphism with its equation over L.

Read Stacks Tags 0EY6 (converse of (2)), 0AUK, and 0E9I online. The converse uses no
etaleness or base depth hypothesis. Searched the source and statement libraries for Hartogs
and depth-two morphism interfaces. LeanFinder found restriction and section results only;
Loogle found resLE identities; Mathlib grep found no Hartogs morphism result; LeanSearch
was unavailable (HTTP 500), as recorded in searches.jsonl.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.iso_of_finite_depth_two_extensions`
(node lem-sbc-depth-two-finite-extension-uniqueness). No sorry remains in the assigned module.

Added two holes:
- `AlgebraicGeometry.Scheme.exists_hom_of_finite_depth_two`
  (lem-sbc-depth-two-finite-hom-extension).
- `AlgebraicGeometry.Scheme.hom_eq_of_finite_depth_two`
  (lem-sbc-depth-two-finite-hom-equality).

This is a decomposition, not a sorry-free proof: one upper hole is closed and two lower
holes are added. The combination proof compiles without warnings. Both helpers have exactly
`:= by sorry`, source citations, complete proof descriptions, and separate modules and nodes.
The empty-open case forces the finite source algebra to vanish by Hartogs; the full-open
case gives the supplied morphism and direct equality. Empty sources are permitted. Targets
need only be affine, not finite or depth two. Thus there is no hidden nonempty, etale, base
depth, or target depth hypothesis. No definitions or existing signatures were changed.

## No longer needed

No original import was removed: all three public imports support the existing statement.
No original dependency is globally pruned. The affine-relative-spectrum node is no longer a
direct proof dependency of this item, but remains needed in both lower nodes. The general
Hartogs module theorem is likewise recorded below, rather than imported without use by the
assigned module. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's first two non-elementary steps had no dependency nodes and no Lean
interface supplying the needed algebra Hartogs bridge. The only listed dependency was the
relative-spectrum equivalence, which does not provide the boundary depth comparison or
extension of open morphisms. The existing FiniteStructureAlgebraDepth theorem runs in the
opposite direction (algebra stalk depth implies source local-ring depth), so it cannot supply
that missing direction. Existing DepthTwoHartogsAlgebraComparison returns a module
isomorphism, without the multiplicative compatibility needed to apply relative spectrum.
The new morphism extension and equality statements isolate these gaps without replacing the
original statement by itself under a new name. They retain the same Hartogs/affine-algebra
route and leave the two genuine geometric obligations available for independent work.

## New nodes

`lem-sbc-depth-two-finite-hom-extension` records arbitrary open morphism extension from a
finite boundary-depth-two source into an affine target. It lives in DepthTwoFiniteHomExtension.

`lem-sbc-depth-two-finite-hom-equality` records equality detection on that source open,
without an extension or isomorphism conclusion. It lives in DepthTwoFiniteHomEquality.

Both share the item's chapter and unit, cite the existing Hartogs and relative-spectrum
nodes, and record the searches actually run. No change record or forced adaptation is needed.

## Second reading by J3

1. Interface: PASS. Compared the delivered original module with the repository using
   diff. The existing theorem signature and docstring are byte-for-byte unchanged;
   only two private proof imports and the proof body changed. The other two modules
   are new, with no definitions or forced adaptations. No change record is required.
2. Kernel checks: PASS for this decomposition. Compiled all three modules in import
   order with lcompile.py, without errors or warnings. Appended #print axioms for
   each of the three public theorems to temporary scratch copies: all report exactly
   propext, Classical.choice, Quot.sound and sorryAx. The assigned theorem has no
   direct sorry; the two new public theorems each have exactly := by sorry. There
   are no forbidden declarations and no data-bearing or hollow definitions. The
   existential witnesses are eliminated inside a proof, not chosen to define data.
3. Split statements: PASS. Independently read Stacks 0AUK, 0E9I, 0EY6 and 01SA.
   The finite structure algebra's depth is computed on affine base charts; Hartogs
   gives its canonical algebra restriction isomorphism. Adjunction extends arbitrary
   algebra maps and injectivity detects equality, giving the stated two helpers.
   Source depth suffices; affine targets need neither finiteness nor depth. For
   U=top the supplied morphism already extends and equality is immediate. For
   U=bottom a nonempty finite source would have a boundary point with a depth-zero
   local ring (equivalently Hartogs forces its algebra to vanish), so the source
   must be empty. Empty sources and empty targets cause no missing hypothesis.
   These are separate existence and equality steps, not an isomorphism restatement.
   Both have sourced proof docstrings and matching nodes. Repeated searches using
   different words: LeanFinder for full faithfulness of restriction on depth-two
   affine schemes, grep for schematicallyDense/open hom_ext, and Loogle for scheme
   morphisms and Epi. No replacement was found. The local upstream open-cover
   hom_ext lemmas require a cover; the algebraic Hartogs lemmas require stronger
   integral/regular/UFD hypotheses. The existing module Hartogs and affine algebra
   correspondence do not provide the source-depth/algebra-map bridge directly.
4. Route and pruning: PASS. Read the proof from its conclusion through both inverse
   identities and the two open-map extensions. Every import is needed either by
   the preserved signatures or this proof. The sole old direct proof dependency,
   lem-weil-pbc-affine-morphism-relative-spec, is explicitly accounted for under
   No longer needed and remains below both new nodes; no module is globally pruned.
   Read dag/units/sk-prop-input-spreading.json: the depth-two/Hartogs/relative-Spec
   route is retained, and its existing realized entries are unchanged. Neither
   helper can be closed in a few minutes from the available interfaces. This remains
   one hole closed, two added (a decomposition; net -1), not a complete proof.
5. DAG: PASS. Checked the existing node diff is confined to proof, proof_deps and
   proof_origin. Checked all three lean.statement strings verbatim against Lean,
   proof_deps against the union of step uses, and the new nodes' sources, searches,
   provenance, chapter, unit and blueprint ancestry. The upper node records exactly
   the extension/equality/inverse-packaging argument that compiles.

Second reading changed only this report by adding the independent checks and verdicts;
no Lean proof, statement, definition, import or node needed repair. Additional search
queries and results are recorded locally in searches.jsonl.

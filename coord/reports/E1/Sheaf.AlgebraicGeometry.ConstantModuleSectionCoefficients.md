## What changed

The unchanged theorem `AlgebraicGeometry.Etale.constantModuleSectionCoefficientEquiv_naturality`
is reduced to the one-morphism coefficient square
`AlgebraicGeometry.Etale.constantModuleTransition_coefficients`, in the new module
`Sheaf.AlgebraicGeometry.ConstantModuleTransitionCoefficients`. Its proof combines that square
with the existing, proved `constantPullbackCompositionCoherence`, unit naturality, direct-image
composition naturality, and evaluation of a sheaf-morphism equality. The two existing definitions
and every existing declaration signature are byte-for-byte unchanged. The new modules are
proof-only imports. The unused public GlobalSections import was removed; Mathlib's Sites.Adjunction
import remains needed by the exposed coefficient sheaf isomorphism construction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.constantModuleSectionCoefficientEquiv_naturality` (node
`lem-weil-pbc-constant-module-section-coefficients`). The item's module now has no sorry.
Added one hole in `AlgebraicGeometry.Etale.constantModuleTransition_coefficients` (node
`lem-weil-pbc-constant-module-transition-coefficients`). This is a decomposition: one original hole
closed, one strictly smaller hole added, net zero holes closed. The target still depends on sorryAx
through the named coefficient square. No data is chosen from an unproved theorem and no definition
contains sorry. No other holes are added. The earlier function-equality auxiliary was removed,
not counted as a closed original hole. The proposed composition helper was removed because an
existing proved theorem supplies it.

## No longer needed

Removed import `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`: none of its
specific global-section declarations is needed. No node in the old proof_deps is removed:
`lemma-constructible-pullback-constant` supplies the definition's canonical comparison,
`lem-weil-pbc-constant-module-pushforward-functoriality` supplies the transition definition, and
`lem-weil-pbc-inverse-image-composition` supplies upperStarComp and lowerStarComp. There is no claim
that GlobalSections becomes unreachable from the whole target closure; that is the maintainer's
ledger calculation. No unit-realizing module is pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's `_naturality_aux` changed pointwise equality into function equality and applied
congrFun. Function extensionality recovers it immediately from the target, so it is a restatement,
not a strictly simpler argument. Its alleged sheaf-level square was actually still the original
section expression. The first report's claim of a proved target was therefore misleading. The
replacement makes a real reduction using the DAG's coefficient and unit square, while reusing
the existing composition coherence theorem found by a broader search. The original DAG node was
not updated by the first worker; its proof now matches the actual reduction.

## New nodes

`lem-weil-pbc-constant-module-transition-coefficients` is a one-morphism sheaf coefficient square:
no base morphism f, no composite h, no composition comparison, no etale section object U, and no
section coefficient equivalence. It has a complete generator/universal-property proof in its
docstring and DAG steps, actual recorded Mathlib searches, and its own Lean module. It is needed
together with the independent, existing composition theorem. The public import removal is recorded in
`coord/changes/constantModuleSectionCoefficientsImports.md`; no existing statement or definition
changes. The sole direct importer already publicly imports GlobalSections independently and
compiles unchanged against the sandbox overlay.

## Second reading by E1

1. Compared every delivered existing declaration with the repository using diff and the declaration
   parser, checking the raw signatures and both definition bodies. Verdict: all existing signatures
   and definitions unchanged; only the target proof, imports and its proof metadata change.
2. Compiled all delivered modules in import order through lcompile.py. Verdict: no errors or
   warnings. Inspected every sorry and searched for forbidden declarations and attributes. The sole
   remaining hole is the public named coefficient-square theorem. A scratch #print axioms check
   shows only propext, Classical.choice and Quot.sound for both coefficient definitions, and those
   plus sorryAx for the target and the new open theorem. No hollow or arbitrary-witness definitions.
3. Verdict: rejected and removed the first auxiliary as equivalent to the target. Checked the
   replacement on zero coefficients, empty schemes and identity morphisms: both sides preserve
   equal-valued constant generators, with no nonemptiness or invertibility assumption on g.
   The hypotheses on preserving sheafification are supplied in the main proof using the explicit
   left-adjoint forgetful functor. Searches through msearch.py (LeanFinder, Loogle, Mathlib grep,
   and unavailable LeanSearch), project/source rg searches and whole-blueprint searches found
   building blocks but no existing one-morphism coefficient square. The composition search found
   constantPullbackCompositionCoherence, which is used instead of adding a duplicate.
4. Verdict: the target is reduced from the top downward by the coefficient square, proved
   composition coherence, and elementary categorical naturality. Removed the unused GlobalSections
   import. All old proof_deps remain used and are accounted for above. Inspected sk-thm-p1.realized:
   this item is below the unit's realized steps, and no unit statement, step or route is bypassed.
5. Verdict: the original node's proof, proof_deps union and proof_origin now follow the Lean proof.
   The new node records its exact Lean signature, source, full proof, statement dependencies,
   actual searches, creation/provenance and chapter/unit. It has no dependency on the target node,
   so the reduction is not circular. The unit record is unchanged.

Second reading changed: removed the equivalent function-equality auxiliary and its node; wrote
and compiled a real reduction with one strictly smaller coefficient-square hole; reused the
existing proved composition theorem; pruned GlobalSections; corrected the target DAG proof and
rewrote the report to state the net-zero decomposition honestly.

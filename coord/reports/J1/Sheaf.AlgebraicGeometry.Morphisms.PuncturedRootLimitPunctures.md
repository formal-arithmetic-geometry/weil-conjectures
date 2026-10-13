## What changed

Proved `AlgebraicGeometry.Scheme.punctured_root_colimit_continuity` with its existing signature.
The proof applies Spec to the original ring colimit, lifts the limiting cone to schemes over
Spec R, and pulls back the fixed punctured root chart over R. Mathlib proves preservation
of limits by pullback and of connected limits by the over-category forgetful functor.
The proof constructs the natural base maps, proves affine stages, and checks both leg equations.

Added `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootBaseChange`, with the fully proved
public theorem `AlgebraicGeometry.Scheme.punctured_root_base_change`. Its private
`root_pushout` proves the polynomial-root algebra pushout using `AdjoinRoot.lift`:
coefficient/root calculations give both factorization and uniqueness. The public proof takes
Spec, identifies the inverse image of the basic open, and pastes pullback squares.
This replaces the planned filtered-colimit calculation of localized root algebras with
single-base-change algebra and general categorical limit preservation.

Added proof-only imports of this helper, `Mathlib.CategoryTheory.Comma.Over.Pullback`,
and `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`. All original public
imports and all existing signatures and visibility are preserved. Updated the original
node's proof, proof dependencies and proof origin to follow the Lean argument.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.punctured_root_colimit_continuity`
(node `lem-sbc-punctured-root-colimit-continuity`). No holes added or split off.
Both the new public `AlgebraicGeometry.Scheme.punctured_root_base_change`
(node `lem-sbc-punctured-root-base-change`) and private `root_pushout` are fully proved.
No `sorry` remains anywhere in the delivered Lean files; this is a proof, not a decomposition.

The proofs require no positivity, regularity, injectivity, or nontriviality assumption.
For n=0 the root relation is 1-f. For f=0 the basic opens are empty. Zero rings and
noninjective ring maps are covered by the same pushout and restriction universal properties.

## No longer needed

No existing imports, nodes, or modules were removed. All original proof dependencies
remain used: the ring-colimit universal property, affine spectrum, and Spec's preservation
of the opposite colimit cone. The separate localized-root filtered-colimit computation
formerly planned in step 1 is unnecessary; it had no separate node or module to prune.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's original proof was valid but longer than necessary:
base change of the fixed chart and preservation of connected limits avoid reconstructing
a filtered colimit of localized root rings. The original node marked that reconstruction
as elementary despite its substantial formalization cost.

## New nodes

`lem-sbc-punctured-root-base-change`, in the original chapter and unit, records the fully
proved single-ring-map comparison. It has no limit or filteredness hypotheses and is
strictly a local part of the original argument. The source is the polynomial-quotient
universal-property calculation in the parent node and the corresponding Mathlib root,
Spec, and restriction declarations. Three kinds of Mathlib search were attempted;
LeanSearch returned an Internal Server Error, while LeanFinder and source grep found
only general tools. No change records or forced adaptations are needed.

## Second reading by J1

1. Compared the existing module and node with the read-only repository. The existing
   theorem signature is byte-for-byte identical, including its universe and hypotheses;
   no existing definition or visibility changed. The only new public declaration is the
   fully proved base-change helper in its own module. Verdict: pass.
2. Compiled both delivered modules through lcompile.py in import order, without errors
   or warnings. Printed axioms of both public theorems: exactly propext, Classical.choice,
   and Quot.sound. Checked both files for forbidden declarations and sorry: none.
   Read the root pushout's lift, factorization and uniqueness proofs, the restriction
   pullback pasting, and the limiting over-category cone construction. Verdict: pass.
3. No statements were split off with sorry. The new helper is strictly the single-map
   base-change step, with no indexing diagram or colimit hypotheses. Its docstring and
   node describe its actual proof. Checked n=0 (relation 1-f), f=0 (empty opens),
   zero rings, and noninjective maps against the universal-property argument. Independent
   Loogle search for AdjoinRoot.map and source searches of the project found only general
   root-map and localization tools, not this chart comparison. Verdict: pass.
4. The proof takes Spec of the supplied colimit, then uses Mathlib pullback preservation
   and connected-limit preservation of Over.forget. The original dependencies are Mathlib
   leaves actually used by these constructions. Read sk-prop-input-spreading's statement,
   steps and realized arrays; this changes only a local tool below the unit's route.
   Removed the redundant direct AffineScheme import from the new helper, since its
   necessary public Pullbacks import already publicly imports AffineScheme. All added
   imports in the existing module are proof-only. No old dependency node or module is
   pruned. Verdict: pass after the import cleanup.
5. Checked the old node's changed fields and the new node's statement, steps, dependency
   union, source, searches, provenance, blueprint ancestry and Lean record against the
   two modules. Spec.reflective is the Mathlib match of the retained Spec-limit node,
   and the colimit and spectrum definition nodes match the constructions used. Verdict:
   pass. No statement or definition correction and no change record is needed.

Second reading changed only the redundant import in the new helper and this report.
Recompiled the helper after that removal. Holes closed: punctured_root_colimit_continuity;
holes added: none. No mathematical proof repair was necessary.

## What changed

Proved `AlgebraicGeometry.Scheme.exists_supported_overlap_restriction_data` in
`Sheaf.AlgebraicGeometry.SupportedOverlapRestrictionData` without changing its signature.
The compact open is explicitly `V.ι ⁻¹ᵁ W`, and G is exact restriction along
`V.ι ∣_ W`. Added proof-only imports of `DerivedOpenLocalization` and
`DerivedPullbackPerfect`, plus the Mathlib pointwise-left-derived API. Two proved private helpers transport a localization across
an abelian equivalence and construct the module equivalence of a scheme isomorphism.
Their constructions follow the existing private helpers in
`PerfectRestrictionClassesSmall` and `SchemeIsoDerivedLocalizations`; neither module
is imported. Updated the existing DAG node to record the actual proof.

Perfectness follows by identifying exact restriction with derived pullback and using
`derivedPullback_preserve_perfect`. Support follows from exact homology and the
Mathlib restriction-stalk isomorphism. Both overlap comparisons are built from
underived natural isomorphisms and then derived. Biproduct and shift comparisons
complete the stabilized-object isomorphism. Empty opens, W or V equal to the whole
scheme, T empty or total, and F zero require no additional hypotheses or choices.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_supported_overlap_restriction_data`
(node `lem-sc-supported-overlap-restriction-data`).

No holes remain in the delivered module; no holes or nodes were added.
This is a proof from existing declarations, not a decomposition. Its dependencies
may themselves reach existing sorries; no claim of global axiom closure is made.
The full module compiles locally; the delivery dry run checks the axiom probe.

## No longer needed

No original imports, nodes, or modules were removed: all original public imports
are required by the unchanged statement. All three added proof-only imports are
used: the Mathlib pointwise-left-derived import supplies
`Functor.isLeftDerivedFunctor_of_inverts`.

No separate new nodes for perfect restriction, stalk support, localization
transport, overlap equivalence, or shift/biproduct compatibility are needed.
The existing `PerfectRestrictionClassesSmall`, `SchemeIsoDerivedLocalizations`,
and `SchemeIsoDerivedRestrictionSquare` modules need not be imported by this proof;
this does not assert they become unreachable from the other targets.

## Where the brief, the DAG or earlier work was wrong

The original DAG listed only definitions as proof dependencies and described the
categorical transport in one broad step. The delivery realizes that argument and
records its actual uses of the existing derived-open localization and
derived-pullback preservation theorems. No statement dispute or interface correction
was necessary, and the unit route is preserved.

## Second reading by W4

1. Compared the delivered Lean module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof-only imports,
   private helpers, and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. Searched the
   delivered file for forbidden `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and
   `implemented_by`; none occur. The sole original theorem is proved and no holes
   were added. Verdict: pass.
3. Checked the proof against the node and searched the library for the principal
   constructions used. The node statement is unchanged, no split-off statement was
   introduced, and the proof uses existing declarations and Mathlib APIs. Verdict:
   pass.
4. The proof follows the compact-overlap, exact restriction, derived pullback, stalk
   support, and derived equivalence route. The added imports are proof-only and all
   are used; no old proof dependency is removed. The unit record is unchanged;
   its currently empty `realized` entries are not bypassed by this reduction.
   Verdict: pass.
5. The DAG proof steps, dependencies, origin, and Lean declaration match the proof
   and imports in the delivered module. Verdict: pass.

Changed only this second-reading report; no Lean statements, definitions, or DAG
interfaces required repair.

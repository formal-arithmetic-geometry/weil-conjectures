## What changed

The existing theorem AlgebraicGeometry.pinned_single_base_change_shift now has a complete
Lean proof. Its signature, visibility and three definitions are unchanged. Two proof-only
imports introduce shift-compatible base-change and tensor comparisons. The proof composes
morphisms of SingleFunctors families, postcomposes with H, checks the actual components,
then cancels the inverse degree-n shift isomorphisms.

New modules PinnedPullbackCounitShifts, PinnedBaseChangeMateShifts and
PinnedSingleTensorShifts isolate the steps of the original argument. The first is proved
using the existing RightKanExtensionCoherentShift theorem. The last is proved by generic
precomposition, postcomposition and mapped-single family comparisons.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.pinned_single_base_change_shift
(lem-pc-pinned-single-base-change-shift). This is a decomposition, not a sorry-free target
proof: the selected comparison maps still depend on lower unresolved statements.

Proved AlgebraicGeometry.exists_pinned_pullback_counit_shifts
(lem-pc-pinned-pullback-counit-shifts) from the existing generic right Kan shift theorem.

Added holes:

- AlgebraicGeometry.exists_pinned_base_change_mate_shifts
  (lem-pc-pinned-base-change-mate-shifts).

Proved AlgebraicGeometry.exists_pinned_single_tensor_shifts
(lem-pc-pinned-single-tensor-shifts), including the termwise and homotopy comparison
isomorphisms and their actual component identities.

No sorry remains inside the item's proof or any definition. The remaining statement
is a strict part of the argument: it concerns the base-change mate on arbitrary
derived objects before the tensor counit, singles, or H.
The separate tensor-counit step is now proved.

## No longer needed

No original imports or DAG dependency modules can be pruned globally: the original public
import SchemeDerivedBaseChangeMap supplies all three definitions and their pinned data.
The old direct proof dependencies def-pc-derived-category,
lem-pc-ringed-spaces-derived-pullback-composition and def-pc-derived-base-change-map are
replaced in the item node by the three intermediate nodes, but remain transitively needed
for their statements and proofs. Thus these nodes and modules are not globally pruned. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's named dependencies supply the chosen counits and composition comparisons, but
none states shift compatibility of the pinned base-change mate. That is now a separate,
precise theorem with its full natural-language argument. The selected pullback does not
have a globally installed CommShift instance; moreover an arbitrary instance would not
ensure compatibility with the chosen counit. The proof explicitly obtains compatible
structures from its right Kan universal property.

The new statements were checked on zero and negative shifts and on identity morphisms.
The generic family calculations hold for any integer k+i=j. No flatness, properness,
quasi-coherence, boundedness or cartesianness is added. All source constructions follow
Stacks Tags 08HY and 0D5S. Shift verification details are written by N1. The generic
RightKanExtensionCoherentShift node is used as a tool, not as a replacement of a unit route.
The unit record has no realized statement or steps assigned to this item.

## New nodes

lem-pc-pinned-pullback-counit-shifts records the proved specialization of coherent right
Kan shifts to the selected pullback counit. Its module is PinnedPullbackCounitShifts.

lem-pc-pinned-base-change-mate-shifts records naturality and shift compatibility of the
base-change mate on derived objects. Its module is PinnedBaseChangeMateShifts.

lem-pc-pinned-single-tensor-shifts records the family morphism obtained from the selected
counit and the actual mapped-single identification. Its module is PinnedSingleTensorShifts.

## Second reading by N1

1. **Visible declarations and statements.** Compared the delivered item module with the repository version. Existing definitions and theorem signatures are byte-for-byte unchanged; only proof-only imports and the proof body changed. The three added modules contain the split statements recorded by their nodes. Verdict: pass.

2. **Proof and trust basis.** Compiled all four modules with `lcompile.py --all`; compilation is clean. The only remaining `sorry` is the named theorem `AlgebraicGeometry.exists_pinned_base_change_mate_shifts`, and it has a matching node and complete proof docstring. No definitions contain `sorry`, and no forbidden declarations occur. The delivery tool's all-declaration axiom probes and preflight pass, with only standard axioms and the explicitly tracked `sorryAx` dependencies. Verdict: pass, with that explicit split hole remaining.

3. **Truth and strength of split statements.** The pullback counit shift theorem is an exact specialization of `rightKanExtension_coherentShift`; the tensor theorem states the explicit family morphism and component equality; the base-change mate theorem states precisely the missing shift-compatible natural transformation before singles and tensor counit. These are strictly smaller than the item and add no geometric hypotheses. Zero, negative, and identity shifts are covered by the integer `CommShift` laws. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing generic right-Kan coherent-shift theorem and the existing mapped-single constructions. No original dependency module can be removed. Moved the triangulated right-derived public import from the pullback-counit module to the mate module, whose statement needs the direct-image shift instance; a compile without public visibility fails instance synthesis. The unit record has no realized statement or step for this item, so its route is unaffected. Verdict: pass.

5. **DAG agreement.** The three new node files match their Lean declarations, proof dependencies, sources, and split status; the item node records the actual three intermediate declarations used by the proof. Verdict: pass.

Changed during second reading: moved the triangulated right-derived public import to the module whose statement actually needs its instances, removed a stray extra space in the theorem proof delimiter, replaced the new nodes' compressed Lean statement fields with the exact multiline signatures, recorded independent searches, clarified the old direct dependencies retained transitively, and added this review section.

The independent searches found Mathlib `Adjunction.CommShift` and its unit/counit laws,
but these require compatibility of the selected adjunction first. The upstream étale
`Etale.commShift_baseChange` applies to a different (bounded-below étale) construction,
not the unbounded ringed-space tensor pullback here. No duplicate of the split was found.

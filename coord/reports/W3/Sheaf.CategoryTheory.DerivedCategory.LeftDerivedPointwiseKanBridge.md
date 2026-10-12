## What changed

Proved CategoryTheory.leftDerived_defined_pointwiseKan_bridge without changing its
signature. Added a private, fully constructed denominator-to-structured-arrow functor
and a private proved fraction-leg independence lemma. Constructed the structured-arrow
cone using Mathlib right fractions, proved naturality by common refinement, and proved
its universal property by restricting cones to denominators. The supplied cone legs
and the identity-denominator comparison are preserved. Updated the existing DAG node
to this direct fraction route; no unit statement or step is bypassed (the unit's
realized statement and steps lists are empty).

## Proved and sorry left

Closed the sole original hole:
CategoryTheory.leftDerived_defined_pointwiseKan_bridge
(node lem-pur-left-derived-defined-pointwise-kan-bridge).
No sorry remains in the module; no holes or nodes were added. The two private helpers
are proved. Mathlib fraction representation and common refinement are sorry-free;
there is no dependency on the holed Hom-colimit theorem. Choosing a representing
fraction is legitimate here because the represented localized map is fixed and the
proved independence lemma shows equality of every downstream cone leg.

## No longer needed

Removed the proof import Sheaf.CategoryTheory.RightLocalizationHomColimit and its
node lem-pc-right-localization-hom-colimit from this node's proof dependencies.
The colimit-of-sets bijection and comma-category connectedness argument are unnecessary
for this proof: their representation/refinement ingredients are used directly from
Mathlib. Kept all public imports because they support the existing statement.
No claim is made that the removed module is globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The previous route used more machinery than needed:
the direct cone construction replaces the Hom-colimit and initiality detour while
retaining the denominator-limit argument and both specified leg equations.
Searches: LeanFinder found Localization.exists_rightFraction; Loogle for
Functor.Initial returned unknown identifier; the launcher grep found Mathlib's
isLimitExtendConeEquiv and fraction lemmas. Direct rg and signature inspection
confirmed RightFraction.map_eq_iff and the two existing Mathlib-leaf DAG nodes.
The original declaration docstring described the earlier initiality route; the
second reader updated it to the implemented direct universal-property proof.


## Second reading by W3

1. Compared the sole delivered Lean module with the repository version. The existing
   theorem signature is byte for byte identical, including all category universes,
   right-calculus and localization assumptions, the supplied witness criterion, the
   pointwise Kan-extension conclusion, and both specified leg equations. There are no
   changed existing definitions or change records. The two added helpers are private;
   the denominator functor is constructed, not obtained from an unproved existence
   theorem. Verdict: pass.

2. Compiled the module locally using lcompile.py without errors or warnings. Compiled
   a scratch copy with #print axioms for the bridge and both private helpers: all three
   list exactly propext, Classical.choice and Quot.sound, with no sorryAx. Read the
   fraction-independence argument, naturality, denominator limit fac/uniq, and the
   structured-arrow limit fac/uniq. No sorry, axiom, unsafe, opaque, implemented_by,
   extern, or hollow definition occurs. The chosen fraction comes from a proved
   Mathlib theorem; the constructed leg is proved independent of that choice.
   Verdict: pass.

3. No statements were split off, no holes were added, and no new nodes are required.
   Read Mathlib RightFractionRel (lines 895–898), exists_rightFraction (963–969), and
   RightFraction.map_eq_iff (973–979). The common denominator, rather than each
   refinement arrow separately, belongs to W; the helper correctly uses exactly this
   condition. Identity denominators recover the supplied legs. Empty-category cases
   are excluded by X; the witness supplies j₀ and the retraction needed for uniqueness.
   Verdict: pass.

4. Searched again with the launcher grep query “essentially constant|EssentiallyConstant|
   denominator.*limit|right.*fraction.*cone” (one irrelevant Mathlib homology hit),
   and rg in Mathlib, the upstream library and lean/Sheaf for essentially-constant
   diagrams, denominator limits, fraction cones and retract limits. No existing bridge
   or shorter applicable theorem was found. The direct construction avoids proving
   initiality or importing a holed Hom-colimit theorem. All four remaining public
   imports support types in the unchanged signature. The sole old unused dependency,
   lem-pc-right-localization-hom-colimit, and its module are listed under No longer
   needed. Read dag/units/sk-def-sf-operations.json: realized.statement and
   realized.steps are both empty; no unit route is bypassed. Verdict: pass.

5. Compared the delivered node with the repository node: only proof, proof_deps and
   proof_origin differ. The union of step uses is exactly proof_deps. The two fraction
   dependencies are existing Mathlib leaves naming the declarations actually applied;
   the explicit witness limit argument matches the essential-constancy definition.
   The source and proof route agree with the code, and no statement metadata changed.
   Verdict: pass.

Changed only the existing theorem's proof docstring to describe the implemented
fraction construction and direct universal property, replacing its stale Hom-colimit
and initiality account. No proof, signature, definition, import, or node repair was
needed. Holes closed: CategoryTheory.leftDerived_defined_pointwiseKan_bridge (1).
Holes added: none (0). This is a proof, not a decomposition.

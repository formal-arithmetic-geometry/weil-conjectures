## What changed

Proved `AlgebraicGeometry.schemeOpenModuleImageComplexComparison_restriction`
without changing its statement or visibility. Its proof uses fully faithful open
pushforward to cancel the localized larger-open unit after smaller-open restriction,
then the existing comparison/unit and underived unit/restriction theorems.
The only added proof import is
`Sheaf.AlgebraicGeometry.OpenImageComplexComparisonUnit`.
The DAG records this unit-cancellation route.

Repair of the returned duplicate-theorem finding: deleted the local
`AlgebraicGeometry.unit_comp_mate`. The existing identically stated theorem in
`KInjectiveMayerVietorisData` is private, so importing its module does not make it
available by name. The final proof now applies Mathlib's
`Adjunction.homEquiv_naturality_left` and `Adjunction.homEquiv_id` directly.
The new proved private `transported_left_triangle` only states the intervening
triangle calculation for one adjunction; it has no second adjunction or mate
and is strictly smaller than the removed theorem. No other module or interface
was changed. Updated the first DAG proof step to match this calculation.
The prior second reading concerned the returned version; a new reading is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.schemeOpenModuleImageComplexComparison_restriction`
(node `lem-pc-open-image-complex-comparison-restriction`).

No `sorry` remains in this module, and no holes or nodes were added.
All five remaining private helpers are proved: `transported_left_triangle`, `isIso_smaller_restriction_unit`,
`isIso_exact_localized_map`, `isIso_smaller_derived_unit`, and
`cancel_into_right_adjoint` (all in namespace `AlgebraicGeometry`).
This is a proof, not a decomposition. The repaired single-file compilation
via `lcompile.py` passed without warnings in 14.7 seconds.
The theorem retains all original hypotheses and universes. No nonempty-open,
strict-inclusion, covering, or termwise injectivity hypothesis is used;
W=U with different supplied adjunctions and empty W are allowed.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` and
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData`.
Both remain genuine dependencies through the unchanged public comparison import,
with nodes `def-pc-derived-open-restriction-maps` and
`def-pc-kinjective-mayer-vietoris-data`. No transitive module is pruned.
The old proof dependency `def-pc-open-image-complex-comparison-iso` is no longer
a proof step: the public `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonIso`
import remains needed by the statement; its construction is not unfolded in the proof.
The proof-only `OpenImageComplexComparisonUnit` import is used.

The duplicate generic `unit_comp_mate` declaration is no longer present.
The old plan's localized derived-counit calculations, localization of the
nested comparison, and rightAdjointUniq normalization are not needed.
No original proof-dependency module is globally unnecessary. No unit-level
route is bypassed: the unit record's realized statement and steps are empty,
and this Mayer--Vietoris restriction comparison itself is proved.

## Where the brief, the DAG or earlier work was wrong

The previous delivery and its second reading overlooked the duplicate-statement
landing check: the private helper repeated `unit_comp_mate` verbatim from
`KInjectiveMayerVietorisData`. The repair removes that statement entirely,
rather than merely renaming it, and uses the accessible Mathlib adjunction
identities directly with a smaller one-adjunction triangle calculation.

The original DAG plan was longer than necessary: the existing proved theorem
`schemeOpenModuleImageComplexComparison_unit`, together with invertibility
from fully faithful open pushforward, suffices by cancellation.
No statement or source error was found. The existing theorem docstring
retains the original plan; the updated DAG records the actual proof.

The earlier session's searches (recorded in searches.jsonl) found generic
derived-unit/counit factorization lemmas and rightAdjointUniq identities;
local searches found the comparison/unit theorem and fully faithful instances.
For this repair, local `rg` searches inspected the private duplicate, the
restriction definitions, and Mathlib's adjunction naturality, unit, triangle,
and mates lemmas. No accessible public replacement for the private generic
mate theorem was found. No new nodes were created.

## Second reading by C3

1. **Unchanged interface — pass.** Compared the only delivered module with the
   repository using `diff`; the existing public theorem signature is byte for
   byte identical, including universes, hypotheses, conclusion, and visibility.
   The only public import is unchanged. No definition or other module is changed,
   and no interface change record is required.
2. **Kernel proof — pass.** Independently compiled the module through
   `lcompile.py`. Regenerated the stale scratch axiom probe from the current
   repaired source, then compiled it. After the second-reader simplification,
   all five private helpers and the public theorem report exactly `propext`,
   `Classical.choice`, and `Quot.sound`; none uses `sorryAx`. No `sorry`, forbidden
   declaration, or hollow definition occurs in the delivered module.
3. **Split statements and duplicates — pass after repair.** There are no split
   statements, new nodes, or added holes. Checked the private helpers against
   Lean sources and Mathlib. The earlier `unit_comp_mate` duplicate is absent;
   `transported_left_triangle` is only the one-adjunction triangle calculation.
   Found that `isIso_map_of_natIso` specializes Mathlib's `NatIso.isIso_map_iff`;
   removed this helper and used the Mathlib theorem at both call sites.
   The argument permits empty W and W=U, arbitrary complexes where each helper
   claims them, and distinct supplied adjunctions. No stronger hypothesis is
   needed for cancellation: only the displayed left-adjoint image is epi.
4. **Shortest route, imports, and unit route — pass.** Read the comparison/unit
   proof, underived unit/restriction theorem, concrete derived mate definition,
   and Mathlib adjunction identities. The cancellation route avoids recomputing
   the comparison and needs both remaining imports; the new unit import is
   proof-only. The removed direct imports remain transitively necessary. The old
   proof dependency `def-pc-open-image-complex-comparison-iso` is no longer a
   proof step, but its module remains needed for the theorem's statement;
   the report now names this explicitly. The unit `sk-thm-picard-duality` has
   `realized = {statement: [], steps: [[]]}`; no realized unit step is bypassed.
   No transitive module is pruned.
5. **DAG agreement — pass.** JSON comparison finds only `proof`, `proof_deps`,
   and `proof_origin` changed. The dependency list equals the union of the
   proof steps' `uses`: derived restriction maps, underived Mayer--Vietoris
   data, and comparison/unit. The steps describe the actual cancellation,
   degreewise invertibility, unit compatibility, and transported triangle.
   Updated the invertibility step and proof-origin note to name the Mathlib
   replacement. No node statement or Lean record changed.

Second reading changed only the redundant natural-isomorphism helper and its
call sites, the DAG description of that calculation, and the report's helper
count and explicit old-dependency accounting. Refreshed the scratch axiom probe.
The final proof closes one original hole and adds zero holes.

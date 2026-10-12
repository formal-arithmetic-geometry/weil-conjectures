## What changed

Proved `AlgebraicGeometry.stein_universally_closed_factor` in
`Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`, preserving its entire signature
and all public imports. Added only the proof import `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
The proof establishes the morphism properties, the canonical sharp isomorphism on a
basic-open basis, and the flat-base-changed sharp isomorphism on an affine-open basis.
The latter uses Mathlib's section-ring pushout comparison directly. Updated the node's
proof, proof dependencies, and proof origin to describe the actual route; updated the
proof docstring accordingly. No definitions, interfaces, or other modules changed.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.stein_universally_closed_factor`
(node `lem-weil-pbc-stein-universally-closed-factor`). No holes added; no `sorry` remains
in the delivery. This is a complete proof, not a decomposition. All proof dependencies
are Mathlib or the already proved Stein composite identity in the source library.
Local compilation passed without warnings. The delivery dry run performs the declaration
axiom probe as well.

## No longer needed

Removed these three proof imports:

- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
  (`lem-weil-pbc-stein-flat-base-change-global-sections`).
- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
  (`pqf-lem-pushforward-qcoh`).
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
  (`lem-weil-pbc-relative-spec-base-change`).

Also removed the following planned proof dependencies from this node:
`lem-weil-pbc-relative-normalization`,
`lem-weil-pbc-universally-closed-global-sections-integral`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-qc-scheme-vanishing-section-nilpotent`.
Surjectivity uses Mathlib's dominant-toSpecΓ instance and closed-range criterion;
integrality follows from universal closedness and affineness of the second map;
the sharp isomorphism follows directly from the qcqs localization instance.
There is no relative-spectrum construction to perform for the theorem's already fixed
canonical factorization. The node is not a unit realization in `sk-thm-p1.json`, and
no unit statement or unit proof step has been bypassed. These dependencies are pruned
from this item's route; other users may still need them. Public imports are retained
because they belong to the unchanged statement interface.

## Where the brief, the DAG or earlier work was wrong

The planned `Scheme.Hom.globalSections_flat_base_change` assumes `IsProper f`, whereas
this theorem assumes only universal closedness and quasi-separatedness. It cannot be
applied here. Mathlib already proves general qcqs flat base change in degree zero:
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` (Flat.lean:457), recorded by the
existing node `lem-weil-pbc-flat-base-change-global-sections-qcqs`.
Mathlib also already has the qcqs basic-open sharp isomorphism. Thus no new node or
unfinished intermediate theorem is needed.

Sources checked: Stacks `lemma-stein-universally-closed` (03GY) and
`lemma-flat-base-change-cohomology` (02KH), read from the available local Stacks mirror.
The flat-base-change argument covers arbitrary B-prime and T by taking an affine-open
basis of B-prime, rather than assuming either entire scheme affine. Empty schemes and
the zero ring require no additional hypothesis; all constructions and basis criteria
used apply to them.

## Second reading by F2

1. **Unchanged interface — pass.** Diffed the only delivered Lean module against the
   repository. The entire theorem signature is byte for byte identical; no definition,
   declaration visibility, or public import changed. The changes are its proof, its
   explanatory proof text, and private proof imports. No change record is required.
2. **Proof and axioms — pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings. Scanned for forbidden declarations and proof escapes;
   there are none, and no `sorry` remains. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.stein_universally_closed_factor`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The canonical
   intermediate scheme is the existing concrete `Spec Γ(X, ⊤)` construction; no
   arbitrary data is chosen from an unfinished existence theorem.
3. **Split statements — pass (none).** There are no new statements, new nodes, or
   split-off holes. Read the actual Mathlib qcqs basic-open localization instance,
   dominant-toSpecΓ instance, separated postcomposition lemma, and flat pushout-section
   theorem. The arguments also apply to empty schemes and the zero ring: no nonempty,
   nontrivial, finite-type, or properness hypothesis is smuggled in. The second Cartesian
   square uses the flat map `b` obtained from the first square; every affine open of
   arbitrary `B'` is covered by the comparison.
4. **Shortest route, imports, pruning, unit — pass.** Searched the source library with
   `rg` and Mathlib through `msearch.py` using the canonical spectrum map, adjunction
   unit, and separated composition terminology. Existing field-specific upstream
   base-change lemmas require a field and do not replace this ring-general proof.
   Mathlib supplies the needed general comparisons directly. The added private Proper
   import supplies `UniversallyClosed.of_comp_of_isSeparated`; each retained public
   import supports the existing interface. All seven removed old proof dependencies
   are listed under No longer needed, including the three removed proof imports.
   Read `dag/units/sk-thm-p1.json`: this item and the removed tool nodes do not realize
   a fixed unit statement or step, and no unit route was bypassed.
5. **Node agreement — pass.** Diffed the node and checked that only `proof`,
   `proof_deps`, and `proof_origin` changed. Its statement and Lean record are unchanged.
   The dependency list is exactly the union of the steps' uses; its Mathlib leaf
   records match the permanence, surjective descent, flat comparison, and sheaf-basis
   results used. The proof origin describes the implemented route.

Second reading changed only this report by adding the independent review and explicit
axiom-check result. No Lean or node repair was needed. Holes closed: one, by
`AlgebraicGeometry.stein_universally_closed_factor`; holes added: zero.

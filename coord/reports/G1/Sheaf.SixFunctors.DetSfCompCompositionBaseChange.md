## What changed

`Sheaf.SixFunctors.DetSfCompCompositionBaseChange` now constructs the normalized open
exchange as the inverse of the specified arrow, proves both localizing-target assertions,
extends proper exchange from generators with the existing localizing extension theorem,
and proves the comparison equation by three applications of common dense refinement and
cancellation of a normalized refinement component. No target or theorem signature changes.

The open-exchange proof uses the already proved cartesian derived counit from
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` and
the proved open-unit theorem. Pullback preservation uses the generic proved helpers in
`UnboundedLocalizingPullback`, so it does not incorrectly restrict to literal coefficient
representatives. `ProperLocalizingAdmissibleCoefficients` supplies proper preservation for
all seven coefficient classes.

Two genuinely separate results are stated with their own modules and nodes: proper exchange
only on bounded constructible finite-Tor generators, and the local equation involving one
refinement before pullback and one further dense refinement after pullback. The generator
lemma accepts any chosen Cartesian square, so its map is the actual ambient mate with no
presentation conversion. The refinement lemma is an equality of actual maps, makes no proper-exchange invertibility assertion, and quantifies
no compactification-comparison family. Neither restates the item. The final common-refinement
and cancellation argument is written in the item itself. The localizing clause and
categorical cancellation are private proved helpers in the same file. Explicit component arguments avoid expanding full-subcategory lifts during inference;
no file split is used to evade a compile limit.

The seven existing helper definitions move to
`Sheaf.SixFunctors.DetSfCompBaseChangeDefs`, publicly reexported by the item, to avoid an
import cycle in the refinement statement. The exchange composite uses a generic directly constructed data structure containing its map,
component formula and component-isomorphism proof. Its map is the same two whiskered arrows;
the generic private associator equality identifies it with the original formula. No data is
chosen from a theorem. The compact-support abbreviation becomes a definition with the same body, avoiding eager
reduction of its derived composite. Pullback and proper exchange retain their original
abbreviation status; the literal proper square is a shared explicit construction. These interface changes
address measured kernel conversion timeouts. No mathematical map or signature changes. The complete proof also passed the compiler
in the diagnostic batch; its profiling-only warnings are absent from the delivery files.
The shared module is required by the refinement statement. It also exposes proved
common-refinement normalization and invertibility APIs for the canonical comparison.
The complete old/new blocks and consumer checks are in
`coord/changes/det-sf-comp-base-change-interface.md`. No source-library files are changed.

## Proved and sorry left

The original item had one hole, in
`AlgebraicGeometry.ProEtale.CondensedRing.det_sf_comp_composition_base_change`.
Its proof is replaced by an assembly from the named inputs. The item has zero
remaining `sorry`s; all seven definitions have zero holes.

Two holes are added, so this packet is a decomposition, not a net hole reduction:

- `AlgebraicGeometry.ProEtale.CondensedRing.properBaseChange_admissible_generators`,
  node `lem-sfb-proper-base-change-admissible-generators`;
- `AlgebraicGeometry.ProEtale.CondensedRing.compactSupportRefinement_baseChange`,
  node `lem-sfb-compact-support-refinement-base-change`.

The private proofs of open exchange, the explicit common dense refinement construction,
categorical cancellation,
and localizing proper exchange contain no holes. Existing imported statements retain
their current proofs and holes.

## No longer needed

The imports `Sheaf.Paper.CartesianCoefficients` and
`Sheaf.Paper.CondensedModuleDerivedPushpull` are no longer needed: the proof uses no
declaration of either (reviewer fix: both imports removed from the item, and
`sk-prop-sfb-cartesian-coefficients`, `sk-def-sfb-module-derived-pushpull` removed from the
item's `proof_deps`; the unit has no realized modules, so no route is bypassed).
No original public import is removed: the helper definitions retain exactly their public
statement dependencies. Trial proof imports for scalar mates, derived composition, identity
on the open, and lower-star composition are not imported directly by the final item. The
open clause needs only the existing cartesian-counit and open-unit results, rather than a
new sectionwise common-right-adjoint construction. The final refinement argument uses binary
common dense refinements three times and needs no finite-family universe parameter.

The following former direct proof dependencies are removed from the item's `proof_deps`:

- `lemma-nagata-compactification-base-change`
- `def-sfb-module-open-lower-shriek-adjunction`
- `sk-def-sfb-module-pushforward-pullback`
- `def-weil-pbc-composite-adjunction`
- `lem-weil-proetale-weakly-etale-localization`
- `def-sfb-finite-lower-star`
- `def-sfb-module-lower-star`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `def-sfb-module-open-lower-shriek`
- `sk-def-sfb-derived-categories`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `det-thm-sfb-proper-base-change-finite`
- `det-thm-sfb-proper-base-change-integral`
- `det-thm-sfb-proper-base-change-rational`
- `def-weil-pbc-adjunction-mate`
- `def-sfb-module-upper-star-comp`
- `lem-sfb-derived-composition-adjunction-normalization`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `det-nagata-refinement-morphisms`
- `det-sf-comp-composition-interchange`
- `lem-sfb-base-change-identity-open-restriction`
- `sk-prop-sfb-cartesian-coefficients` (reviewer)
- `sk-def-sfb-module-derived-pushpull` (reviewer)

The finite/integral/rational coefficient results remain dependencies of the new generator
lemma. Derived normalization, identity on the open, mate pasting and refinement uniqueness
remain dependencies of the new local refinement lemma. They are moved down the retained
argument, not claimed globally pruned. Other foundational definitions remain reached through
the definitions and the proved imported APIs. No whole existing module is withdrawn or
asserted globally unnecessary. In particular no upstream declaration is removed.

The obsolete direct `tool_uses` approvals removed (retained entries keep their order) are:

- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ring-sheaves-grothendieck`

## Where the brief, the DAG or earlier work was wrong

The planned coefficient case analysis mentions six familiar representatives, but the actual
admissibility predicate also includes the full continuous-map algebraic closure and permits
ring-object isomorphism transport. The existing rational theorem does not directly state the
full-continuous generator assertion. The separate generator lemma records that missing input
explicitly; it does not conflate continuous-map and finite-subextension coefficients.

The public pullback theorem likewise lists representatives. Its private, already proved
constant-model preservation argument applies to arbitrary condensed coefficients and supplies
the preservation actually needed here. Proper preservation for all seven classes is already
proved and is used unchanged.

After arbitrary base change the original dense compactification need not stay dense. The
proof chooses a new dense source over the pulled-back base, refining both pulled-back
compactifications and the pulled-back original dense source, and never assumes density of
the latter. The local equation and its edge cases (identity refinements/base changes, empty
opens and zero objects) preserve the indicated arrow directions. The unit route stays
open exchange, proper exchange, then comparison compatibility.

## New nodes

`def-sfb-compact-support-base-change-maps` records the seven specified constructions in their
shared API module. Change record: `coord/changes/det-sf-comp-base-change-interface.md`.

`lem-sfb-proper-base-change-admissible-generators` states proper exchange on the Dctf
generators only. Its proof source is the proper-base-change step of the item, with full
continuous coefficients and coefficient-isomorphism transport made explicit.

`lem-sfb-compact-support-refinement-base-change` states the one-refinement pasting equation
from steps 4--7, with a further dense source after pullback. It does not assert the final
comparison compatibility and does not assert invertibility.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

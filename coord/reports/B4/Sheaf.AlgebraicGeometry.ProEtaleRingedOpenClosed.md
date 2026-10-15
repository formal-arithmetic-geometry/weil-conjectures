## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` by a compiling combination proof.
The existing public definitions, theorem signature, and public imports are unchanged.
The private helpers construct the actual module pullback/pushforward adjunction,
construct the extension/sheafification adjunction and prove its unit invertible
using the singleton summand comparison and sheafification under slice restriction,
prove finite-limit preservation
of extension by zero using the empty-or-singleton summand formula, compute open
restriction of closed direct image as zero, and deduce the other zero composite by
adjunction. A categorical cokernel argument proves finite-colimit preservation of
closed direct image from the counit and localization sequence.

Added five modules, one theorem each. Four isolate the geometric comparison,
closed counit, localization sequence, and abelian filtered-colimit comparison.
The fifth, `ProEtaleRingedFilteredColimits`, is proved: it transfers the abelian
filtered-colimit result to modules using the existing module forgetful API and
reflection of colimits. Updated the parent DAG proof and added the five matching
nodes. No existing interface changes or forced adaptations were necessary. The
proper-base-change unit's realization and route are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.proEtale_ringed_open_closed` (one of one original holes).
Also proved the new theorem
`AlgebraicGeometry.Scheme.proEtale_ringed_filtered_colimits` in
`ProEtaleRingedFilteredColimits`.

Four holes are added; the original module has none. This is a decomposition,
not an axiom-free proof or a net reduction in the sorry ledger (1 closed, 4 added):

- `AlgebraicGeometry.Scheme.proEtale_ringed_open_comparison`, node
  `lem-weil-pbc-proetale-ringed-open-comparison`. Still needs the arbitrary-ring
  transport along the weakly-etale localization equivalence, its comparison with
  the actual model-based module inverse image. The shriek unit is proved in the
  parent module. This comparison needs no closed complement or finiteness
  hypotheses.
- `AlgebraicGeometry.Scheme.proEtale_ringed_closed_counit`, node
  `lem-weil-pbc-proetale-ringed-closed-counit`. Still needs the affine ind-etale
  closed-site adjunction to compute the actual inverse-image counit, then descent
  from the affine basis, including compatibility with the coefficient action.
- `AlgebraicGeometry.Scheme.proEtale_ringed_localization_sequence`, node
  `lem-weil-pbc-proetale-ringed-localization-sequence`. Still needs the bounded
  weakly-contractible covering argument and the identification of the actual
  module unit/counit maps with the local open/specialization formulas. The monic,
  epic, and exact assertions are all included in this one geometric obligation.
- `AlgebraicGeometry.Scheme.proEtale_closed_abelian_filteredColimits`, node
  `lem-weil-pbc-proetale-closed-abelian-filtered-colimits`. Still needs the
  qcqs-section comparison transported through localization to affine objects of
  the ambient site, followed by detection of the colimit comparison on that basis.
  Module actions are already handled in the proved ringed transfer theorem.

All four are proper portions of the original conclusion; none restates the whole
parent or merely repackages its hypotheses. Empty sites/objects, zero modules and
empty extension index sets are included in the constructions. The closed-counit
assertion is independent of the choice of adjunction, by
uniqueness of adjunctions. The localization sequence uses those specified
adjunctions; changing either conjugates the corresponding map by an isomorphism.

## No longer needed

The following proof imports were removed from the original module:

- `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus`
- `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`
- `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation`
- `Sheaf.RingTheory.WContractibleClosedLocalization`
- `Sheaf.RingTheory.BoundedWContractibleExtension`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

These are removals from the parent's direct imports, not a claim that every
listed module disappears from the global target closure. The affine comparison,
closed-site adjunction, module inverse-image comparison, qcqs section calculus,
weakly-contractible, specialization, ring-theoretic, and covering dependencies
remain imported by the new geometric obligations. They are not pruned globally.

The delivery does not use node
`lem-pur-site-restriction-module-adjunction-exact` or its module
`Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`. This is the only old parent
proof dependency unused by every delivered node. Its required adjunction and
exactness portions are proved locally with the universes of the actual site.
The derived-category and sheaf-cohomology imports are unnecessary for this
underived argument. No modules are withdrawn and no `deleted.txt` is needed.


For completeness, the old parent node dependencies removed from its direct
`proof_deps` are:

- `def-exc-closed-site-lift`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-proetale-covering`
- `def-weil-pbc-proetale-site`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-sheaf-of-modules-category`
- `def-weil-size-convention`
- `lem-exc-closed-site-adjunction`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-ind-etale-basis`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-proetale-affine-wcontractible-covering-family`
- `lem-weil-pbc-proetale-qcqs-fp-section-calculus`
- `lem-weil-pbc-proetale-shriek-specialization-zero`
- `lem-weil-pbc-proetale-specialization-restriction-sections`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-spec-localization-away-basic-open`
- `lem-weil-pbc-wcontractible-affine-weakly-contractible`
- `lem-weil-pbc-wcontractible-closed-localization`
- `lem-weil-pbc-wcontractible-ring-extension`
- `lem-weil-proetale-weakly-etale-localization`

Except for the unused generic localized-module argument identified above, these
are retained in the split nodes or remain available through their imports; this
is direct-dependency pruning, not a claim of global closure pruning.

## Where the brief, the DAG or earlier work was wrong

The generic `localizedModule_adjunction_exact` is stated with site objects and
morphisms in the same universe and module coefficients in that universe. Here the
actual pro-etale site has objects in `Type (u + 1)` and morphisms in `Type u`, while
module coefficients are in universe `u + 1`. Direct instantiation does not fit.
The proof below needs only its extension adjunction and finite-limit argument;
these are supplied by universe-correct private helpers without changing the
existing lemma or public interface.

Weakly-etale localization supplies the site and arbitrary sheaf-category
comparisons, but its module comparison is for its stated coefficient presentation.
It does not directly supply the arbitrary coefficient-ring comparison required
here. This missing compatibility is recorded explicitly in the open-comparison
node, rather than treating a constant-coefficient result as an arbitrary-ring one.

The original step deriving `i* j! = 0` from the short exact sequence is unnecessary:
the two adjunctions and the proved equality `j* i_* = 0` give it directly by Hom
vanishing. The parent proof and docstring now record this shorter route.
An attempted alternative used
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` to reflect
isomorphisms via fixed integer coefficients, then deduce the closed counit from
the localization sequence. Its import fails before elaborating a proof:
`import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs failed,
environment already contains AlgebraicGeometry.ProEtale.«term(_)_*[_]» from
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
The attempted import and helper were removed. The delivery makes no changes to
those source modules and retains the independent geometric counit obligation.

No statement is marked disputed, no target signature changed, and no data were
chosen from an unproved mere-existence theorem inside a definition.

## New nodes

`lem-weil-pbc-proetale-ringed-open-comparison`:
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedOpenComparison.lean` isolates open
localization for arbitrary ring coefficients. Source: Stacks
Tags 09BN and 00XZ. It contains one geometric hole.

`lem-weil-pbc-proetale-ringed-closed-counit`:
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedClosedCounit.lean` isolates full
faithfulness of closed direct image with its actual coefficient action. Source:
Stacks Tags 09AA, 09BK and 09BL. It contains one geometric hole.

`lem-weil-pbc-proetale-ringed-localization-sequence`:
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedLocalizationSequence.lean` isolates
short exactness of the actual unit/counit sequence. Source: Stacks Tags 09AH,
09AG and the bounded weakly-contractible localization argument. It contains one
geometric hole.

`lem-weil-pbc-proetale-closed-abelian-filtered-colimits`:
`lean/Sheaf/AlgebraicGeometry/ProEtaleClosedAbelianFilteredColimits.lean` isolates
the abelian geometric comparison. Source: Stacks Tags 0738 (4) and 098D and the
existing qcqs section calculus. It contains one geometric hole.

`lem-weil-pbc-proetale-ringed-filtered-colimits`:
`lean/Sheaf/AlgebraicGeometry/ProEtaleRingedFilteredColimits.lean` proves the
module transfer of the preceding abelian preservation theorem, using
`moduleSheaves_colimits_forgetful`. Its proof contains no hole. Source: Stacks
Tags 0738 and 098D and the module-sheaf colimit construction.

All five nodes are in `dag/nodes/sec-proper-base-change/`. Their blueprint
ancestor is `thm-weil-pbc-qbar`, with the parent item and the existing descent
chain recorded in `from.via`. Blueprint searches for Tags 09BN, 09AA and 0738
found no identical imported blueprint statement. No change record is
required: no existing public declaration, definition, statement, or visibility
changed.

First-worker validation: all six delivered modules compiled with `lcompile.py --all`;
the main module took approximately 21 seconds. Its dry run printed `OK (dry run)`.
The independent second reading and final delivery follow below.


## Second reading by B4

1. Interface check: PASS. Compared every delivered file against the read-only
   repository using `diff` and an exact extraction check. The three existing
   definitions, the existing theorem signature, and all original public imports
   are byte for byte unchanged. The other five modules are new. No change record
   or forced adaptation is needed. The parent node differs only in `proof`,
   `proof_deps`, and `proof_origin`.

2. Proof check: PASS as a decomposition. Independently compiled all six modules
   in import order with `lcompile.py --all`. Read the model-site adjunction
   construction, direct-sum Hom equivalence, singleton/empty evaluation argument,
   restriction/sheafification unit comparison, empty closed-fibre computation,
   Hom-vanishing argument, cokernel argument, and module colimit transfer. No
   forbidden declarations, hidden data holes, or arbitrary data selected from
   unproved existence occur. Explicit `#print axioms` in a scratch copy gives only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the parent and
   split-dependent theorems; the three public definitions use only the three
   allowed axioms. The four remaining `sorry`s are exactly the named geometric
   theorems listed above. The original hole is closed syntactically, not
   axiom-free; the hole count is 1 closed and 4 added, net -3.

3. Split-statement check: PASS. Read all four new holed statements and their
   complete docstring arguments, and checked their matching nodes. Each is a
   proper part of the argument. Open comparison needs no closed complement;
   closed counit needs no complementary open; localization isolates just the
   short exact sequence; abelian filtered-colimit preservation has no module
   coefficients. None merely renames the parent. Checked zero rings/modules,
   empty schemes, the empty open, and the entire open: direct sums with no
   indices are zero, singleton sums recover restriction, and empty closed fibres
   have zero sections by the empty covering. Adjunction changes conjugate the
   unit/counit by isomorphisms and preserve exactness. Independently searched
   with leanfinder (slice/open/subterminal module equivalence), loogle
   (sheaf counit isomorphisms), grep, and `rg` over both source roots. The hits
   concern sheafification, dense-subsite equivalences or fixed coefficients,
   not these actual arbitrary-ring module functors. Inspected the generic
   localized-module theorem: its `SmallCategory` universe prevents direct use
   here. The existing fixed-coefficient closed-immersion theorem also cannot
   directly replace the ringed comparison. No split could be closed by a short
   application of the inspected declarations.
   Checked the cited geometric arguments against Stacks
   [09AA](https://stacks.math.columbia.edu/tag/09AA),
   [09AH](https://stacks.math.columbia.edu/tag/09AH),
   [09BN](https://stacks.math.columbia.edu/tag/09BN), and
   [0738](https://stacks.math.columbia.edu/tag/0738).

4. Route and pruning check: PASS after report corrections. The proof opens the
   original target hole and proves its categorical consequences directly before
   leaving the four geometric obligations. The proper-base-change unit's
   `realized` statement/steps are unchanged and none is bypassed. The module
   forgetful API is used for the colimit transfer. Removed two redundant new
   proof imports, `Mathlib.CategoryTheory.Sites.CoverLifting` and
   `Mathlib.Algebra.Category.Grp.FilteredColimits`; a scratch compile of the
   resulting main module passed. Completed the list of old direct parent DAG
   dependencies removed from `proof_deps`. Corrected the report's import list:
   `ProEtaleModuleInverseImageUnderlying` was already absent from the repository
   parent's imports. No global module pruning is claimed.

5. DAG check: PASS. Each new node has source, statement dependencies, proof steps,
   origin, search records, creation data, unit/chapter, blueprint ancestry, and a
   Lean record. Every `proof_deps` is exactly the union of its proof-step uses.
   All five new Lean signatures match their node statements verbatim; the old
   parent's normalized stored signature also matches. The parent proof records
   the actual adjunction, zero-composite, finite-limit, cokernel and filtered-
   colimit routes. Existing unit records need no change.

Second-reader changes: removed the two redundant private Mathlib imports and
corrected/completed the report as described in point 4. No mathematical statement,
public definition, proof body, or DAG record changed during the second reading.

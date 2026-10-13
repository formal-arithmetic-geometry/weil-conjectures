## What changed

Repair: removed the duplicate local `restrictedResolutionSections_nonempty`
construction from `FlatBaseChangeTargetOpenEdge`. The proof now imports
`Sheaf.AlgebraicGeometry.RestrictedResolutionSectionsExist` and uses its public
`restrictedResolutionSections_exists` theorem.

Replaced `exists_flatBaseChange_module_leray_comparison`'s sorry with a complete
Lean combination of a chart transport and a smaller-open normalized Leray edge.
The existing signature and visibility are unchanged. Added proof-only imports of
`FlatBaseChangeChartCohomologyTransport` and `FlatBaseChangeTargetOpenEdge`.
The former isolates the geometric chart and coefficient-unit calculation. The
latter is proved using `affine_resolutionSectionClass_bijective` and
`resolutionSectionClass_map_smulHom`, and constructs restricted resolutions
termwise rather than choosing arbitrary data from an unproved existence theorem.

The main proof composes the supplied E inverse with the two additive equivalences,
proves scalar compatibility from E naturality and their scalar equations, and
uses `LinearEquiv.ofBijective` through the proved private helper
`linearEquiv_from_scalar_transports`. Its formula follows by cancelling E inverse
composed with E and composing the chart unit and normalized restriction equations.
`ResolutionSectionClassOpenRestriction` defines the actual open restriction h-map
using the restriction-composition coefficient iso and adjunction unit.

The complete delivered set is checked with lcompile.py and deliver3.py. The extra heartbeat budget is
for elaborating categorical/module transports; explicit equality compositions
avoid expensive rewriting. No definitions, existing statements or other groups'
modules were changed. Local irreducibility commands are documented in the change
record because preflight conservatively classifies them as interface commands. The realized statement and steps of sk-thm-p1 are unaffected.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_module_leray_comparison`
(node `new-flat-base-change-module-leray-comparison`). There are no sorries left in
the item's module.

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_target_open_edge`
(node `new-flat-base-change-target-open-edge`) from existing affine bijectivity
and scalar compatibility and the new restriction statement.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_chart_cohomology_transport`
  (`new-flat-base-change-chart-cohomology-transport`): the geometric chart/unit
  step, without any Leray edge, higher images, Ext coordinates, qcqs or
  quasi-coherence assumptions.
- `AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_open_restriction`
  (`new-resolution-section-class-open-restriction`): restriction between two
  arbitrary opens for a fixed augmented resolution, without affineness,
  quasi-coherence, base change or scalar extension.

This is a decomposition, not a sorry-free mathematical proof: one original hole
closed, two lower holes added. The intermediate statements are strictly different
parts of the argument and their combination, including B-linearity, is proved.
Neither adds an invertibility assumption on any cohomology pullback/restriction.

Edge cases checked in the statements and their source arguments: W=V or top
opens make restriction the identity; empty W gives zero section/cohomology groups;
zero coefficients give zero groups; p=0 uses augmentations and ordinary sections.
The chart construction uses the exact canonical algebraMap hypothesis. No flatness
is used: only the chart identification and affine Leray edge are inverted.

## No longer needed

Current second reading removed the redundant proof-only import of
`ModuleOpenRestrictionInjectives` from `FlatBaseChangeTargetOpenEdge`: the proved
`restrictedResolutionSections_exists` supplies the construction directly. The
edge node now records `lem-pc-restricted-resolution-sections-exist` as its immediate
dependency; the injectivity and restriction-comparison construction dependencies
remain below that existing theorem. No module becomes unreachable.

No existing imports were removed. This second reading also removed the unused
public import of `FlatCohomologyComparison` from the new target-edge module, replacing
it with the direct `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` import needed
for `smulHom` in the signature.
Removed unused imports of
`FlatCohomologyComparison`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
and `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` from the new general
restriction module. Chart transport imports its required scalar-extension
definitions directly. No original planned node or module is pruned:
the geometric/functorial nodes now belong below chart transport, and the
bijectivity/scalar/natural section nodes below the smaller-open edge and restriction
statement. The parent now records its immediate dependencies accurately rather
than all geometric substeps. The chart module imports only the general restriction
interface, so it does not depend on the target edge theorem.

The parent no longer directly lists the following old proof dependencies:
`def-pc-fibre-product`, `def-pc-tensor-pullback-composition-iso`,
`def-weil-pbc-flat-base-change-open-choices`, `def-weil-pbc-module-cohomology-fmap`,
`lem-pc-affine-resolution-section-bijective`, `lem-pc-resolution-section-scalar-map`,
`lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-module-cohomology-fmap-functorial`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction`.
These are retained below the new intermediate nodes or in the public signature's
underlying definitions; none represents a pruned module. The second reader also
made the new edge module's Tilde import proof-only. A fresh Loogle search for
`sectionCohomologyTheta` and library searches for cohomology isomorphism,
composition and resolution-class naturality found no duplicate of either split claim.

## Where the brief, the DAG or earlier work was wrong

The old proof plan accurately describes the argument, but its existing declarations
do not supply the chart transport or arbitrary-open normalized class restriction
as usable interfaces. `TargetSectionClassRestriction` supplies only a top-open germ
formula, which cannot imply this two-open equation for arbitrary classes. Reusing
its proof would require extending the section-complex restriction calculation.
`RestrictedResolutionCohomology` gives top-to-open restriction before theta; the
new restriction statement identifies the remaining composition/naturality step.
The already proved affine bijectivity and scalar lemmas were used directly.
No statement is disputed. LeanSearch was unavailable (Internal Server Error);
LeanFinder, Loogle, Mathlib/library searches and blueprint searches were recorded.

## New nodes

`new-flat-base-change-chart-cohomology-transport` records the chart and coefficient
unit calculation (original steps 1–2), with its scalar endomorphism equation.
Module: `Sheaf.AlgebraicGeometry.FlatBaseChangeChartCohomologyTransport`.

`new-resolution-section-class-open-restriction` records the general restriction
calculation for normalized resolution classes, used to identify the old target
class on a smaller open (original step 3). It also records the explicitly
constructed `cohomologyOpenRestriction` in its Lean declarations.
Module: `Sheaf.AlgebraicGeometry.ResolutionSectionClassOpenRestriction`.

`new-flat-base-change-target-open-edge` records the proved smaller-open affine
edge and its scalar/restriction equations (original steps 3–4), using the
existing `lem-pc-restricted-resolution-sections-exist` theorem for restricted
sections.
Module: `Sheaf.AlgebraicGeometry.FlatBaseChangeTargetOpenEdge`.

Every new theorem has a source and full proof in words in its docstring. The
parent node's proof, proof_deps and proof_origin now follow the actual Lean
combination. The change record is
`coord/changes/flat-base-change-module-leray-elaboration.md`: it documents only
local irreducibility attributes, conservatively classified by preflight as
interface commands. They prevent repeated unfolding during this file's proofs;
no signature, definition, target meaning or exported attribute changes.
No forced adaptations are needed.


## Earlier second reading (a previous round; superseded)

1. Compared each delivered module with the repository versions. Existing declarations and target signatures are unchanged; only the intended proof imports, proofs, and new split modules/nodes are present. Verdict: pass.

2. Compiled all delivered modules with `lcompile.py`; the only remaining `sorry`s are the two named split theorems listed above, with no forbidden declarations or hollow definitions. The proof uses only ordinary Lean axioms plus those open theorem holes. Verdict: pass.

3. Read Tags 02KH, 0096, 0097, 01FB, 01E4 and 01XK against the declarations. For chart transport, hV and hW identify the affine opens with their spectra; eVW supplies the restricted square; hAlgebra fixes its section map; D.unit_square pins the coefficient map. The two displayed clauses are scalar compatibility and compatibility with that unit. No flatness, qcqs or quasi-coherence is needed because t identifies two presentations of the same pullback, rather than inverting cohomological base change. For arbitrary-open restriction, R.augmentation and R.components, and the corresponding fields of R prime, fix the resolution and section comparisons; Tag 01E4 and naturality give the displayed restriction equation without affineness. For the target edge, qcqs is preserved by base change and quasi-coherence by pullback; hW permits affine_resolutionSectionClass_bijective, resolutionSectionClass_map_smulHom gives the scalar clause, and resolutionSectionClass_open_restriction gives the restriction clause. The parent composes E inverse, t and d; E naturality supplies B-linearity, and hunit followed by hres gives its unchanged formula. Checked p=0, empty opens and zero coefficients using the same constructions. RestrictedResolutionCohomology and TargetSectionClassRestriction supply top-to-open results, not either new statement. No sk-thm-p1 realized node is bypassed. The erroneous 01AJ citation was corrected to 0096 and 0097.

4. The parent proof follows the shortest available proved route through the chart transport and affine target edge. Imports used by the proofs are retained, and the report's pruning list records removed imports from the restriction module. Verdict: pass.

5. The parent and new node records match the declarations, proof dependencies, and proof origins; the realized unit route remains unchanged. Verdict: pass.

Changed during second reading: changed the Tilde import in FlatBaseChangeTargetOpenEdge from public to proof-only, because it supplies isQuasicoherent_pullback only in the proof; expanded the immediate dependency accounting and appended this review record. No statements or proof bodies changed.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the repository version. Existing declaration
signatures and target statements are unchanged; added imports are proof-only except
for the new modules and their public interfaces. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py`. The parent and target edge
compile without errors; the only remaining `sorry`s are the two named split theorems
`exists_flatBaseChange_chart_cohomology_transport` and
`resolutionSectionClass_open_restriction`. No forbidden declarations or hollow
definitions were found. Scratch-copy `#print axioms` checks of the parent, target
edge and chart theorem show only propext, Classical.choice, Quot.sound and sorryAx;
cohomologyOpenRestriction has only the three permitted axioms. Verdict: pass.

3. Checked the two split statements against their source arguments and edge cases
(equal and empty opens, degree zero, and zero coefficients). Both are strictly smaller
than the parent and needed for its composition; no duplicate library theorem was
found. Fresh LeanFinder searches for derived-section naturality on nested opens,
Loogle searches for mapNatTrans, and Mathlib grep for cohomology restriction/isomorphisms
found general ingredients but no duplicate of either split claim. Verdict: pass.

4. The parent proof uses the shortest available route through chart transport and the
smaller-open affine edge, with the restriction theorem supplying the missing naturality
step. Proof-only imports and unused dependencies were pruned as recorded above.
Verdict: pass.

5. Compared all node `lean`, `proof`, `proof_deps`, and `proof_origin` fields with the
Lean declarations. The realized `sk-thm-p1` route is preserved and the new nodes carry
their sources and docstrings. Verdict: pass.

Changed during this reading: removed the redundant public FlatCohomologyComparison
import from FlatBaseChangeTargetOpenEdge in favor of the defining Cohomology.Defs
module, removed the unused Ext flat-comparison statement dependency from the new
edge and restriction nodes, and added the required review section and
explicit axiom/search evidence. No proof bodies or theorem statements changed.


## Second reading by U3

1. Compared all four delivered modules with the read-only repository. Only the
parent already exists there; its theorem signature and docstring are byte-for-byte
unchanged. The three new modules introduce the reported interfaces. No target,
existing definition, exported attribute, or other group's module changed. Pass.

2. Compiled the four modules with lcompile.py. Exactly the two reported named
split theorems contain sorry; the parent and target edge have complete proofs.
cohomologyOpenRestriction constructs its coefficient map from restriction units
and composition isomorphisms. restrictedResolutionSections_exists is proved by
an explicit termwise construction, so the edge does not select arbitrary data
from an unproved existence theorem. The adjunction witness determines its
left-adjoint comparison uniquely. No forbidden declarations found. Scratch-copy #print axioms checks of the parent, target edge and both split
theorems show only propext, Classical.choice, Quot.sound and sorryAx; the concrete
cohomologyOpenRestriction definition has only the three permitted axioms. The
delivery probe additionally checks every declaration.

3. Read both split statements, their full proof docstrings, and the underlying
RestrictedResolutionSections and FlatBaseChangeOpenChoices fields. Checked the
geometric chart identification, coefficient-unit normalization, and restriction
naturality against Stacks [02KH](https://stacks.math.columbia.edu/tag/02KH),
[01FB](https://stacks.math.columbia.edu/tag/01FB),
[01E4](https://stacks.math.columbia.edu/tag/01E4), and the affine edge against
[01XK](https://stacks.math.columbia.edu/tag/01XK). The chart equivalence identifies
two presentations of the same scheme and coefficient; it does not assert
invertibility of a base-change map. The restriction clause needs no affineness.
Equal opens give identity restriction, empty opens and zero coefficients give
zero groups, and degree zero uses the pinned augmentations. Both holes are true,
needed, and strictly smaller parts of the argument. Fresh LeanFinder search for
nested-open derived-section naturality, Loogle for mapHomologyIso, msearch grep
for module-cohomology isomorphisms, and rg of the library found ingredients but
no duplicate of either statement. Closing either hole requires substantial
comparison calculations, not a short application of an existing theorem. Pass.

4. Read the composition from the target downward: the helper constructs the
linear equivalence from E inverse, t and d using all three scalar equations;
the final equality composes hunit with hres. Existing affine bijectivity and
scalar results are used directly. The new restriction theorem covers arbitrary
opens; the existing TargetSectionClassRestriction only covers top-open germs.
Removed the redundant proof-only ModuleOpenRestrictionInjectives import from
the new target-edge module. No original planned module is pruned; the complete
old immediate-dependency list appears above. sk-thm-p1's realized route stays
unchanged. Pass.

5. Compared the four nodes with their Lean declarations and proof steps. The
parent changes only proof, proof_deps and proof_origin. New nodes have sources,
searches, creation and blueprint records, and verbatim theorem statements.
Corrected the target-edge node to cite lem-pc-restricted-resolution-sections-exist,
which the proof applies, rather than listing its internal construction steps as
immediate dependencies. Recomputed proof_deps as the union of step uses. Pass.

Changed in this reading: removed one redundant proof-only import and corrected
the target-edge proof dependency accounting. Added this independent review.
No theorem statements, definitions, or proof bodies changed. One original hole
is closed and two holes are added: this remains a decomposition, with net -1
holes closed, rather than a completed mathematical proof.

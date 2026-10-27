## Worker report

Stage 2, Q53, lem-sfb-space-closed-coherent-modules. This delivery states
`AlgebraicGeometry.AlgebraicSpace.closedImmersion_noetherian_coherent_support` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules`. Its sole proof is
`sorry`. The companion module `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`
constructs support using actual sections and pointed refinements, with no postponed data
or proofs. Both files compile individually through scompile.py against the published
server library, including the sibling dependency in a private overlay. No warnings.

The inherited BLOCKED ending concerned the already accepted stage-1 split, not an
existing stage-2 statement. The live item has status split, no lean record, no repair
note, and an entry in the stage-2 queue. Q09's report is explicitly Stage-1. The split
and its proof are preserved; the item changes only in lean and stmt_deps (the new
support definition and the landed owner of mapPoint). No dependency record is changed. The landed owner of mapPoint is added to stmt_deps.

Hypotheses and clauses, in order:

- A scheme S and algebraic spaces Z and X over S are the explicit binders
  `{S : Scheme.{u}} {Z X : AlgebraicSpace S}`. There is no assumption on S.
- The map is `i : Z ⟶ X`, using the category of fppf sheaves in the recorded
  AlgebraicSpace definition. `hi : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` states that every scheme
  base change is represented by a scheme closed immersion. It includes representability.
- Local Noetherianity on all etale scheme charts is `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)` for the existing atlas
  topology. CompactSpace does not require Hausdorffness or nonemptiness.
- Absolute quasi-separatedness is hqs: for any two affine S-schemes mapping to X,
  the point space of their presheaf fibre product over X is quasi-compact. This is
  the usual affine-pair test for the absolute diagonal, also used by the landed
  AlgebraicSpaceCoherentFilteredUnion module. This condition does not assume that
  S is quasi-separated or replace absolute quasi-separatedness by relative
  quasi-separatedness over S.
- The first three conclusion factors are the identical local Noetherian, compact,
  and affine-pair quasi-separated tests for Z: precisely Z is Noetherian.
- Module sheaves are the recorded `Z.Modules` on the small etale structure sheaf.
  For every such M, `M.IsFinitePresentation` expresses coherence. Stacks Spaces
  Cohomology, lemma-coherent-Noetherian (07UB), explicitly identifies this predicate
  with quasi-coherent finite type modules and with coherent pullbacks on every etale
  scheme chart, on locally Noetherian algebraic spaces. The local Noetherianity of Z
  is a conclusion of the same theorem. No finite presentation assumption stronger
  than the node's coherence is added. Mathlib's finite presentation class already
  implies IsQuasicoherent, so no redundant hypothesis is included.
- `((moduleDirectImage i).obj M).IsFinitePresentation` states that the specified
  module direct image, including its canonical regular-function scalar action,
  is coherent on X. This uses the existing universal-property direct image rather
  than an arbitrary functor.
- The remaining equality is literally
  `moduleGeometricSupport ((moduleDirectImage i).obj M) =
  mapPoint i.hom.hom '' moduleGeometricSupport M`.
  Its right side is the set image under the existing induced point map.
- The node's remarks describing reducedness and irreducibility are conventions,
  not hypotheses or conclusions: neither property is assumed for X or Z.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  EtaleSite, etaleForget, structureSheaf and Modules.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian,
  the all-affine-open definition and the locally-finite-type permanence theorem.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its slice
  sheafification instances; Mathlib's SheafOfModules.IsFinitePresentation and
  IsQuasicoherent are used on the exact same module category.
- Mathlib's SheafOfModules.IsFinitePresentation is the coherence predicate used here,
  exactly as in the landed Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
  convention, justified for locally Noetherian spaces by Stacks 07UB. The existing
  pqf-def-coherent record is preserved; neither its scheme finite-type predicate nor
  RingedSpace.IsCoherent occurs in this statement. The record question is reported
  below for the maintainer.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology and AlgebraicSpacePointClasses:
  Point, PointRepresentative, pointTopologicalSpace. The new support definition
  uses these exact classes, their actual field-valued representatives and their
  given small etale charts.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion, specialized inside IsRepresentableWith.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleDirectImage,
  the limit of the chart diagram with its regular-function scalar action.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: mapPoint, the existing quotient map
  on field-valued point classes, used for the support image.
- Proof imports with recorded declarations: EtaleLocalNoetherianDescent
  (isLocallyNoetherian_of_etale_cover), SchemeZariskiEtaleQuasiCoherentEquivalence
  (scheme_zariski_etale_quasiCoherent_equivalence),
  AlgebraicSpaceEtaleModulePushforwardRestriction
  (etale_module_pushforward_restriction), AlgebraicSpaceFibreProductsEtaleCovers
  (fibreProduct_isAlgebraicSpace), and upstream
  WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
  (closedImmersion_coherent_equivalence and closedImmersion_coherent_support).
  The remaining proof dependencies lack recorded modules or are Mathlib facts
  already provided by the imports; the natural-language docstring retains every
  step and names the dependencies needed later. No missing proof dependency is
  used to choose mathematical data in this statement.

Edge cases checked before writing:

- The empty space and empty closed subspace are allowed. Compactness has no
  Nonempty requirement, all chart statements quantify over their actual sites,
  and support is empty when there is no point representative.
- The zero module has empty support: a purported surviving section is tested
  against its own pointed chart and identity refinement, so zero cannot survive.
- The identity immersion gives precisely preservation by the canonical identity
  direct image and equality with the identity point image.
- Nonreduced closed immersions and nontrivial nilpotent ideals are allowed;
  there is no reduced, integral, irreducible, or injective structure-map hypothesis.
- Quasi-separatedness is absolute, with an arbitrary possibly non-quasi-separated
  base. All field and scheme tests use universe u, matching the actual project
  space convention; an algebraic closure of a u-small field is again u-small.
- Support is defined for arbitrary modules, including ones that are not finitely
  generated: the forall refinement condition is imposed on a single section, not
  a claim that the entire module vanishes on one neighbourhood.

Searches made:

- msearch leanfinder: "A closed immersion of algebraic spaces into a Noetherian
  algebraic space has Noetherian source and preserves coherent modules and their
  supports under direct image". Eight hits on scheme Noetherian and closed immersion
  facts; no algebraic-space theorem.
- msearch loogle: `"IsClosedImmersion", "IsCoherent"`: zero hits.
- msearch grep: `AlgebraicSpace|closed.*coherent|coherent.*closed`: eleven hits on
  generic quasi-coherent categories and unrelated topological coherence.
- msearch leanfinder for support by nonzero geometric germs on pointed etale charts:
  eight hits, on affine support, scheme ideal support and ordinary ringed-space germs.
- msearch loogle: `"AlgebraicSpace", "stalk"`: zero hits.
- msearch grep: `ModuleGermRepresentative|moduleGeometricSupport|AlgebraicSpace.*[Ss]talk`:
  zero hits.
- msearch leansearch: "Support of a sheaf of modules on an algebraic space computed
  by pointed etale neighborhoods and nonzero geometric germs": eight hits, on
  scheme ideal support, Module.support, and TopCat.Presheaf.Γgerm. None supplies
  this support set on algebraic-space point classes.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, closed/coherent space
  facts, module support, stalks, and the proposed declaration names: no existing
  theorem or support declaration. Existing space modules provide the reused
  infrastructure. Scheme support and coherent direct images were read, not copied.
- Searched DAG definition nodes for geometric support and pointed neighbourhoods;
  the hits are scheme/proetale and coefficient-specific definitions. The existing
  lem-sfb-space-etale-chart-support is a theorem requiring this very support set,
  with no Lean record; it does not define a competing notion. blueprint_refs.py
  search algebraic support returned 87 blueprint nodes, none defining this notion.
  blueprint_refs.py ancestor returns None for this item's already broken imported
  ancestry; the new node preserves the item's explicit source place and via chain.

Sources inspected: spaces-properties.tex definition-support and lemma-zero-over-image;
spaces-cohomology.tex definition-coherent, lemma-coherent-Noetherian,
lemma-i-star-equivalence and lemma-finite-pushforward-coherent; spaces-morphisms.tex
lemma-stalk-push-closed, with the transposed subscripts explicitly noted by the item.
There is no statement dispute or correction.

## New nodes

`def-sfb-space-module-support` defines support on the existing algebraic-space point
classes, for an arbitrary module on the existing small etale ringed site. Its module
has two declarations: ModulePointedChart records a chart with a field-point lift over
p, and moduleGeometricSupport consists of classes of algebraically closed representatives
with a section surviving every pointed refinement. The source is Stacks Properties of
Spaces, definition-support, with the explicit zero-germ test of lemma-zero-over-image.
This is nonvanishing of the actual geometric stalk: stalks are filtered colimits of
sections, and a germ is zero if and only if a refinement makes its representative zero.
No stalk module, map, or choice of atlas is postulated. All data are constructed in full,
and there are no extra theorems or sorries in this definition module. The searches above,
also recorded on the new node, found no existing algebraic-space module support notion.
The item cites this node in stmt_deps; its statement and accepted split stay verbatim.

## Repair of return ae9c7a197cd6

H13: removed the sandbox copy of pqf-def-coherent.json from the packet, so the
landed Q25 record in Sheaf.AlgebraicGeometry.CoherentFiniteType is unchanged.
This delivery does not rebind a dependency used by other landed files.

H9: removed the unused public import WeilConjectures.AlgebraicGeometry.Coherent.
The theorem signature and its Mathlib IsFinitePresentation coherence convention
are unchanged. The six-step proof docstring and the actual pointed-refinement
support construction are preserved. The clause-by-clause and edge-case checks
above still apply: closed immersion, chartwise locally Noetherian, compact points,
absolute affine-pair quasi-separatedness, all three corresponding conclusions for
Z, coherence of the canonical moduleDirectImage, and equality with the mapPoint
set image; empty Z, zero M, identity immersion, nonreduced Z, arbitrary S.

Advisory: added the already landed def-sfb-proper-curve-moduli to stmt_deps because
its recorded declarations own AlgebraicGeometry.AlgebraicSpace.mapPoint. The
existing public import Sheaf.AlgebraicGeometry.ProperCurveModuli supplies that
canonical map; no new map or duplicate definition is introduced.

## Maintainer note

The natural-language pqf-def-coherent includes the finite-type-kernel condition,
whereas its landed Q25 declaration Scheme.Modules.IsQuasiCoherentFiniteType
expresses quasi-coherence and finite type. The prior packet attempted to rebind
that shared record to RingedSpace.IsCoherent. That rebind is withdrawn as requested;
the maintainer should resolve the shared record question with its existing users.
This item uses neither scheme predicate: on the stated locally Noetherian spaces
it uses Mathlib IsFinitePresentation, the 07UB convention already used by
AlgebraicSpaceCoherentAbelian. There is no mathematical statement correction.

Preflight repair: the new definition node now contains the required import_flags
field (empty). The wrapper's server preflight required it in addition to the fields
listed in the worker brief. No tool files were changed.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (NT-cc-Q53-1b5ef15a3)

Q118 landed def-sfb-space-module-support (lem-sfb-space-coherent-ideal-filtration, landing 20e80a77,
2026-10-23 22:49) after this delivery's base, with module Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
and declaration AlgebraicGeometry.AlgebraicSpace.moduleSupport (scheme-point nonzero-germ test, equivalent to the
geometric-stalk test of this delivery's moduleGeometricSupport). This delivery's copy of the node and module is
dropped (--drop-nodes def-sfb-space-module-support); the item keeps the stmt_dep on the landed node and its
statement now uses moduleSupport in both support terms. No other change.

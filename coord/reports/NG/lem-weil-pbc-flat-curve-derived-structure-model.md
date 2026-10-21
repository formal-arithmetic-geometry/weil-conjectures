## Worker report

Item: `lem-weil-pbc-flat-curve-derived-structure-model`. Module:
`Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel`. The main statement is
`AlgebraicGeometry.flatCurve_derivedStructure_model`. Its sole proof is `sorry`.
Four auxiliary declarations name the objects and arrows explicitly introduced by
the node; they contain real constructions and no postponed proofs.

The source was read in `literature/stacks-project/curves.tex`, the full statement
and proof of `lemma-genus-in-nodal-family-of-curves` (Tag 0GKA). The node isolates
the proof's proper-flat finite-presentation, fibrewise H0, and dimension inputs;
it does not assume nodal singularities or geometrically connected fibres.
The source proves the local positive summand is H1 placed in degree one by
the residue finite-free model. This is precisely the splitting stated here.
No statement correction is needed.

Hypotheses and clauses, in their original order:

* A morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`.
  `[IsProper f]`, `[Flat f]`, and `[LocallyOfFinitePresentation f]` express
  proper, flat, finite presentation. Properness already implies quasi-compactness
  and separatedness, hence quasi-separatedness, so this is the finite-presentation
  convention of the node with no added geometric condition.
* The residue fibre is `f.fiber s`, definitionally the chosen pullback of `f`
  along `S.fromSpecResidueField s`. The dimension assumption is
  `hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1`.
* The structural map on fibre functions is
  `(f.fiberToSpecResidueField s).appTop`. Its source is the global sections
  of `Spec (S.residueField s)`, canonically the residue field, and its target
  is the global functions of the fibre. `hconstants` requires `IsIso` of this
  ring map, equivalently bijectivity. Degree-zero structure-sheaf cohomology
  is global sections, so this is the stated H0 assumption.
* `derivedStructureImage f` is exactly
  `(schemeDerivedDirectImage f).obj (single_0.obj (SheafOfModules.unit X.ringCatSheaf))`.
  This is the node's K, not an arbitrary derived object.
* `derivedStructureUnit f` is `single_0.map` of
  `SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`, followed by
  `Scheme.Modules.canonicalSingleDirectImageMap f` at the structure sheaf.
  This is the canonical derived structural unit. The source's
  `Scheme.Modules.canonicalDirectImageH0Unit` identifies H0 of its second
  factor with the canonical H0 identification; naturality identifies H0 of
  the full composite with structural function pullback. No arbitrary H0
  comparison or unspecified morphism is a hypothesis.
* Perfectness is `S.IsPerfect (derivedStructureImage f)`.
* Invertibility of H0(u) is the `IsIso` conjunct for
  `(DerivedCategory.homologyFunctor ... 0).map (derivedStructureUnit f)`.
* `derivedStructureH1 f` is definitionally H1(K). Its two conjuncts are
  `.IsQuasicoherent` and `.IsFiniteLocallyFree`. The latter is the shared
  variable-rank definition, not finite locally free of one globally fixed rank.
* Zariski locality is `∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ...`.
  The left side of the local isomorphism is restriction of K by the shared
  `(SheafOfModules.overFunctor ... U).mapDerivedCategory`. The two summands
  are the unit on the localized open site placed in degree zero and
  `(derivedStructureH1 f).over U` placed in degree zero then shifted by -1.
  Cohomological shift -1 puts E in degree one. Thus the second summand is
  the restriction of the specified E, not an independently chosen locally
  free module. `Nonempty (A ≅ B)` states existence of the isomorphism.
* The vanishing clause is over all integers:
  `∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (H_i.obj K)`.
  In particular negative degrees are included.
* Arbitrary base change is `∀ (T : Scheme.{u}) (g : T ⟶ S),
  IsIso (derivedStructureBaseChangeMap f g)`.
  The square is the chosen pullback with `f_T = pullback.snd f g` and
  `g_X = pullback.fst f g`. The arrow is `schemeDerivedBaseChangeMap`
  followed by derived direct image of the pinned derived-to-ordinary
  comparison at O_X and the canonical identification of its ordinary
  pullback with O_{X_T}. The target is exactly `derivedStructureImage f_T`.
  The recorded `canonicalSinglePullbackMap` internally uses tensorPullback's
  pinned left-derived counit, followed by the unique adjunction-preserving
  comparison to Mathlib's abstract pullback. The following
  `SheafOfModules.pullbackObjUnitToUnit` is the transpose of the same
  structural map. Consequently their composite is precisely the canonical
  tensor-pullback comparison followed by its structural-unit identification;
  no second pullback notion is defined. This is the normalized map of
  `def-pc-derived-module-base-change-map`.
* There is no flatness assumption on g, no reducedness or Noetherian assumption
  on S, no fixed global rank, and no nonempty-scheme assumption.

The universally quantified `HasDerivedCategory.{w}` instances select shared
derived-category realizations on schemes. The localized-site instances on opens
of S are needed by the recorded `Scheme.IsPerfect` definition and by restriction.
These are foundational localization choices, not additional geometric hypotheses.
All variables and universes are explicitly bound; `autoImplicit` is disabled.
There is no file-local notation, private definition, or local instance.

Dependency declarations read and used (module followed by declarations):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; together with properness
  this implements the conventions-only `def-weil-pbc-scheme-conventions`.
* `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  chosen `Limits.pullback`, its projections, and the module base-change convention.
  Its imported `Mathlib.AlgebraicGeometry.Fiber` supplies `Scheme.Hom.fiber`
  and `Scheme.Hom.fiberToSpecResidueField`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`.
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
* `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, with the ordinary degree-zero
  global-sections interpretation used in the hypothesis.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`;
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, with Mathlib's `DerivedCategory.homologyFunctor`.
* `WeilConjectures.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly supplies Mathlib's
  `SheafOfModules.IsQuasicoherent`; only quasi-coherence is required here,
  not the conjunction with finite type introduced by that dependency module.
* `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, imported publicly by the recorded
  canonical pullback module.
* `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`:
  `IsDerivedModulePullbackComparison`, `IsDerivedModuleBaseChangeMap`; the
  arrow's explicit construction specializes their defining composite with
  the pinned counit and the unit identification, as explained above.
* `WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison`:
  `Scheme.Modules.canonicalSingleDirectImageMap`.
* `WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`:
  `Scheme.Modules.canonicalSinglePullbackMap` and
  `Scheme.Modules.canonicalTensorPullbackAdditive`. The two new definition nodes
  below own these constructors and the direct-image constructor. They replace
  the two invertibility-theorem ids in stmt_deps; neither invertibility theorem
  is used in the statement or the four-step proof plan, so neither is added to
  proof_deps.

All eight recorded proof-dependency modules are imported without `public`.
Their full signatures and docstrings were read, including the affine Cech
formulation recorded for `lem-pc-rf-perfect-base-change` and the localized-site
formulation of `exists_finiteFreeResidueModel`. The docstring gives all four
proof steps and explains the geometric specializations and the canonical maps.
No dependency interface is repaired or duplicated in this delivery.

Edge cases checked before writing:

* Empty base: the pointwise hypotheses and local splitting are vacuous, the
  module category is zero, and every T mapping to it is empty. All asserted
  conclusions remain valid; no artificial nonempty hypothesis appears.
* Empty fibre over a point: its dimension is minus infinity, so the dimension
  bound allows it, but the map from a nonzero residue field to zero sections
  is not bijective. Exactly the existing constants assumption excludes it.
* Dimension-zero fibres and genus zero: E can be zero and has rank zero;
  neither the finite-local-freeness predicate nor the splitting excludes this.
* Disconnected base with different genera: finite local ranks can differ on
  components. No choice of a common rank occurs anywhere in the signature.
* Nonreduced and non-Noetherian bases and nonflat base-change maps are allowed.
  Finite presentation plus properness, not a hidden base condition, is used.
* The vanishing statement includes negative cohomology, and the shift is -1,
  not +1. No global splitting is asserted.

Searches performed with the prescribed wrapper:

* LeanFinder: "For a proper flat finitely presented family with fibres of
  dimension at most one and only constant global functions the derived
  structure direct image is locally O plus a finite locally free module in
  degree one". Eight hits, concerning flatness, universal openness, and
  finite presentation; none states this structure model.
* Loogle: `AlgebraicGeometry.Scheme.Modules, DerivedCategory`. Zero hits.
* Mathlib grep: `flat.*curve.*derived|derived.*structure.*model|proper.*flat.*locallyFree`.
  Zero hits.
* LeanSearch: "A proper flat family of curves has a perfect derived structure
  direct image locally O plus a finite locally free module in degree one".
  Eight hits concerning flatness and stalks; no matching theorem.
* `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the preceding
  patterns and `flat_curve_derived_structure_model`: no matching statement.
  Exact node-id grep over `lean/WeilConjectures`: no hits.
* Searches for `structureUnit`, `unitToPushforwardObjUnit`, and the canonical
  single comparisons found the shared unit and pinned pullback constructors
  used here. The existing local degree-zero criterion and finite-free residue
  model are ingredients, not duplicates of this complete theorem.
* The four new auxiliary names and main theorem name were searched in both
  project source roots and were absent.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by NG

A separate clause-by-clause rereading of the node and completed source checked
the actual definition bodies, not merely their names. This was an in-thread
second pass; the dispatcher explicitly forbids starting another agent, and the
maintainer supplies independent review after delivery.

The pass verified the fibre's appTop direction is residue-field functions to
fibre functions, the unit is the explicit structural composite, the local H1
summand is the restriction of H1(K) itself, the shift places it in degree one,
and the normalized base-change target is the structure sheaf of the chosen
fibre product. It also checked that proper plus locally finite presentation
is finite presentation in the stated convention and that the rank is allowed
to vary. No mathematical mismatch was found. The initial compile identified
a missing terminator for the noncomputable section; that syntax defect was
repaired before the clean compile. The main statement and all helper
signatures are checked with auto-implicit variables disabled.

Repair reading (2026-10-21), with the return for immutable head ab7ba9f8967e,
retained source, current-main node, and both upstream constructor modules open:
the return's H2 finding is correct. The retained packet differed from current
main only in `lean` and the two added theorem ids in `stmt_deps`. The source
uses the plain constructors, not choices of those invertibility theorems.
I replaced those two ids by the two definition ids below. One record per
existing module keeps each declaration attached to the module that defines it.
Their combined dependencies include exactly the four foundational interfaces
requested in the return: derived pullback composition, derived pullback,
derived direct image, and the pinned module-pullback adjunction; scheme and
derived-category definitions are also cited where used.

The direct-image record's arbitrary module `M` matches the actual map's signature;
it adds no acyclicity assumption. Its formula uses the inverse single-complex
identification followed by the right-derived unit, in the source's order.
The pullback record owns both the additive abbreviation and the arbitrary-module
comparison; its formula uses the same chosen composition counit, then the
single-complex identification, then `leftAdjointUniq` from the pinned tensor
adjunction to ordinary pullback. It adds no invertibility or flatness assumption.
Both records are `existing: true`, so no source module or declaration is copied
or modified. Empty schemes, zero modules and nonflat morphisms are admitted by
both definitions. The main Lean file, its signature, hypotheses, conclusion,
proof docstring, and single `sorry` are unchanged. The original clause-by-clause
reading and edge-case assessment above therefore still apply.

## New nodes

`def-weil-pbc-canonical-single-direct-image-map` owns the already existing
`AlgebraicGeometry.Scheme.Modules.canonicalSingleDirectImageMap` in
`WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison`.
It defines `(f_*M)[0] → Rf_*(M[0])` for every module by the localized
single-complex identification followed by the right-derived unit (Stacks 079V,
`cohomology.tex`, section-unbounded). Its `lean.statement` is the exact defining
signature from that unchanged module. The old theorem node asserts invertibility
under positive acyclicity, and therefore cannot own this unrestricted notion as
a theorem dependency. No new Lean module is supplied or needed.

`def-weil-pbc-canonical-single-pullback-map` owns the already existing
`AlgebraicGeometry.Scheme.Modules.canonicalTensorPullbackAdditive` and
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackMap` in
`WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`.
It records the exact selected composition additive structure and the explicit
derived counit / single-complex / adjunction-preserving comparison composite,
for every module, without an invertibility hypothesis. Sources: Stacks 06YJ,
08HY and 0D5S, the derived-pullback construction and its base-change and
composition normalization, read in `cohomology.tex`. The exact map signature is
recorded, with both names in `lean.declarations`. No new Lean module is needed.

For both nodes the prescribed searches were repeated during repair and their
outputs are retained verbatim in `mathlib_searches`: LeanSearch for the ordinary
and derived single-module comparisons returned eight generic pullback/adjunction
hits; Loogle `Functor.rightDerivedFunctorUnit, Adjunction.leftAdjointUniq`
returned zero hits with the unknown-identifier note; Mathlib grep for the three
constructor names, `rightDerivedFunctorUnit`, and `singleMapHomologicalComplex`
returned one generic single-complex hit. Project `rg` found the existing
constructors in precisely the two upstream modules; Sheaf supplies compatibility
imports and users. A search of all DAG definition statements and `lean` records
found no definition node owning any of the three constructors. The matching
theorem nodes state invertibility instead. `tools/blueprint_refs.py search
canonicalSingle` returned zero blueprint nodes. Thus these are new ownership
nodes for existing constructions, not second definitions.

## Repair validation

The initial required dry run on the saved packet passed mechanically at
681de9d25f0. It did not address the independent review's H2 finding, so the
ownership repair above was made before delivery. The unchanged delivered Lean
file was compiled again through `scompile.py` against the live published build:
the sandbox check and library-module check were clean (15.7 s and 18.7 s).

The repaired packet's first preflight required the schema's `slopmaster2`
branch label for the two existing `WeilConjectures` declarations. Both new
records were corrected accordingly; their source modules remain the live
upstream modules compiled by the authorized wrapper. The new statements also
explicitly introduce the localization Q and the tensor-pullback functor P_f.

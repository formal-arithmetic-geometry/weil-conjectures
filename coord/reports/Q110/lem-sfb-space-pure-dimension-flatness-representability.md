## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePureDimensionFlatnessRepresentability` states
`AlgebraicGeometry.AlgebraicSpace.exists_pure_dimension_flatness_representative` with
one `sorry`. It introduces no definitions or additional theorem obligations. The node's
statement, proof and proof dependencies are unchanged. Its statement dependencies gain the
already landed `def-sfb-space-dimension-flat-condition`, whose exact all-chart predicate is
used rather than repeated.

Source read: `literature/stacks-project/spaces-flat.tex`, lines 1813–1900 (Tags 0CWS,
0CWT and the functor) and 1979–2097 (Tag 0CX1 and its descending-induction proof).
The stated result is the node's chosen specialization of 0CX1: scheme base and universal
purity, with an algebraic-space representative. The source proves more, namely a scheme
representative over a scheme base, but the delivered conclusion retains exactly the node's
algebraic-space conclusion.

Clause-by-clause correspondence:

- Absolute base and sizes: `universe u`, `Spec (CommRingCat.of (ULift.{u} ℤ))`,
  `X : AlgebraicSpace ...`, and `Y : Over ...`. These encode all schemes in the chosen
  universe over Spec Z. All scheme tests `B` are in that same universe. Over Spec Z every
  scheme has its unique structure map and every scheme morphism is a morphism over it.
  Thus the slice encoding excludes no schemes or maps in the size convention.
- Family and finite presentation: `f : X ⟶ schemeSpace Y`,
  `hf : MapIsFiniteType f`, `hlfp : MapIsLocallyOfFinitePresentation f`, and
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. Finite type unfolds to
  quasi-compactness and the local finite-type chart test. The latter follows from local
  finite presentation on each chart (Mathlib's instance in Morphisms/FinitePresentation,
  lines 108–113). Accordingly these three binders are equivalent to exactly the node's
  quasi-compact + quasi-compact diagonal + locally finitely presented condition; they do
  not add a restriction. The finite-type witness is needed as an argument of the recorded
  universal-purity definition, and `hf.1` supplies precisely the quasi-compactness clause.
- Module: `M : X.QCoh` and `[hM : SheafOfModules.IsFinitePresentation M.obj]`.
  QCoh is the recorded full subcategory of the unchanged Mathlib quasi-coherence predicate.
  The finite-presentation class means locally the cokernel of a map of finite free module
  sheaves, precisely the finite local matrix presentation in the node. Its Mathlib
  finite-type instance supplies purity's module-finiteness argument, without an assumption.
- Universal purity: `hpure : IsUniversallyPureRelativeToScheme Y f hf hqs M inferInstance`.
  This is the exact recorded definition: every scheme base change, every associated point
  and every specialization in the base admit the specified specialization lift.
- Nonnegative integer: `n : ℕ`, including zero.
- Actual base change and module pullback: `dimensionFlatCondition f M.obj n b` unfolds to
  `enlargedFibreProduct f (dimensionFlatBaseMap b)` and tensor pullback along its actual
  first projection, not an arbitrary equivalent space or module.
- Every representable etale chart and every point: the predicate quantifies over the
  full `EtaleSite` of this fibre product and every point of its underlying chart scheme.
  Its `dimensionFlatChartMap` is the Yoneda preimage of the composite with the actual
  second projection, so its image point is precisely v in the node.
- Residue-degree inequality: the predicate uses `(n : Cardinal.{u}) ≤ Algebra.trdeg`,
  with the field-algebra structure induced by the same chart map's `residueFieldMap`.
  No finite-degree or separability assumption is supplied.
- Flatness: the chart's module is restricted to Zariski opens by `schemeRestriction`,
  then stalked by `RingedSpace.moduleStalkFunctor`. `ModuleCat.restrictScalars` along
  the chart map's `stalkMap` gives its actual O_(B,v)-module; `Module.Flat` is imposed
  precisely for points satisfying that inequality. This is the node's stalk formulation
  of the recorded `Scheme.Modules.IsFlatOver` notion, rather than global flatness in all
  dimensions or flatness of the space morphism.
- Representing object and morphism: `∃ (E : AlgebraicSpace ...) (j : E ⟶ schemeSpace Y)`.
  Its first conjunct is `MapIsLocallyOfFinitePresentation j`, quasi-compactness of j,
  and quasi-compactness of its relative diagonal: exactly finite presentation.
- Monomorphism: for every test scheme `B`, `Function.Injective (j.hom.hom.app (op B))`.
- Exact functor of points: for every `b : B ⟶ Y`, existence of a section `e` with
  `j.hom.hom.app (op B) e = b` is equivalent to `dimensionFlatCondition f M.obj n b`.
  Together with injectivity this is a bijection onto the stated subset. Naturality is
  already part of the actual natural transformation j; no arbitrary bijections are
  introduced, and no separate naturality assumption is necessary.
- Neither proper support nor separatedness of f is a binder. Quasi-separatedness is
  explicitly the quasi-compact diagonal, which is required by finite presentation.

Dependency declarations read and used (all in namespace AlgebraicGeometry, with
AlgebraicSpace namespace where appropriate):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules` and full-subcategory morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  the actual pullback construction uses the first of these, the others are proof inputs.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its slice
  sheafification instances. `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` and its finite-type instance.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  defined by adjunction to the canonical chart-limit `moduleDirectImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`,
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`; `ProperCurveModuli` provides
  `MapIsQuasiCompact` with its actual affine scheme-test pullbacks.
- `Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity`:
  `IsUniversallyPureRelativeToScheme`, read in full including relative assassin and
  actual base changes; no specialization or private copy is used.
- `Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition`: `dimensionFlatCondition`,
  `dimensionFlatBaseMap`, `dimensionFlatChartMap`. Its source and node were read in full.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; `Mathlib.RingTheory.AlgebraicIndependent.Basic`:
  `Algebra.trdeg`. `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver` with its affine-section signature and stalk explanation.

The public imports expose the statement dependencies transitively, including all the
recorded APIs above. Plain proof imports are exactly the currently stated remaining proof
inputs: `EtaleSheafSpaceAtlasBootstrap`, `AlgebraicSpaceFlatProperFpLocality`,
`EtaleSchemeMapOpenImage`, and `AffineCompleteDevissageDimensionFlattening`. The other
proof-dependency nodes currently have no Lean record, so there is no module to import yet.
The docstring records all nine proof steps and their DAG inputs, including those awaiting
stage 2. There is no import cycle.

Edge cases checked against the definition and signature: n = 0 tests all points; an empty
chart has no point conditions; an empty base has the usual empty-scheme sections and is
included; empty X and the zero module make the criterion true and admit the base itself as
a representative; n greater than the universal fibre bound makes it vacuous; infinite
residue transcendence degree is covered by the cardinal inequality. No affine or
Noetherian hypothesis on Y or B, support condition, nonempty hypothesis, separation,
characteristic, finite residue-field extension or positive n has been introduced.

Searches performed:

- `msearch.py leanfinder`, query "representability of dimension filtered flatness condition
  for universally pure finitely presented quasi coherent module": 8 hits, chiefly
  `SheafOfModules.IsFinitePresentation` and its local-presentation API; no representability
  theorem. These hits led to reuse of the finite-presentation class.
- `msearch.py leansearch`, query "universally pure module flattening functor algebraic
  space finite presentation": 8 hits about module flatness and flat morphisms; no match.
- `msearch.py loogle`, query "AlgebraicSpace, Scheme, Module, Flat, Representable": unknown
  identifier AlgebraicSpace (the project notion is absent from the Mathlib search index).
  Follow-up `SheafOfModules.IsFinitePresentation`: 5 exact API hits, reused as above.
- `msearch.py grep`, query
  `flat.*dimension.*represent|dimension.*flat.*represent|pure.*flat.*represent` against
  Mathlib: 0 hits. An earlier grep mistakenly included an extra Mathlib path component;
  this successful search corrected its scope and is the one relied on.
- `rg` in the named project's `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  dimension-flat names, residue-field transcendence degree and representability:
  no existing full theorem. Found and reused the landed `SpaceDimensionFlatCondition`
  module and its owning definition node, and Q105's affine special-case theorem.
  The affine theorem requires an affine algebra complete devissage and only represents
  the condition near a specified prime; it does not state this global pure-family theorem.
- `rg` in `dag/lean_names_upstream.json` and Mathlib for the chosen new theorem name:
  no conflict. `tools/blueprint_refs.py search dimension-flat-condition`: 0 blueprint
  matches; the DAG definition node is present and landed, so no new node was made.

No node fault or STATEMENT-DISPUTED issue was found. The withdrawn CompactObject example
module and its current Mathlib-backed node were read; module/header conventions instead
follow the current stage-2 brief and the landed neighbouring modules.

Validation: `scompile.py Q110 lem-sfb-space-pure-dimension-flatness-representability
<module>` compiled the module in both sandbox and library contexts on the server with no
errors or warnings (3.9 s and 2.4 s). Every variable/universe is explicitly bound, with
`autoImplicit false`. Only the theorem's `sorry` remains. All Lean lines are at most
100 characters. Dry-run and delivery results are recorded by the prescribed wrapper.


## Second reading by Q110

Independent clause-by-clause reading (maintainer reviewer, replacing the worker's
self-check) of the node against Stacks spaces-flat Tags 0CX1, 0CWS, 0CWT and the Lean.

- Base and universes: schemes and algebraic spaces over `Spec (ULift.{u} ℤ)`, `Y`, `B : Over`
  that base. Every scheme lies uniquely over Spec Z, so no scheme or map is excluded. Same
  universe convention as the recorded purity definition. Correct.
- f of finite presentation (qc, qc diagonal, chartwise lfp): `hf : MapIsFiniteType f`
  (qc + chartwise lft), `hlfp : MapIsLocallyOfFinitePresentation f`,
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. Jointly equivalent to the node's
  condition (lfp ⇒ lft); nothing stronger. Correct.
- M finitely presented quasi-coherent: `M : X.QCoh`, `[SheafOfModules.IsFinitePresentation M.obj]`.
  Correct (finite-type instance feeds purity's argument).
- Universal purity: `IsUniversallyPureRelativeToScheme Y f hf hqs M inferInstance`, the
  recorded def-sfb-space-universal-relative-purity predicate with identical binders. Correct.
- n ≥ 0: `n : ℕ`. Correct.
- P_n(b): `dimensionFlatCondition f M.obj n b` (def-sfb-space-dimension-flat-condition,
  landed before the delivery base): actual enlargedFibreProduct with `yoneda.map b`, tensor
  pullback along the actual first projection, every étale-site chart and every point,
  `(n : Cardinal) ≤ trdeg` over the residue field of the Yoneda-preimage chart map, Module.Flat
  of the Zariski stalk over O_{B,v} via the actual stalkMap. Exactly the node's P_n.
- Conclusion: `∃ E j`, finite presentation of j as lfp ∧ qc ∧ qc diagonal (same encoding as for f);
  monomorphism as injectivity of `j.app (op B)` for every scheme B; and for every b, b lies in the
  image of `E(B)` iff P_n(b). With injectivity this is the bijection onto {b | P_n(b)}; the map is
  the actual natural transformation j. Quantifier order as in the node. Correct.
- No proper-support or separatedness binder; no Noetherian, affine or field assumption.

Edge cases: n = 0 (all points), empty B, empty X or M = 0 (condition true, E = Y), n beyond the
fibre bound (vacuous), infinite transcendence degree (cardinal inequality).
Searches: worker records plus `rg dimensionFlat|pure_dimension_flatness` in side-live
lean/Sheaf: only the landed predicate (reused) and the affine 05UF node (different statement);
no existing theorem. Records: the node differs from live only by `lean` and the added landed
definition stmt_dep; `lean.statement` is verbatim the file's signature; imports are the
statement owners plus proof_deps modules present in side-live. Docstrings carry source, blueprint
id and all nine proof steps; proof is `sorry`. No Lean change.

## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeDerivedEtaleQCohComparison` states
`AlgebraicGeometry.Scheme.Modules.scheme_derived_etale_qcoh_comparison` with a whole-proof
`sorry`. All other declarations contain real data: one canonical counit-mate natural
transformation, ordinary terminal evaluation on the small étale site, and a record of
precisely specified derived-global-sections witnesses. The ownership repair reuses the now-landed equivalence definition node and records
existing definition ownership for the comparison square; no duplicate definition is retained.

Source reading: spaces-perfect.tex, Lemma `lemma-derived-quasi-coherent-small-etale-site`
(Tag 071Q), including its proof that restriction is the quasi-inverse, and Remark
`remark-match-total-direct-images` (Tag 08GH), including its qcqs direct-image square.
The final assertion follows by the K-injective adjunction argument of derived.tex 08BJ.
The current blueprint is `literature/blueprint/latest` (COMMITS records ef6f9619 for
2026-10-24). This supporting item has no independent blueprint unit statement.

Clause-by-clause reading:

* Every scheme Z: `∃ d : ∀ T : Scheme.{u}, DerivedEtaleZariskiEquivalenceData T`.
  There is no quasi-compactness, separatedness, Noetherian, nonempty or boundedness
  binder on T. Explicit universes `u w a` and the families of `HasDerivedCategory.{w}`
  assumptions implement the recorded size convention and localization choices; the
  abelian target localization has its independent morphism universe `a`.
* Module sheaves on the Zariski and small étale sites are the shared
  `SheafOfModules.{u} (moduleRings T.toRingedSpace)` and `SmallEtaleModules T`.
  The latter is the existing `SheafOfModules.{u} (smallEtaleModuleRing T)`.
  No auxiliary algebraic space is quantified over: the statement's theorem concerns
  schemes, and the algebraic-space dependencies explain the small étale convention.
* The ringed-site map epsilon, exact module pullback and structure module:
  `(d T).context` is the existing `ZariskiEtaleModuleContext T`, whose restriction
  is `zariskiEtaleModuleRestriction` and whose extension is the canonical sheafified
  tensor pullback. `(d T).exact_limits` and `.exact_colimits` state exactness on
  all modules. `.structure_iso` is invertibility of the actual multiplication map
  `.context.structureMap`, not an arbitrary identification of structure modules.
* Unbounded derived QCoh equivalence and inverse: `.extension_factors` identifies
  extension with termwise exact pullback after Qh. `.restriction_derived` is the
  right-derived universal property of restriction and `.restriction_injective`
  specifies computation on every K-injective. `.extension_qcoh` and
  `.restriction_qcoh` preserve the full cohomological QCoh predicates;
  `.unit_iso` and `.counit_iso` make the actual normalized derived adjunction an
  equivalence on those full subcategories. Quasi-coherence is the shared
  `schemeDerivedQCohProperty` / Mathlib `IsQuasicoherent` in every integer degree;
  it does not require quasi-coherent terms in a representative.
* For each morphism v: `∀ (Z W : Scheme.{u}) (v : Z ⟶ W), QuasiCompact v →
  QuasiSeparated v → ∃ s : DerivedEtaleZariskiSquareData v (d Z) (d W), ...`.
  These two hypotheses apply only to the direct-image clause. The existing square
  data has the actual small-étale pushforward, its right-derived universal property,
  K-injective computation and preservation of QCoh. Its Zariski functor is the
  shared `schemeDerivedDirectImage v`. Its ordinary square is normalized by
  `gabberPreimageEtaleIso`, and its derived pullback/adjunction comparisons by their
  representative equations.
* The canonical direct-image comparison is the real definition
  `DerivedEtaleZariskiSquareData.directImageComparison`. It inserts
  `s.adjunction.unit`, applies `s.comparison.inv` and then the Zariski derived
  counit. Its component is exactly the arrow already appearing in the existing
  square field `.pushforward_comparison_iso`. The conclusion
  `∀ K, schemeDerivedQCohProperty Z K → IsIso (s.directImageComparison.app K)`
  makes it a natural isomorphism on the full unbounded QCoh subcategory.
  Naturality is intrinsic to the natural transformation, not extra objectwise choices.
* Derived global sections: `∀ T, Nonempty (SchemeEtaleZariskiDerivedSectionsData T (d T))`.
  This record's `.zariski` and `.etale` have their right-derived units and universal
  properties, as well as unit-isomorphism assertions on every K-injective complex.
  Zariski ordinary sections use the existing `RingedSpace.globalSectionsFunctor`
  followed by forgetting to abelian groups. Étale ordinary sections are evaluation
  of the underlying abelian sheaf at `op (Etale.mk (𝟙 T))`, with no coefficient lift.
  `.ordinary_sections` fixes the ordinary comparison to restriction along the map
  `T.topIso.inv : T ⟶ (⊤ : T.Opens).toScheme` in the étale site.
  `.comparison : (d T).restriction ⋙ zariski ≅ etale` and
  `.comparison_representatives` require exactly the same comparison on homotopy
  representatives. This is the asserted RΓ_Zar R epsilon_* = RΓ_et comparison.
  Whisker the equivalence unit with RΓ_Zar and then whisker this comparison with
  `(d T).extension` to obtain RΓ_Zar F ≅ RΓ_et epsilon^* F on QCoh. Taking H⁰
  recovers the recorded zeroth-hypercohomology convention.
* K-flat computation of derived tensor pullback is inherited from the canonical
  square's `.pullback_derived`, `.pullback_counit` and its representative comparison,
  using the same shared derived-pullback API. No substitute arbitrary functor is used.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.structureSheaf`, `.Modules` (imported through its QCoh module).
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Qh` and homology functors.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, not another module category.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and the shared
  `SheafOfModules.IsQuasicoherent` local-presentation predicate.
* `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, used in the section record and existing equivalence.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the K-flat framework (imported
  as the recorded resolution convention; no new tensor or K-flat notion).
* `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, the H⁰ RΓ convention.
  Its max-universe implementation is not incorrectly specialized to the actual
  small étale site with section universe u: our record specifies RΓ by the same
  universal property and terminal-section K-injective computation in universe u.
* `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  (proof dependency; imported without `public`).
* `Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence`:
  `DerivedEtaleZariskiEquivalenceData` and
  `ZariskiEtaleModuleContext.structureMap` are owned by the now-landed
  `def-sfb-derived-etale-zariski-equivalence-data` (NJ, existing:true).
  `DerivedEtaleZariskiSquareData`, `smallEtaleStructureMap`, and the square's
  `ordinaryPullbackHomotopy` and `ordinaryPullbackComplex` helpers are recorded by
  the new existing:true `def-sfb-derived-etale-zariski-square-data`. Both definition
  nodes are in stmt_deps. The module is publicly imported for these plain data
  declarations. Its theorem `derived_etale_zariski_equivalence` remains solely a
  proof dependency; its conclusion does not occur in the statement.
* `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.globalSectionsFunctor` and its additive instance.
  Added its already landed owning definition node to stmt_deps to use the canonical
  global-sections functor with the shared sheaf-module category instance.

Edge cases checked: the empty scheme and zero complexes are admitted; all cohomology
indices range over ℤ; no lower/upper bound occurs. Non-qcqs schemes are allowed in
the equivalence and sections clauses. Only v is assumed qcqs for direct images;
no separatedness or finite-type assumption occurs. Identity morphisms are included.
The ordinary terminal comparison uses the isomorphism of the top open subscheme
with T, rather than silently treating these different objects as equal. Sections
stay in u on the small étale site, whose objects lie in u+1 and arrows in u;
there is no equation forcing w or a to equal either of these universes. Explicit
category carriers avoid introducing the separate bundled `T.Modules` category instance.

Searches (2026-10-24):

* msearch leanfinder, query `Unbounded Zariski etale comparison derived quasi coherent
  modules global sections`: only unrelated general module/quasi-coherence hits;
  no theorem including the unbounded global-sections comparison.
* msearch loogle, query `DerivedCategory, SheafOfModules`: no exact match.
* msearch grep, query `etale.*quasicoherent|quasicoherent.*etale|derived.*[Zz]ariski`:
  no exact Mathlib comparison theorem.
* msearch leansearch, query `Zariski etale derived quasi coherent comparison global
  sections`: eight hits about ordinary structure-sheaf global sections, not the theorem.
* rg on `lean/WeilConjectures` and `lean/Sheaf` with the same patterns, and with
  `EtaleZariski|etaleZariski|ZariskiEtale|SmallEtaleModules`: found the landed Q65
  equivalence and square, reused here. `EtaleZariskiDerivedSectionsAcyclicLeray`
  concerns bounded-below ordinary abelian-sheaf cohomology, not unbounded module RΓ.
* rg of the item id in `lean/WeilConjectures`: no existing implementation.
  rg of proposed fully qualified names in the source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collisions. Existing terminal-section APIs for
  constant-coefficient sheaves have a different coefficient category; ours directly
  evaluates the already existing structure-module sheaf.

No mathematical statement correction or disputed statement is needed. The records
in the existential conclusion describe witnesses without selecting arbitrary objects
from a sorried existence theorem. All theorem proofs are exactly `by sorry`, and
all definitions have real data. Every helper has source and blueprint docstrings.

## Returned delivery repair

The immutable head reviewed was `455eae2115cb`. The return says the proposed new
`def-sfb-derived-etale-zariski-equivalence-data` already exists on sheaf-dag.
I read that current node: NJ's landed existing:true owner names only
`DerivedEtaleZariskiEquivalenceData` and `ZariskiEtaleModuleContext.structureMap`,
from the original `Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence` module.
It does not own the square. I read the full signatures, fields and docstrings of
both records, the structure maps and both helpers in that original module, and
read current server source with scompile.py --source.

The repair removes the colliding new-node copy and both extraction modules, and
removes the lean-only repair of the existence theorem node. The item now imports
the published original module and cites NJ's existing definition node unchanged.
The new existing:true square owner below covers the remaining declarations. Thus
no landed node is overwritten and no declaration is redeclared or moved. The item
signature and all mathematical clauses are unchanged from the reviewed head; only
its public import and ownership dependencies change. The item node is regenerated
from the current read-only base, changing only lean and permitted stmt_deps.

## New nodes

`def-sfb-derived-etale-zariski-square-data` is an existing:true definition owner
for four plain declarations in the already published
`Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence`; it has no new Lean file.
It cites the landed equivalence-data owner and the foundational definitions needed
by the fields. Sources: Stacks spaces-perfect.tex Tag 08GH, both comparison squares,
and descent.tex Tag 03FH, canonical scalar extension and structure multiplication.
No existence theorem conclusion is owned or asserted.

Every clause of the new definition is rendered as follows:

* Schemes U,T and h are explicit binders, and dU,dT use the landed equivalence data.
  The original explicit independent u,w and HasDerivedCategory families are retained.
* `rightAdjoint`, `ordinary_right`, `ordinary_right_sections` give the ordinary
  adjunction and canonical base-change restriction on opens. The bracketed fields
  retain the four ordinary additivity witnesses and pushforward additivity.
* `pullback`, `pullback_counit`, `pullback_derived` give the left-derived functor;
  `zariski_counit`, `zariski_derived`, `zariski_normalized` pin the Zariski side.
* `pushforward`, `pushforward_unit`, `pushforward_derived`,
  `pushforward_injective` give the right-derived functor and its computation on all
  K-injective complexes; `adjunction` and `adjunction_normalized` fix transposition.
* `comparison` is the natural pullback iso, and `comparison_representatives` is its
  prescribed ordinary scalar-extension and counit equation.
* `pullback_qcoh` preserves QCoh in all integer degrees; `pushforward_qcoh` and
  `pushforward_comparison_iso` have only the stated qcqs hypotheses on h. The latter
  uses the actual unit--inverse-comparison--counit composite, not an arbitrary map.
* `smallEtaleStructureMap` is the real adjoint scalar-multiplication definition;
  `structure_iso` and `structure_compatibility` express its invertibility and the
  square's compatibility with the actual structure maps.
* `ordinaryPullbackComplex` and `ordinaryPullbackHomotopy` are the termwise ordinary
  functors with the square's additivity witness. Their data is not sorry.

Searches for this owner: msearch leansearch `Canonical derived etale Zariski
pullback direct image comparison square data` returned eight ordinary pullback
results, no derived square. msearch leanfinder `Derived etale Zariski pullback
comparison square data` returned eight ordinary etale-site/morphism results.
msearch Mathlib grep `DerivedEtaleZariskiSquareData|smallEtaleStructureMap` returned
zero hits. `blueprint_refs.py search 'derived etale zariski square'` returned zero
blueprint nodes. rg in lean/WeilConjectures, lean/Sheaf and the upstream index found
these definitions only in the published original module. rg in dag/nodes found
only the original theorem's declaration list; NJ's definition owner has neither
square nor smallEtaleStructureMap. The new node stores the exact query outputs.
Reuse as existing:true supplies the missing owner without copying a notion.

Edge cases of the existing record were rechecked: U and T may be empty, h may be an
identity or any morphism, no global qcqs assumption occurs, all cohomology indices
range over integers, and qcqs appears only in the pushforward fields. The witness
type asserts no existence. No statement correction or disputed statement is needed.

## Dependency modules

None in this repair. The returned extraction and dependency theorem-module repair
are removed; published definitions and theorem are used from their original module.
The landed equivalence owner is not included among files of this delivery.

## Second reading by Q03

This is a self-reading; no independent worker was started because dispatch forbids
other agents. The maintainer performs the independent review. The current landed
owner was checked against the full record. The new existing:true owner was checked
against every square field and helper above. The item theorem signature is unchanged
from the returned version and the mathematical checks of that review still apply.
Only one module is delivered, containing the original actual counit mate and
sections constructions, with only the theorem proof postponed by sorry.

Validation: scompile.py compiled the item both as sandbox (6.9 s) and named library
module (6.5 s), with no diagnostics. The current source read through --source
matches the read clone. The item signature matches lean.statement verbatim; only
lean and permitted stmt_deps differ from current base. deliver2.py --no-push passed preflight, the existing-declaration probe and per-file
compilation at dry-run commit `a2bff92cbc6`; nothing was pushed by that run.

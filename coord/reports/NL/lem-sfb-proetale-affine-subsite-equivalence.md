## Worker report

Repair of the returned stage-1 head 98653b3d3d5b (H1/H2/H11). The starting sandbox was
empty. I read the current item, every statement dependency and its recorded declaration,
the six proof steps, and their recorded proof interfaces. This delivery contains a real
stage-2 module and a node changed only in `lean`; it does not re-push the split commit.
There is no new node, dependency repair, statement correction, or disputed statement.

Module: `Sheaf.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence`.
Main declaration:
`AlgebraicGeometry.Scheme.ProEt.affineWeaklyEtale_sheafEquivalence`.

Each hypothesis and clause of the item is rendered as follows:

- "Let X be any scheme": `(X : Scheme.{u})`. There is no affineness,
  quasi-compactness, quasi-separatedness, Noetherian, or nonemptiness assumption on X.
- "Its small pro-etale site": the recorded `Scheme.ProEt` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, with `ProEt.topology X` and
  `ProEt.precoverage X`. Its objects are weakly etale maps to X, with all X-morphisms.
  I opened its full definition and docstring, including the comap definition of the
  topology's generating precoverage. This is the current recorded interface of
  `def-weil-pbc-proetale-site`, repaired upstream on 2026-10-17.
- "Compatible universes and skeletons": neither category is replaced by an arbitrary
  small site. `AffineWeaklyEtale X : Type (u + 1)` inherits `Category.{u}` from
  `X.ProEt`. Sets are `Type (max (u + 1) v)` for arbitrary explicit universes u, v.
  Thus the object and hom universes are not forced equal, and sets are large enough
  for a compatible skeleton of either category. These are the recorded site's full
  universes, not a smaller Type-u surrogate.
- "The full subsite whose objects are affine weakly etale maps": `affineSource X`
  is `fun U : X.ProEt ↦ IsAffine U.left`, and `AffineWeaklyEtale X` is its
  `ObjectProperty.FullSubcategory`. In particular affineness means the source U is
  affine, not that the structure map U → X is an affine morphism. Morphisms are all
  X-morphisms, via the full-subcategory category instance.
- "Standard coverings, finite families ... satisfying the covering condition":
  `affineWeaklyEtalePrecoverage X` is
  `Precoverage.finite _ ⊓ (ProEt.precoverage X).comap (affineWeaklyEtaleInclusion X)`.
  `Precoverage.finite` means the set of distinct arrows of the presieve is finite;
  `comap` means its image presieve belongs to the recorded pro-etale precoverage.
  This is exactly the finite-family convention up to removal of repetitions, which
  does not change the sheaf condition. On affine targets this is equivalent to
  finite joint surjectivity, as proved in step 2 of the node. The topology is the
  generated Grothendieck topology, by `Precoverage.toGrothendieck`.
- "Restriction along the inclusion": `affineWeaklyEtaleInclusion X` is the actual
  `ObjectProperty.ι`, with real object and arrow data. The conclusion's natural
  isomorphism identifies `e.functor`, after `sheafToPresheaf`, with
  `sheafToPresheaf (ProEt.topology X) ... ⋙
  (Functor.whiskeringLeft _ _ ...).obj (affineWeaklyEtaleInclusion X).op`.
  This fixes both sections and natural transformation components to restriction;
  the conclusion is not merely an unrelated equivalence of abstract categories.
- "Induces an equivalence of topoi": the existential `e : Sheaf ... ≌ Sheaf ...`,
  together with that natural isomorphism, states that restriction is an equivalence
  of sheaf categories. Every category equivalence preserves finite limits and is
  adjoint to its quasi-inverse, so it gives precisely an equivalence of topoi.
  There is no arbitrary comparison map or extra continuity hypothesis.

All five helper definitions/abbreviations contain real data, have source/blueprint
references, and are listed in `lean.declarations`. They express the affine subsite
introduced in this item's own statement, as expressly allowed for owning-node helpers
in the launcher brief. The sole postponed theorem is the item's theorem, with its
matching node and all six proof steps in its docstring. No other theorem is introduced.

Statement dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (the exact category used by `X : Scheme.{u}`).
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.precoverage`, `ProEt.topology`.
- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its docstring retains the
  `Sheaf J.toGrothendieck` convention used here. No second sheaf definition is made.

All stated proof dependencies are imported non-publicly, with their declarations read:

- `Sheaf.AlgebraicGeometry.EtaleComparison`,
  `AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison` (first conjunct).
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`,
  `AlgebraicGeometry.weaklyEtale_stability` (composition and base change).
- `Mathlib.AlgebraicGeometry.AffineScheme`, `Scheme.isBasis_affineOpens`.
- `Mathlib.AlgebraicGeometry.Pullbacks`, `pullbackSpecIso` and its projection lemmas.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `isAffineHom_of_isAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, its open-immersion instance.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`, the three fpqc covering-axiom instances.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`,
  `Functor.IsSpecialCocontinuousForCoverings`.
- `Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`,
  `CategoryTheory.specialCocontinuous_sheafEquivalence`.

The last general comparison currently uses SmallCategory for both sites. It is only
an imported proof tool, not a binder or definition in this statement. The proof
plan explicitly calls for compatible enlargement/transport of hom universes or the
Mathlib dense-subsite comparison, rather than identifying u and u+1. No unusable
statement dependency is being hidden by an additional size assumption.

Edge cases checked against the definitions and the source:

- Empty base and empty affine source are allowed. The empty presieve is finite
  and its image covers an empty target in the pro-etale precoverage. Both sheaf
  conditions consequently force the appropriate singleton sections.
- A nonempty target is not covered by the empty presieve.
- Infinite pro-etale covers of an affine target still admit finite affine
  refinements; the original site has not been restricted to finite covers.
- Repetitions and arbitrary reindexings of the same finite presieve do not change
  coverings or sheaves. The code imposes no incorrect indexed-composition class.
- Non-quasi-compact and non-quasi-separated bases are allowed. The pullbacks used
  for standard covers are over an affine target, not necessarily over X.
- Affine weakly etale objects need not have a chosen ind-etale presentation. The
  narrower upstream `Scheme.AffineProEt` was explicitly rejected as a match.

Sources opened: `literature/stacks-project/proetale.tex`, definition-standard-proetale
(Tag 098E, line 2233) and lemma-alternative (Tag 098W, line 2696), including the proof.
The latter's display contains `affine, etale`, but the definition and both sides of
its equivalence say `affine, proetale`; this is the source typo already identified in
the stage-1 review. The node correctly says affine proetale and requires no correction.

Searches made this repair (2026-10-18):

- `msearch.py leanfinder`: "Restriction of sheaves from the small pro-etale site to
  affine weakly etale objects with finite covering families is an equivalence".
  Eight hits: generic `Functor.IsDenseSubsite.sheafEquiv`, affine Zariski and affine
  scheme equivalences, etale forget functors; no exact match.
- `msearch.py loogle`: `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`.
  Six hits, all generic dense-subsite/equivalence APIs; no site-specific theorem.
- `msearch.py leansearch`: "Full subcategory of affine weakly etale schemes over a
  scheme with finite jointly surjective covering families". Eight hits: AffineScheme,
  affine covers, small etale topology and other generic definitions; no exact match.
- `msearch.py grep`: `AffineProEt|affine.*[Ww]eak|sheafEquiv` in
  `AlgebraicGeometry/Sites`. Six hits, affine etale/Zariski and constant sheaves.
- `rg` in the named Mathlib, upstream WeilConjectures, and both shared Lean trees:
  no occurrence of any of the six proposed declaration names.
- `rg` for affine subsites/weakly etale terminology in the project and DAG finds
  this node and its consumers, not an already-defined full affine weakly etale site.
- `rg` for the node id in upstream WeilConjectures: no hit.
- Read upstream `AlgebraicGeometry/ProEtale/Comparison/Affine.lean` at its
  `AffineProEt` definition and `isEquivalence_sheafPushforwardContinuous_toProEt`.
  They use pro-(affine etale) structure maps, so cannot be recorded as existing
  for the full affine weakly etale subsite. This repairs the return's explicit concern.
- `scompile.py --source Mathlib.AlgebraicGeometry.Sites.Proetale` confirmed the
  current published source agrees with the recorded dependency used here.

Validation: the sole delivered file passed `scompile.py NL
lem-sfb-proetale-affine-subsite-equivalence <file>` as both sandbox and library module
with no diagnostics (1.8 seconds each). No lake/global build was run.

## Second reading by NL

This is a separate author self-reading of the finished node and file; the maintainer
provides the independent reading. No second agent was started, as the dispatch brief
forbids it. I compared every hypothesis/clause again with the source rather than
reusing the stage-1 report.

The binder X is arbitrary and its exact recorded site is used. I checked that
`affineSource` tests `U.left`, not U.hom; that `ObjectProperty.FullSubcategory` gives
all X-morphisms; that finite and pro-etale covering conditions are intersected on
the affine category; and that the topology is generated from those actual covers.
The theorem uses sets (not module or abelian sheaves) and its natural isomorphism
pins down the equivalence functor on both objects and morphisms as restriction.
All universes are explicitly bound, with no extra site universe equality. The
existential equivalence and the natural isomorphism add no geometric assumption.

I rechecked the six-step docstring against each of the six node steps: affine-open
cover density; identification of finite standard covers; covering pullbacks and
continuity; finite refinement and cocontinuity; local fullness/faithfulness; and
03A0 with the restriction identification. The empty cover and arbitrary base cases
remain included. I found no statement mismatch. The return's H1/H2/H11 defects
are repaired by the actual module, complete `lean` record, these two report sections,
and the clean per-file compile. Nothing outside the permitted `lean` field changed.

Resumed packet self-check (2026-10-18): the required initial dry run compiled the
saved module, but rejected the commit because its base already contained the identical
module, leaving only the node record changed. I retained every definition and the
theorem signature, and added the module docstring's declaration index required by
brief-stage2 §3. This makes the module part of the repair commit. I reread Tags 098E
and 098W and the three statement dependency records: arbitrary schemes, all affine
weakly étale sources, finite standard covering presieves, and the natural restriction
isomorphism still match clause by clause. The empty base and empty covering remain
allowed. There is no repair note for this item and no mathematical change.

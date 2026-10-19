## Worker report

The module `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus` states
`AlgebraicGeometry.proetale_qcqs_fp_section_calculus`. Its only proof is `sorry`.
No definitions, new nodes, dependency replacements, or statement corrections are needed.

Hypothesis and clause correspondence:

- The scheme X is `(X : Scheme.{u})`; the weakly etale object V → X is
  `(V : X.ProEt)`, using the recorded small-pro-etale-site Mathlib match.
- Quasi-compactness and quasi-separatedness of V are `[CompactSpace V.left]`
  and `[QuasiSeparatedSpace V.left]`. No such assumption is imposed on X or on V → X.
- The size convention is explicit: schemes in universe u, coefficient carriers and
  filtered index category in u+1. The site has objects in u+1 and arrows in u.
  Universes can be enlarged; no independent undersized index universe is used.
- Every small filtered diagram is quantified by `(I : Type (u+1)) [SmallCategory I]
  [IsFiltered I]` and `∀ F : I ⥤ Sheaf ... AddCommGrpCat.{u+1}`. IsFiltered includes
  nonemptiness, common targets, and equalization of parallel arrows.
- The sheaves live on `Scheme.ProEt.topology V.left`, precisely V_proet, not X_proet.
  The terminal object `Scheme.ProEt.mk (𝟙 V.left)` is V itself on that site.
- The section comparison is `Function.Bijective (colimit.post F E)` where
  `E = (sheafSections ... AddCommGrpCat).obj (op (Scheme.ProEt.mk (𝟙 V.left)))`.
  This is the map from the abelian-group colimit of sections to the sections of the
  sheaf colimit, coerced to its underlying function. Bijectivity has exactly the
  requested set-theoretic meaning.
- An arbitrary commutative ring sheaf A is `Sheaf ... CommRingCat.{u+1}`.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` only forgets commutativity, as
  the dependency's `ringedSiteModules` accepts a RingCat-valued sheaf.
- P and every N_i belong to the dependency's `ringedSiteModules.{u+1}` over this
  same ring sheaf. This transparent abbreviation is exactly SheafOfModules.
- `[SheafOfModules.IsFinitePresentation.{u+1,u,u+1} P]` is Mathlib's local finite
  presentation: a family covering the terminal object, with presentations on each
  slice and finite generator and relation index sets. Finite sets are equivalent
  to Fin n, including n=0; thus this is locally coker(A^m → A^n), exactly as required.
  It imposes no global presentation or constant-rank assumption.
- The second comparison is `Function.Bijective (colimit.post N (coyoneda.obj (op P)))`.
  Coyoneda is Hom(P,-), acting by postcomposition, so its target is precisely
  Hom_A(P,colimit N), and its source is the set colimit of Hom_A(P,N_i).
- Both colimits of sheaves are `colimit F` and `colimit N`, formed in their respective
  sheaf categories. They are not presheaf or sectionwise colimits.
- `colimit.post` is defined as `colimit.desc` on the image of the chosen colimit
  cocone. The identity `colimit.ι_post` says that its composite with each source
  coprojection is exactly the evaluated (or postcomposed) given sheaf coprojection.
  Hence the comparisons are the maps specified by the node, not arbitrary bijections.
- The two additional equivalences quantify sections at arbitrary stages i,j and
  module maps at arbitrary stages i,j. Equality after the chosen coprojections is
  equivalent to `∃ k (a : i ⟶ k) (b : j ⟶ k), ...` equality after transition along
  those arrows. This explicitly renders the node's common-later-stage clause for
  general filtered categories, not only directed posets.

Dependencies used (full declarations and docstrings were read in their sources):

- `Mathlib.AlgebraicGeometry.Scheme`: AlgebraicGeometry.Scheme and Scheme.Hom.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: Scheme.ProEt, ProEt.mk, ProEt.topology.
- The scheme-conventions and size-convention nodes introduce no new declaration;
  their properties and universes are expressed by the binders above.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (the recorded module):
  CategoryTheory.Sheaf and CategoryTheory.sheafSections (defined in its Sheaf import).
  No cohomology is used, since this node concerns sections only.
- `Sheaf.CategoryTheory.RingedSiteModules`: CategoryTheory.ringedSiteModules.
- `Mathlib.CategoryTheory.Limits.HasLimits`: colimit, colimit.ι, colimit.desc,
  colimit.post, and IsColimit; `Mathlib.CategoryTheory.Filtered.Basic`: IsFiltered.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  SheafOfModules.IsFinitePresentation and its QuasicoherentData/Presentation definitions.

Imports for the proof plan (non-public):

- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`:
  Sheaf.hasExactColimitsOfShape, recorded as the abelian-colimits Mathlib match.
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`: sheafifyComposeIso
  and sheafComposeIso_hom_fac, the underlying-sets dependency.
- `Sheaf.Paper.SiteSheafificationSectionsLocal`: sheafification_sections_local.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`:
  moduleSheaves_colimits_forgetful.
- `Sheaf.Paper.SiteRestrictionExact`: siteRestriction_exact.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: SheafOfModules.homObj.
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`:
  colimitLimitToLimitColimit_isIso and filtered_colim_preservesFiniteLimits.
- The finite-covering and qcqs-permanence dependencies use the recorded Mathlib
  Proetale/QuasiCompact/QuasiSeparated declarations already imported above.
  The qcqs-site-limits dependency has no statement module yet, so no import exists.
  No available proof dependency is omitted to avoid a cycle.

Source and edge-case checks:

Read the local Stacks sources sites.tex, lemma-directed-colimits-sections (0738),
sites-modules.tex, lemma-hom-finite-presentation-colimit (0GMZ) and
lemma-finite-presentation-quasi-compact-colimit (0GN0), and proetale.tex,
lemma-proetale-affine (098D). They give finite affine refinements and section
continuity, followed by the local finite-presentation kernel argument and gluing.
All eight DAG proof steps are retained in the declaration docstring, including
finite overlaps, sheafification, common-stage bookkeeping and Hom separation.
The new module-object framework was read at its exact group-clone paths and
coord/pefw-upstream-framework.md: it does not replace arbitrary ring-sheaf modules
by condensed coefficient module objects for this general calculus statement.

Checked empty V: the empty cover forces sections and Hom to have one element;
filteredness supplies a stage. Empty filtered categories are correctly excluded
by IsFiltered. Zero P and presentations with zero generators or zero relations are
included by IsFinitePresentation. No nonzero-ring, nonempty-scheme, affine,
Noetherian, constant-rank, separated-base, or transition-injectivity hypothesis
has been added. Non-poset filtered categories are included with explicit arrows
and eventual equality. There is no known statement dispute.

Searches made:

- msearch.py leanfinder: “Sections and Hom from locally finitely presented modules
  on qcqs pro etale schemes commute with filtered colimits”: eight hits, including
  Presentation.map, Presentation.isColimit and presheaf colimit formulas; none is
  the node's section/Hom comparison theorem.
- msearch.py loogle `SheafOfModules.IsFinitePresentation`: five hits; the class
  docstring exactly matches the needed local finite presentation notion.
- msearch.py grep `IsFinitePresentation|colimitComparison` in
  Algebra/Category/ModuleCat/Sheaf: five hits, all finite-presentation definitions
  and their instances; no comparison theorem.
- rg in upstream WeilConjectures, group-clone lean/Sheaf and the new module-object
  framework for `proetale_qcqs_fp_section_calculus|qcqs_fp_section|section_calculus|
  IsFinitePresentation.*[Cc]olimit|[Cc]olimit.*IsFinitePresentation`: no matching
  theorem. Broader rg searches for IsFinitePresentation found presentation
  transport and scheme-module cohomology results, not this general assertion.
- rg for the exact DAG id in upstream WeilConjectures and lean/Sheaf: no hits.

Validation: scompile.py compiled the final module cleanly on the server with nice 19,
two threads and the fixed 60-second per-file limit (2.7 seconds for this module).
Explicit universe levels on IsFinitePresentation resolve elaboration; no local
instances, hidden hypotheses, custom objects, or increased compiler limits remain.


## Second reading by NN

I independently read the node, its eight proof steps, the submitted module,
all statement-dependency nodes and the source declarations they record. No
mathematical mismatch was found; the Lean and node signature are unchanged.

The node's object/hypothesis/conclusion inventory and correspondence are:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})` | Exact; no base-field or finiteness assumption. |
| Weakly etale V over X, in the small site | `(V : X.ProEt)` | Exact: `Scheme.ProEt` is `MorphismProperty.Over @WeaklyEtale ⊤ X`. |
| V quasi-compact and quasi-separated | `[CompactSpace V.left] [QuasiSeparatedSpace V.left]` | Exact properties of the source scheme; no extra property of X. |
| Size convention | Site schemes at u; coefficient carriers and I at u+1 | The site objects fit u+1 and arrows fit u; coefficients and filtered colimits use the containing universe. No independent undersized test/index universe. |
| Every small filtered diagram | `(I : Type (u + 1)) [SmallCategory I] [IsFiltered I]`, then universal F and N | Includes arbitrary arrows and parallel-arrow equalization, not just posets. Sharing the universally quantified I between the two conjuncts is logically equivalent to separate quantification. |
| Abelian sheaves on V_proet | `F : I ⥤ Sheaf (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1}` | Exact; this is V's site, not X's site. |
| Evaluation at V | `(sheafSections ...).obj (op (Scheme.ProEt.mk (𝟙 V.left)))` | The identity object is terminal, so this is precisely F_i(V). |
| Canonical section comparison bijective | First `Function.Bijective (colimit.post F ...)` | Exact: `colimit.post` is `colimit.desc` applied to the evaluated colimit cocone. It is an abelian-group map whose underlying function is asserted bijective. |
| Arbitrary commutative ring sheaf A | `A : Sheaf (Scheme.ProEt.topology V.left) CommRingCat.{u + 1}` | Exact, including the zero ring. |
| P and N are A-module sheaves | `ringedSiteModules` applied to `sheafCompose ... (forget₂ CommRingCat RingCat)` | Exact recorded dependency: transparent abbreviation for `SheafOfModules`; forgetting commutativity retains the same ring and module operations. |
| P locally coker(A^m to A^n), finite m,n | `[SheafOfModules.IsFinitePresentation.{u + 1, u, u + 1} P]` | Exact: read `QuasicoherentData`, `Presentation`, `Presentation.IsFinite`, and `IsFinitePresentation`. They give a family covering the terminal object and finite generators and relations on slices. Finite index types can be enumerated by Fin n. |
| Canonical global Hom comparison bijective | `Function.Bijective (colimit.post N (coyoneda.obj (op P)))` | Exact: coyoneda is Hom(P,-) into sets, with postcomposition on arrows. No internal-Hom comparison substituted. |
| Both comparisons use given coprojections | `colimit.post` and `colimit.ι` | Confirmed from `HasLimits.lean`: `colimit.ι_post` identifies each composite with the mapped coprojection. No arbitrary equivalence is used. |
| Equality of representatives at a common later stage | Both explicit iff clauses, with `∃ k (a : i ⟶ k) (b : j ⟶ k)` | Exact for section elements and module morphisms, including different starting indices. |
| Colimits are sheaf colimits | `colimit F` and `colimit N` inside `colimit.post` | Computed in the sheaf/module-sheaf categories. The source Hom colimit is in sets; section colimit is in abelian groups, with its underlying filtered set-colimit meaning. |

Source check: read sites.tex, lemma-directed-colimits-sections (0738),
including all four hypotheses and its finite-cover/overlap proof; sites-modules.tex,
lemma-hom-finite-presentation-colimit (0GMZ) and
lemma-finite-presentation-quasi-compact-colimit (0GN0), including the ringed-site
hypotheses and local finite-presentation reduction; proetale.tex,
lemma-proetale-affine (098D), including finite affine refinements and the adjacent
covering definitions. No Noetherian, separated-base, nonzero-ring, injective
transition-map, or global finite-presentation hypothesis occurs. The node's
finite affine covers with qcqs overlaps provide the source's site compactness
conditions. All eight proof steps occur in order in the theorem docstring.

Dependency check: opened `RingedSiteModules.lean`, the Mathlib Proetale module,
the definition of `sheafSections`, `IsFiltered`, and `colimit.post`, and the
finite-presentation structures listed above. Also opened the recorded module
forgetful/colimit and exact slice-restriction declarations and the upstream
internal-Hom declaration. The qcqs-site-limits proof dependency has no Lean
module yet and therefore needs no import in this statement delivery. There are
no new definition nodes or dependency replacements in this delivery to audit.
No statement correction is needed, so there are no corrected-statement citers.

I read `coord/pefw-upstream-framework.md` and the exact group-clone framework
`ConstructibleSheaf/ProEtaleModule/Def.lean`, notably
`AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented`, and the coefficient
construction declarations in `ModuleObject/Basic.lean`. Those describe internal
module objects in an ambient coefficient category; this item uses arbitrary
ordinary ring sheaves and the recorded general ringed-site module category.
No framework declaration states this complete section/global-Hom calculus.

Edge cases: an empty V is allowed; its empty covering forces unique sections
and module maps, and IsFiltered supplies a representative stage. The empty
index category is correctly excluded by IsFiltered, whose definition includes
nonemptiness. Zero P, m=0, n=0, and the zero ring are allowed by the finite
presentation structures. No characteristic assumption appears. The universal
u and the containing u+1 support the node's size convention; arbitrary filtered
categories, including multiple parallel arrows, are covered by the explicit
common-stage arrows. All variables and universe levels in the signature are
bound explicitly.

Independent searches, using different wording from the worker:

- LeanFinder: "Global sections on a coherent pro etale site preserve filtered
  colimits and finitely presented sheaves are compact": eight hits concerning
  condensed categories and their colimits/equivalences, no matching statement.
- Loogle: `"SheafOfModules", "IsFinitePresentation"`: twelve hits; checked the
  finite-presentation class and presentation structures in source. These define
  the required notion and do not state the complete calculus.
- LeanSearch: "Evaluation of abelian sheaves on quasi compact quasi separated
  pro etale schemes preserves filtered colimits": unavailable, Internal Server
  Error, recorded by msearch.py; no mathematical conclusion drawn from failure.
- rg in Mathlib module-sheaf sources, upstream WeilConjectures, group-clone
  lean/Sheaf, and the pro-etale module-object framework for filtered-colimit
  preservation, compact objects, finite presentations, and section/colimit
  combinations. Opened the closest project hits:
  `FinitePresentationHomColimit.lean` is internal sheaf Hom on topological
  ringed spaces and directed posets; `SiteFilteredColimitSections.lean` is
  section continuity under a finite-precoverage hypothesis. Neither states this
  qcqs pro-etale result with global Hom and both eventual-equality clauses.

Repairs: none to Lean or node metadata. Added this independent reading only.
No definitions, axioms, local notation, local instances or proofs were introduced;
the one theorem proof remains `sorry`. Checked the signature byte-for-byte against
`lean.statement`, the 100-column limit, and the source/blueprint docstrings.

Validation: scompile.py on the server compiled the submitted module cleanly in
2.6 seconds (and its side-only RingedSiteModules dependency in 0.9 seconds),
with nice 19, two threads and 60 seconds per file. No compiler warning or error.

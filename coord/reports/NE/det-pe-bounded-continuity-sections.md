## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections` states
`AlgebraicGeometry.Scheme.ProEt.isIso_ringHypercohomology_colimitPost` with `sorry`.
It also supplies the concrete helper `ringHypercohomology` and the named structural
statement `ringHypercohomology_transport_preservesZeroMorphisms`, with `sorry`,
needed to apply the published module transport termwise. These helpers belong to the
hypercohomology convention explicitly introduced in this node's statement. Their
source/blueprint docstrings and full names are recorded in `lean.declarations`.
No other DAG node is stated, and the item JSON changes only in `lean`.

Hypothesis and clause correspondence:

- The base scheme is `X : Scheme.{u}`; the site is exactly `X.ProEt` and `topology X`,
  the recorded `sk-def-pe-site` Mathlib definitions. No qcqs assumption is made on X.
- The arbitrary sheaf of rings is `R : Sheaf (topology X) RingCat.{u + 1}`.
  `RingCat`, rather than `CommRingCat` or a constant/condensed ring, retains
  noncommutative rings and arbitrary ring-sheaf restrictions.
- The site object is `U : X.ProEt`. Its underlying scheme is `U.left`.
  `[CompactSpace U.left]` expresses quasi-compactness, equivalently a finite affine
  open cover; `[QuasiSeparatedSpace U.left]` says intersections of quasi-compact
  opens are quasi-compact, equivalently the stated affine-open intersection condition.
- The size convention is explicit: schemes have level u, the original site objects
  level u+1 and its morphisms level u; coefficient rings/modules, abelian groups,
  and the indexing category have level u+1. The published `proEtaleSiteModel X`
  is `AsSmall.{u+1} X.ProEt`; it enlarges only the Hom universe and retains EVERY
  original object and cover. It imposes no equality between original site universes.
- `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]` is a small filtered category
  in the coefficient universe. Mathlib's `IsFiltered` includes nonemptiness.
- The diagram is `K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ`.
  `ringedSiteModules` is the dependency's transparent abbreviation for exactly
  `SheafOfModules R`, i.e. sheaves of left R-modules with linear morphisms.
- The common bound is `a : ℤ`, with
  `hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b)`.
  This is strict vanishing of TERMS, not merely vanishing of cohomology.
  Categorical `IsZero` is invariant under choice of the zero module object.
- The chosen `colimit K` is a complex colimit. Mathlib's
  `HomologicalComplexLimits` constructs it degreewise in the coefficient category;
  its evaluations preserve these colimits. Consequently it is the stated termwise
  colimit in sheaves of modules, with induced differential and cocone chain maps.
- `ringHypercohomology X R U q` gives the node's H^q(U,-) as an actual functor to
  `AddCommGrpCat.{u+1}`: first precompose module sheaves along `AsSmall.down` using
  `proEtaleModuleToModel`, then use the published functorial K-injective replacement
  on the genuinely small model, evaluate its module section complex at
  `AsSmall.up.obj U`, forget only its scalar action, and take integer homology.
  The transported ring S is the actual precomposition of R, and its values at this
  object are R(U). The Grothendieck property on the small site is supplied by the
  recorded arbitrary-ring theorem `SheafOfModules.isGrothendieckAbelian S`.
  The replacement is the source's small-object-argument construction, with its
  natural monomorphic quasi-isomorphism and termwise-injective instance. It is
  neither a chosen arbitrary resolution functor nor data extracted from `sorry`.
  On bounded-below inputs this computes precisely bounded-below injective evaluation:
  comparison of a bounded-below injective resolution with the K-injective replacement
  is a homotopy equivalence between K-injectives, unique up to homotopy, so additive
  evaluation induces the canonical same cohomology and maps. The representative
  need not itself be bounded below; this does not change the specified functor.
- `(q : ℤ)` includes every degree. The conclusion is exactly
  `IsIso (colimit.post K (ringHypercohomology X R U q))`.
  Mathlib defines `colimit.post` as `colimit.desc` of the image colimit cocone;
  `colimit.ι_post` identifies each leg with hypercohomology of `colimit.ι K i`.
  Thus this asserts invertibility of the specified canonical map, not existence
  of some isomorphism between the two objects.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.precoverage`,
  `ProEt.topology`; the Mathlib match is the dependency's binding (no missing lean
  record for this Mathlib leaf).
- `def-weil-size-convention` is metatheoretic, with no declaration/import.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `Cocone`, `IsColimit`,
  `colimit.desc`, `colimit.post`; `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q` were read; the node's cochain complexes
  and their homology are the underlying Mathlib `CochainComplex` and
  `HomologicalComplex.homologyFunctor`. No second complex or derived category is defined.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `SheafOfModules.evaluation` is Mathlib's module-valued evaluation functor.
- The stated proof dependency `lem-weil-pbc-ring-sheaves-grothendieck` binds exactly
  `SheafOfModules.isGrothendieckAbelian` in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`. It is used on
  the small model with the transported arbitrary RingCat sheaf.
- The Mathlib proof leaf `lem-weil-pbc-filtered-colimit-abelian-groups-exact` is
  `instPreservesHomologyFunctorAddCommGrpCatColim` in `Mathlib.Algebra.Category.Grp.AB`,
  imported as a proof-only import.
- The published `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` supplies
  `proEtaleSiteModel`, `proEtaleModelTopology` and `proEtaleModuleToModel`, whose
  definitions were read in full. This is the site-size transport already contemplated
  by the size convention, not a new mathematical assumption.
- The source `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
  supplies the actual `CochainComplex.kInjectiveResolutionFunctor` and its injective
  components. Its parent module supplies the natural monomorphic quasi-isomorphism.

The three geometric proof dependencies `det-pe-hypercover-existence`,
`det-pe-hypercover-complex`, and `det-pe-sections-limits-colimits` have no Lean
records yet, so there is no module to import for them. They are proof dependencies,
not unstated prerequisites of the signature. Their exact six-step use remains in
this theorem's proof docstring; this delivery does not state those other nodes.

Edge cases checked: the empty scheme and empty site object are allowed, as are the
zero ring, zero module sheaves and the zero diagram. No nonempty-space or nonzero-ring
assumption is introduced. The filtered category is nonempty by the definition in the
node, so an empty indexing category is correctly excluded. Any integer a is allowed;
no truncation changes the complexes. For q<a the same canonical comparison is stated
(and both hypercohomology groups vanish). Negative degrees and q=0 are included.
Finite total diagonals with no summands are included in the proof, as required.

Searches made (2026-10-16):

- `msearch.py ... leanfinder` with “Hypercohomology of uniformly bounded below
  complexes of module sheaves on the pro-etale site at a qcqs object commutes with
  filtered colimits”: eight hits, including condensed-module colimits/Grothendieck
  instances, `Sheaf.H` and sheaf presentations. None states this assertion.
- `msearch.py ... loogle` with `CategoryTheory.Limits.colimit.post, SheafOfModules.evaluation`:
  zero hits. Both exact declarations were independently read in source.
- `msearch.py ... grep` with
  `ProEtale.*[Cc]ohomology|[Cc]ohomology.*ProEtale|[Hh]ypercohomology.*[Cc]olimit`:
  zero hits in Mathlib. Direct rg additionally inspected cochain colimits and
  module-sheaf evaluation and colimit declarations.
- `msearch.py ... leanfinder` with “Hypercohomology functor of complexes of modules
  over an arbitrary sheaf of rings computed by injective resolutions”: eight hits,
  including ordinary `Functor.rightDerived`, `injectiveResolutions`, `Sheaf.H` and
  `Sheaf.cohomologyPresheafFunctor`; none gives this integer-indexed arbitrary-ring
  complex functor on the pro-etale site. Reuse their existing homology/resolution
  infrastructure rather than constructing a second resolution.
- `msearch.py ... loogle` with
  `CochainComplex.kInjectiveResolutionFunctor, HomologicalComplex.homologyFunctor`:
  the upstream-specific first name is unknown to the Mathlib-only search; this is
  inconclusive, and its actual published source declaration was read directly.
- Direct rg in the source project's `WeilConjectures`, the shared `lean/Sheaf`,
  and `dag/lean_names_upstream.json` for the proposed declaration names: no clash.
  Required `grep -rn det-pe-bounded-continuity-sections` in the source project:
  no existing binding. Concept searches found the related
  `condensed_qcqs_globalSections_continuity` (constant condensed coefficients and
  cohomological truncation), and `smallDerivedEvaluation` (constant commutative
  coefficients); neither is this arbitrary-ring statement/helper. Existing
  hypercover totals also require commutative coefficient sheaves. They cannot be
  substituted for the arbitrary RingCat coefficients here.
- DAG searches read the parallel `det-lem-bounded-continuity-sections` and checked
  definition nodes mentioning hypercohomology/derived evaluation. No distinct
  unstated definition node carries the helper's arbitrary-ring complex functor.

There is no statement correction, new node, dependency-module repair or
STATEMENT-DISPUTED finding. All original statement dependencies have usable recorded
interfaces or Mathlib matches. Only the two named theorem proofs are postponed.

Validation: prescribed scompile.py compiled both the sandbox file and its actual
library module path cleanly (26.0 s and 17.7 s), with no warnings. The initial
incorrect homological-complex colimit import was repaired to
`Mathlib.Algebra.Homology.HomologicalComplexLimits`. The missing zero-map instance
was repaired by the named, documented structural lemma above.


## Second reading by NE

I independently read the current DAG node, the sandbox Lean module and binding, every
statement dependency's record and declaration, the blueprint node and its proof, and the
parent unit sk-cor-pe-bounded-continuity. I also read Stacks injectives.tex,
Theorem theorem-K-injective-embedding-grothendieck (079P); sites-modules.tex,
Lemma lemma-pushforward-module (03D1); and proetale.tex,
Lemma lemma-compute-cohomology (09A2) with the preceding hypercover convention.
The blueprint permits arbitrary ring sheaves, and neither it nor these source places
requires X itself to be qcqs or coefficients to be commutative. There is no repair note
for this item, no statement_change, no new node, and no dependency module in this packet.

Independent object/hypothesis/conclusion inventory and correspondence:

1. A scheme X and its small pro-etale site: `(X : Scheme.{u})`, `X.ProEt`,
   and `topology X`. Verdict: exact. I opened Mathlib's Scheme and Proetale modules:
   `Scheme.ProEt` is the weakly-etale over-category with all over-morphisms, and its
   precoverage is the fpqc/finite-refinement weakly-etale precoverage. This uses
   def-pc-scheme and sk-def-pe-site, not the big site or just affine objects.
2. An arbitrary sheaf of rings R on that site: `(R : Sheaf (topology X) RingCat.{u+1})`.
   Verdict: exact; RingCat has unital rings, with no commutativity, constancy, torsion,
   characteristic, Noetherian, or nonzero assumption. The R in every occurrence is
   this same variable, including the transported coefficient sheaf in the helper.
3. A qcqs site object U: `(U : X.ProEt) [CompactSpace U.left]
   [QuasiSeparatedSpace U.left]`. Verdict: exact. Quasi-compactness is compactness
   of the underlying scheme, equivalent to a finite affine cover. I checked
   `quasiSeparatedSpace_iff_forall_affineOpens`: the other instance says exactly that
   intersections of affine opens are quasi-compact. No extra property of U -> X
   beyond being an object of X.ProEt is assumed.
4. The chosen universe convention: `universe u`, with Scheme at u, site objects
   at u+1 and original site morphisms at u, ring/module/Ab values at u+1, and
   `I : Type (u+1)` with `SmallCategory I`. Verdict: exact to the recorded larger
   universe convention. I read `proEtaleSiteModel := AsSmall.{u+1} X.ProEt`,
   its induced topology, and both sectionwise transports in ProEtaleInverseImage.
   AsSmall retains every object and transports all covers, enlarging Hom sizes;
   it does not identify the original site's two universe levels or select a
   smaller collection of schemes. There are no extra smallness-instance binders.
5. A small filtered category I: `{I : Type (u+1)} [SmallCategory I] [IsFiltered I]`.
   Verdict: exact. Mathlib IsFiltered extends IsFilteredOrEmpty and includes
   Nonempty C, as does the dependency's definition of filteredness.
6. A diagram of integer-indexed cochain complexes of left R-module sheaves:
   `(K : I ⥤ CochainComplex (ringedSiteModules.{u+1} R) ℤ)`.
   Verdict: exact. I opened RingedSiteModules: the abbreviation is precisely
   Mathlib `SheafOfModules.{u+1} R`, not sheaves of modules over a constant ring.
   Mathlib's module-sheaf definition has sectionwise modules and semilinear
   restrictions; its morphisms are linear natural maps. CochainComplex and its
   integer homology use the complex/cohomology part of def-weil-abstract-derived-category.
7. A single integer a, with every term below it zero for every diagram object:
   `(a : ℤ) (hK : ∀ (i : I) (b : ℤ), b < a → IsZero ((K.obj i).X b))`.
   Verdict: exact. This is strict termwise vanishing with a uniform bound, not
   vanishing of homology or an individually chosen bound for each i. IsZero is
   the invariant categorical meaning of a zero module sheaf.
8. The termwise colimit complex: `colimit K` inside `colimit.post`.
   Verdict: exact. I read HomologicalComplexLimits: complex colimits are formed
   degreewise with the induced differential, and evaluation preserves them.
   Thus neither a derived colimit nor a sectionwise presheaf colimit is substituted.
9. Hypercohomology computed by derived evaluation, valued in abelian groups:
   `ringHypercohomology X R U q`. Verdict: exact. Its concrete composite is
   sectionwise module transport, published `kInjectiveResolutionFunctor`,
   `SheafOfModules.evaluation` at `op (AsSmall.up.obj U)`, scalar forgetful functor,
   and integer homology. I read the resolution definition, its natural
   monomorphic quasi-isomorphism, K-injectivity and injective-term statements.
   On a bounded-below input, comparison with a bounded-below injective resolution
   is a homotopy equivalence of K-injective resolutions, compatible with maps;
   additive evaluation preserves the homotopies. It therefore yields the node's
   hypercohomology functor and canonical maps. The replacement itself need not
   vanish below a. The helper's S is the actual precomposition of R and has the
   same value R(U) at AsSmall.up.obj U. The arbitrary-RingCat Grothendieck theorem
   applies to this genuinely small model, with all required instances supplied.
10. Every integer degree q, after the diagram and bound are fixed: `(q : ℤ)`.
    Verdict: exact, with no restriction to natural or positive degrees.
11. Invertibility of the canonical cocone comparison:
    `IsIso (colimit.post K (ringHypercohomology X R U q))`.
    Verdict: exact. Mathlib colimit.post is the universal map from the colimit
    of the functor-applied diagram into the functor of colimit K. Its composites
    with the colimit legs are precisely hypercohomology of the original cocone
    maps. This asserts the specified map is an isomorphism, with the correct
    direction and quantifier order.

Edge cases: the empty scheme and empty object U, zero rings, zero module sheaves,
and the zero diagram remain allowed. An empty index category is excluded exactly
because filtered includes nonemptiness. All integers a and q are permitted, including
q=0, negative degrees and q<a. For q<a both groups vanish; the same canonical map is
still asserted invertible. There is no characteristic condition. Empty total diagonals
and rank-zero terms are included. The ring and module universe is the site's larger
universe, and no hidden universe variable or auto-implicit binder remains.

Independent duplicate searches (all through the prescribed tool or read-only rg):

- `msearch.py ... leanfinder` with "For a coherent ringed site derived sections on
  complexes with a uniform lower bound preserve filtered colimits": eight hits,
  including Sheaf.hasFilteredColimitsOfSize, Sheaf.ab5ofSize and module-sheaf
  colimit infrastructure. None gives derived sections continuity at a qcqs object.
- `msearch.py ... leansearch` with "Hypercohomology at an object of a ringed site
  commutes with filtered colimits of complexes with one common strict lower bound":
  eight hits, including complex filtered colimits, exact Ab colimits and ordinary
  ModuleCat filtered-colimit constructions. These are inputs, not this theorem.
- `msearch.py ... loogle` with `"colimit.post", "IsIso"`: zero hits.
- `msearch.py ... grep` with `ringHypercohomology|isIso_ringHypercohomology_colimitPost`
  and then `derived.*[Ss]ections|[Ss]ections.*derived|[Hh]ypercohomology.*filtered`:
  zero Mathlib hits. Direct rg searched Mathlib, the old source project's
  WeilConjectures, shared lean/WeilConjectures, and shared lean/Sheaf with
  hypercohomology, derivedEvaluation, continuity and zero-map transport spellings.
- I opened the nearby candidates rather than relying on names:
  `smallDerivedEvaluation` fixes constant commutative coefficients and starts
  on D+; `condensed_qcqs_globalSections_continuity` uses pulled-back condensed
  commutative internal modules and cohomological truncation;
  `ringedSiteZerothHypercohomology` assumes CommRingCat and computes global H0;
  `sectionHypercohomologyFunctor` is for fixed-value sheaves `Sheaf J A`, not
  modules over a varying ring sheaf. None is the present arbitrary-RingCat,
  object-evaluation, complex-input functor or theorem. Existing resolution,
  evaluation, homology and transport constructions are reused.
- I also searched pushforward/PreservesZeroMorphisms/Additive in Mathlib and both
  project source sets. The open-module direct-image zero-map instance is only
  for an open of a scheme; it does not apply to the site's AsSmall transport.
  No general usable zero-map statement duplicates the helper in this delivery.

H5/H6/H8/H9 checks: the sole definition has real functor data assembled from existing
constructions; its needed zero-map proof is a named theorem with its source and full
sectionwise proof in its docstring. It is recorded in lean.declarations under this
node's hypercohomology convention. Both theorem bodies are exactly `by sorry`.
The main docstring carries all six DAG proof steps, including construction of the
underlying Ab module-colimit action, signs, finite sums, cycles/boundaries and
canonical-map identification. Each declaration has source and blueprint citations;
there are no private definitions, local notation, extra axioms or file-local instances.
The geometric proof-only dependencies remain unstated and hence have no imports;
recorded proof dependencies with usable modules are imported. No sibling/dependency
module needs separate verification.

Mismatch found and repair: the module had several public declarations but lacked
brief-stage2 §3's Main definitions/Main statements index. Added those two lists to
the module docstring. No mathematical statement, definition body, dependency record,
or Lean signature was changed. The original worker report remains above.

Validation: the first independent prescribed scompile.py run compiled both sandbox
and library paths without errors or warnings (29.9 s and 13.0 s). The module is
recompiled after the docstring-only correction: sandbox 10.6 s and library 11.6 s,
again without errors or warnings. The required deliver2.py dry run follows.
The node's lean.statement was mechanically checked against the exact theorem header;
all non-lean item fields equal the repository copy.

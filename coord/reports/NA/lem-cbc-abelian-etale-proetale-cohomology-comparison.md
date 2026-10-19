## Worker report

The module states `AlgebraicGeometry.ProEtale.comparisonCohomologyMap_bijective` with
sorry, and constructs the canonical constant-sheaf identification and canonical
cohomology pullback with real data. There is no statement correction or new node.
The two helpers belong to the comparison map in this node and are recorded in
lean.declarations.

Clause-by-clause reading:
- An arbitrary scheme T is `(T : Scheme.{u})`.
- Its small etale site is `T.smallEtaleTopology`; its small pro-etale site is
  `Scheme.ProEt.topology T`. The imported comparison module supplies the inclusion
  and the geometric morphism. The abelian inverse image is the existing
  `comparisonUpperStar AddCommGrpCat.{u + 1} T`, defined by left Kan extension and
  sheafification along that same inclusion.
- Every abelian sheaf is `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  There is no coefficient ring, torsion, finiteness, or constructibility binder.
  The group universe is the common larger universe for the small sites, whose
  object universe is u+1 and morphism universe is u.
- Every integer i >= 0 is represented without loss by `(i : ℕ)`.
- The source group is `Sheaf.H F i`, the Ext model of right derived global sections.
  The target is `Sheaf.H ((comparisonUpperStar ... T).obj F) i`.
- The arrow is `comparisonCohomologyMap T F i`. It uses `Sheaf.H.mapFunctor`:
  apply exact inverse image to an Ext class and precompose with the canonical
  identification of the constant integer sheaves. `comparisonConstantSheafIso`
  constructs that identification by uniqueness of left adjoints to global sections,
  using the actual comparison adjunction and the identity identification of sections
  after direct image. No arbitrary isomorphism or map is chosen.
- `Function.Bijective` of this additive homomorphism states exactly that this
  canonical arrow is an isomorphism of abelian groups.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded
  `Scheme.proEtaleDerivedCategory` supplies the same `Scheme.ProEt.topology` site;
  no ring-valued derived category is substituted for abelian sheaves. This module
  is publicly imported by `ProEtaleSiteComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `Scheme.preservesFiniteLimits_proEtaleSiteComparison`, and its upstream public
  import `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`:
  `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction` and exactness
  instances. These already allow arbitrary Grothendieck abelian coefficients.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`,
  whose record explicitly retains `Sheaf.H` and `Sheaf.H'` for cohomology.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `Sheaf.H.mapFunctor`. Read-only source
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf` explains the terminal-object/adjunction construction used for the helper.

The recorded proof dependency modules SiteCohomologyPullback, SiteLerayDegenerate,
SitePullbackAbelianExact and Abelian.RightDerived.LongExactSequence are imported
without public. The two cbc proof dependencies without Lean records are not imported;
this delivery does not need their proofs to state its theorem. The docstring gives
all four proof steps, including naturality and the triangle identity identifying
the Leray composite with the canonical map.

Edge cases checked: i=0 gives the usual unit on global sections; the empty scheme
is permitted, with zero section/cohomology groups; the zero sheaf is permitted;
non-torsion and infinite sheaves are included. No affineness or quasi-compactness
restriction occurs. Terminal preservation is used only for the canonical constant
comparison, not added as a hypothesis.

Searches:
- msearch leanfinder: "Etale proetale cohomology comparison for arbitrary abelian
  sheaves": eight hits on sites/formal etaleness/light condensed objects, no match.
- msearch loogle: `"cohomology", "Sheaf"`: seven hits, including Sheaf.functorH,
  cohomologyPresheafFunctor; no comparison theorem.
- msearch grep: `compare.*cohomology|cohomology.*[Pp]ro[Ee]t` in AlgebraicGeometry:
  only the ElladicCohomology TODO.
- rg of upstream ProEtale for cohomologyMap and cohomology/isomorphism patterns:
  LowerStarAcyclic has a vanishing transfer, not bijectivity of a canonical map.
  Read that declaration: it assumes vanishing of a fixed degree and concludes
  vanishing, so it is not the present theorem.
- rg of the item's id in WeilConjectures: no hit.
- rg of cohomology/pro-etale patterns in lean/Sheaf: hypercover, support and
  functions-quotient modules, no arbitrary-abelian comparison theorem.
- Further source search found the existing `Sheaf.H.mapFunctor` and the canonical
  constant-sheaf pullback construction; these are reused instead of a new Ext map.

Read source: literature/stacks-project/proetale.tex, lemma-compare-cohomology
(Tag 099W), explicitly arbitrary abelian sheaves, all degrees, via relative
comparison and Leray. No node fault or STATEMENT-DISPUTED issue found.

Validation: scompile.py compiled the module cleanly; deliver2.py --no-push passes
the delivery preflight and per-file compilation. No delivery was pushed.

## Second reading by NA

I independently read the node and its four proof steps against
`proetale.tex`, the opening of section-comparison (Tag 099R),
lemma-relative-comparison (099V), and lemma-compare-cohomology (099W), part (1).
The section assumes only a scheme and compatible choices of the two small
sites; it does not assume quasi-compactness, separation, a characteristic, or
coefficient restrictions. The node agrees with the source. No statement
correction, new definition node, or dependency module is needed.

Object/hypothesis/conclusion checklist:

- Arbitrary scheme T: `(T : Scheme.{u})`. I opened the recorded Mathlib
  `AlgebraicGeometry.Scheme` structure: a locally ringed space with local affine
  charts. Verdict: same object, no added scheme hypothesis.
- Small etale site: `T.smallEtaleTopology`. I read the recorded
  `Mathlib.AlgebraicGeometry.Sites.Etale` declaration, `Scheme.Etale`, and
  `ofArrows_mem_smallEtaleTopology_iff`: etale T-schemes, T-morphisms, jointly
  surjective covers. Verdict: exact.
- Small pro-etale site: `Scheme.ProEt.topology T`. I opened the recorded
  `ProEtaleDerivedCategory` dependency and Mathlib's `Scheme.ProEt` and
  `proetalePrecoverage`: weakly etale T-schemes with fpqc covers, not the big
  site and not all merely surjective families. Verdict: exact; the module does
  not substitute the dependency's constant-ring module derived category for
  abelian sheaves.
- Comparison geometric morphism: `Scheme.toProEt T` and
  `comparisonUpperStar AddCommGrpCat.{u + 1} T`. I opened the recorded
  `ProEtaleSiteComparison` module and upstream `Comparison.Defs` signatures:
  direct image is restriction and inverse image is left Kan extension followed
  by sheafification along that very inclusion; `comparisonAdjunction` is their
  constructed adjunction. The upstream instances give exactness on arbitrary
  Grothendieck abelian coefficients. Verdict: the abelian inverse image of
  this geometric morphism, without the finite-ring restriction of the
  dependency's separate module-coefficient specialization.
- Arbitrary abelian etale sheaf F: `(F : Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u + 1})`. No torsion, finite, constructible, or ring binder.
  Verdict: every abelian sheaf in the common larger site universe.
- Every integer i >= 0: `(i : ℕ)`, quantified after T and F. Verdict: exactly
  the nonnegative degrees of the node.
- Source cohomology: `Sheaf.H F i`. I opened Mathlib's definition: Ext from
  the constant integer sheaf. Hom from that sheaf is global sections, by
  the constant-sheaf/terminal-sections adjunction; its derived Ext therefore
  computes right derived global sections. Verdict: correct cohomology model.
- Target cohomology: `Sheaf.H ((comparisonUpperStar ... T).obj F) i`.
  Verdict: the same cohomology model on the correct small pro-etale site.
- Specified canonical arrow: `comparisonCohomologyMap T F i` uses the existing
  `Sheaf.H.mapFunctor` with the inverse of the constant-sheaf identification.
  I read its signature and body: map Ext by exact inverse image, then
  precompose by constant integers on the target mapping to pulled-back
  constant integers. This direction is correct. Both constant-sheaf
  identifications are compatible with their sections adjunctions, so this is
  the usual degree-zero unit and its canonical cohomology extension.
  Verdict: the canonical map, not an arbitrary group isomorphism.
- Isomorphism of abelian groups: `Function.Bijective` of that additive
  homomorphism. Verdict: equivalent to an abelian-group isomorphism with
  precisely this underlying map; no extra conclusion or weakened clause.

Edge cases: zero sheaf and empty scheme have no excluded binders. Degree zero
is explicitly included and the constant/sections adjunction gives the unit on
sections there. Infinite and non-torsion sheaves are allowed. There is no
characteristic assumption and no index family to restrict. The sites have
object universe u+1 and morphism universe u; coefficients are in the common
larger universe u+1, as in the dependency's size convention, without imposing
equality of the two site universes. All universes/variables are bound.

Independent searches (different wording from the first reading):

- msearch leanfinder, `restriction from weakly etale sheaves to etale sheaves
  comparison cohomology abelian`: eight unrelated formally-etale results;
  no theorem match.
- msearch loogle, `"comparison", "H"`: general terminal/pullback comparison
  morphisms, no cohomology comparison theorem.
- msearch leansearch, `Cohomology of an abelian etale sheaf equals cohomology
  of its inverse image on the pro-etale site`: service unavailable (Internal
  Server Error), no mathematical verdict assigned to that search.
- msearch grep, `comparisonUpperStar|constantSheafsheafPullbackIso`: no indexed
  Mathlib hit. Direct rg in Mathlib, the project's lean/Sheaf, and both the
  slopmaster2 and group-clone pro-etale trees independently found the
  upstream `ConstantSheaf` helper and `Comparison/LowerStarAcyclic`.
  The latter's
  `isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj` assumes
  vanishing of one source degree and concludes target vanishing; I opened
  its signature and body. It does not state bijectivity of this canonical
  cohomology map. No matching theorem was found, so the theorem module stays.

Mismatch repaired: the worker rebuilt the constant-sheaf comparison from
adjunction uniqueness although upstream already supplies
`Functor.constantSheafsheafPullbackIso`. I added its public import and changed
`comparisonConstantSheafIso` to specialize that existing isomorphism, transporting
from abstract pullback to the constructed inverse image with Mathlib's
`Functor.sheafPullbackConstruction.sheafPullbackIso`. This transport is needed:
the generic helper uses `Functor.sheafPullback`, whereas `comparisonUpperStar`
uses `Functor.sheafPullbackConstruction.sheafPullback`. Both transports use
uniqueness with the specified right adjoint, preserving the canonical map.
The helper docstring now describes that specialization. No theorem signature,
node statement, or dependency record changed.

I also read the imported proof-dependency signatures (SiteCohomologyPullback,
SiteLerayDegenerate, SitePullbackAbelianExact, and the right-derived module).
They are proof imports, not additional hypotheses on this theorem. The
statement docstring retains all four node proof steps, including naturality
and the triangle identity identifying the Leray composite. The two definitions
have real construction data; the sole local theorem has only `sorry` as proof.
Every local declaration has the source/blueprint docstring. There is no private
notion, file-local instance/notation, or unbound binder. The node's
`lean.statement` remains verbatim the theorem signature.

Validation: scompile.py compiled the repaired file both as a sandbox module
and at its library module path (9.1 s and 9.4 s), without errors or warnings.

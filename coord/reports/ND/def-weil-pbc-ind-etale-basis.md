## Worker report

The whole definition already exists. Record the existing declarations in
`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`; no module is added.
The primary declaration is `AlgebraicGeometry.Scheme.AffineProEt`, accompanied by
`AlgebraicGeometry.Scheme.instCategoryAffineProEt` and the declarations
`AlgebraicGeometry.Scheme.AffineProEt.toProEt`, `.precoverage`, and `.topology`.
The node copy changes only `lean`; no new node, dependency repair or statement
correction is needed. No theorem is proved in this delivery.

Clause-by-clause correspondence:

- "For affine X": use `X.AffineProEt` at an arbitrary `X : Scheme.{u}` with
  `[IsAffine X]`. The existing definition works for every base scheme, so it
  applies to all affine X without introducing any further restriction. Its
  applicability to nonaffine bases does not alter the defined site for affine X.
- "full subcategory of X_Proet": `AffineProEt X` is
  `proAffineEtale.Over ⊤ X`. Thus an object is a structure morphism satisfying
  `proAffineEtale`, and `⊤` permits every morphism over X. The category instance
  is the category of these objects and all X-morphisms. `AffineProEt.toProEt X`
  is `MorphismProperty.Over.changeProp` along
  `proAffineEtale_le_weaklyEtale`; the source registers both `Full` and `Faithful`
  instances for this inclusion. Hence the ambient site is the stipulated small
  weakly-etale site, not a category with fewer morphisms.
- "consisting of affine schemes ind-etale over X": `proAffineEtale` is the
  cofiltered-limit property for affine etale stages. `proAffineEtale.isAffine`
  ensures the domain is affine. The dependency's
  `AlgebraicGeometry.proAffineEtale_Spec_iff` identifies the property for a spectrum
  map with `RingHom.IndEtale`; its coordinate-free form
  `AlgebraicGeometry.proAffineEtale_iff_appTop` applies to any morphism between
  affine schemes. This is the same `Algebra.IndEtale` of the dependency, whose
  presentation uses a small filtered category and etale (thus finitely presented)
  algebras. There is no extra finite-type requirement on the limit algebra.
- "Give it the coverings induced from the small pro-etale site": the exact
  definition is `AffineProEt.topology X =
  (AffineProEt.toProEt X).restrictedTopology (ProEt.topology X)`.
  `AffineProEt.precoverage` additionally records the covering families as the
  comap of `Scheme.proetalePrecoverage` along the inclusion and the forgetful
  functors to schemes. In particular the fpqc covering condition is retained;
  it is not replaced by bare joint surjectivity or by etale coverings.

Dependency records and source declarations inspected:

- `def-weil-pbc-ind-etale-algebra` records
  `Sheaf.RingTheory.IndPrincipalZariski`, `Algebra.IsIndPrincipalZariski`, with
  supporting declarations `Algebra.IndEtale`, `Algebra.WeaklyEtale`,
  `AlgebraicGeometry.proAffineEtale_Spec_iff`, and
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`. Its module publicly
  imports `WeilConjectures.RingTheory.ProEtale.IndEtale` and
  `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`. The ind-etale
  clause and its spectrum equivalence are the relevant ingredients here;
  the principal ind-Zariski and weak-flatness clauses are not additional conditions
  on the site's objects.
- `def-weil-pbc-proetale-site` records
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`. Its public import
  `Mathlib.AlgebraicGeometry.Sites.Proetale` supplies `Scheme.ProEt`,
  `Scheme.ProEt.precoverage`, and `Scheme.ProEt.topology`, the site ingredients
  of that composite definition. The existing affine-site module imports the same
  Mathlib site through `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
  The coefficient and derived-category clauses are not used by this node.

The blueprint source was opened at
`literature/blueprint/master/blueprint/sec-proper-base-change/` followed by
`sk-thm-properbasechange/def-weil-pbc-ind-etale-basis.md`; its entire statement
is the node's two sentences. The existing module's docstring explicitly describes
cofiltered limits of affine etale schemes; its definition, inclusion, category
instance and restricted topology were all read in full.

Edge cases checked: the empty affine scheme and the zero coordinate ring are not
excluded; an empty domain is allowed, and covering families retain the ambient
site's empty-cover behavior. A nonempty affine target cannot acquire an empty
cover because the inherited fpqc condition still applies. No nonemptiness,
Noetherianity, connectedness, finite-presentation condition on the final object,
or additional field hypothesis is imposed. `Scheme.{u}` and `Type (u + 1)` allow
arbitrary scheme universes with the dependency's usual size convention. The
filtered presentation index has universe u, as required by the project. Affine
etale stages have affine transition maps automatically. Ind-etale objects are
weakly etale through the existing implication, not through a new assumption.

Searches for existing declarations:

- `msearch.py ... leanfinder`, query "full subcategory of the small pro-etale site
  consisting of affine ind-etale schemes with induced coverings": eight ordinary
  etale-site results, no affine ind-etale match in that index.
- `msearch.py ... loogle`, query
  "AffineProEt, AlgebraicGeometry.AffineProEt.topology": no hits, unknown identifier
  `AffineProEt` in the Mathlib index.
- `msearch.py ... grep`, query `AffineProEt|ind.etale.*site` restricted to
  `AlgebraicGeometry`: no Mathlib hits.
- `msearch.py ... leansearch`, query "affine ind-etale subsite of the pro-etale
  site": service unavailable (Internal Server Error); no result inferred.
- Direct `rg` on upstream `WeilConjectures` for `def AffineProEt`,
  `namespace AffineProEt`, and `instCategoryAffineProEt` found
  `AlgebraicGeometry/ProEtale/Comparison/Affine.lean`, including its object
  definition, category, inclusion, precoverage, and topology. Direct source reads
  establish the exact match that the remote Mathlib search index did not contain.
- Direct `rg` for `AffineProEt|affine ind.etale` in Mathlib algebraic geometry and
  `lean/Sheaf` found no competing definition (only an unrelated prose occurrence).
- Direct `grep -rn` for the item id in upstream `WeilConjectures` found no hit;
  the match is semantic, not a blueprint-tag hit. Searching the upstream-name
  metadata for `AffineProEt` found no indexed hit either.

Validation: a sandbox scratch probe imported the exact existing module and used
`#print` on `AffineProEt`, `toProEt`, `precoverage`, and `topology`, and `#check`
on `instCategoryAffineProEt` and `proAffineEtale_Spec_iff`. It compiled cleanly
on the server via `scompile.py`, taking 1.7 seconds, nice 19, two threads, with
60 seconds per file. The server printed the same object and induced-topology
bodies inspected locally. The delivery dry run also checks every recorded name
in a fresh server probe. No local Lean compiler or library build was run.

## Second reading by ND

I independently read the node copy, both dependency nodes and their recorded
modules, the exact framework sources in the read-only group clone, and
`coord/pefw-upstream-framework.md`. The blueprint source at order 1278 has the
two sentences in the node, with no proof or additional standing hypotheses.
I also read Stacks `proetale.tex`, `definition-ind-etale`,
`definition-fpqc-covering`, and `definition-big-small-proetale`, including the
preceding size discussion. Neither Noetherianity nor a base field is assumed.

Object, hypothesis, and conclusion checklist:

- Base: an affine scheme X. `def AffineProEt (S : Scheme.{u}) : Type (u + 1)`
  is used with `[IsAffine S]`. Its definition on additional bases does not
  change its value on affine S. Verdict: the same base, no extra hypothesis.
- Ambient site: `X_Proet`. The recorded dependency module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` publicly imports Mathlib's
  `Scheme.ProEt`. I read its body, `WeaklyEtale.Over ⊤ S`, and its
  `precoverage` and `topology`. These are the ambient category and topology
  used by the affine module. Verdict: the same small weakly-etale site.
- Objects: affine schemes ind-etale over X. The body of `AffineProEt` is
  `proAffineEtale.Over ⊤ S`. I read `proAffineEtale`, its `isAffine` consequence,
  and `proAffineEtale_Spec_iff` and `proAffineEtale_iff_appTop` in the exact
  group clone. They identify this condition with ind-etaleness on coordinate
  rings when both schemes are affine. The recorded dependency module
  `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes `Algebra.IndEtale`;
  I read its small filtered colimit presentation with etale stages. Those
  stages are finitely presented, with no such condition on the final algebra.
  The dependency's principal ind-Zariski clause is not imposed on these
  objects. Verdict: exact object condition, no added finiteness requirement.
- Full subcategory: `instCategoryAffineProEt` uses the over category with
  morphism property `⊤`. `AffineProEt.toProEt` changes only the object property
  using `proAffineEtale_le_weaklyEtale`. I read its Full and Faithful instances
  and the identities for the underlying object and structure map. Verdict:
  all over-X morphisms are retained, with no additional condition.
- Coverings: `AffineProEt.precoverage` is the comap of
  `Scheme.proetalePrecoverage` under inclusion followed by forgetting to
  schemes. `AffineProEt.topology` is exactly
  `(toProEt S).restrictedTopology (ProEt.topology S)`. I read Mathlib's
  `restrictedTopology` construction and `proetalePrecoverage =
  propQCPrecoverage WeaklyEtale`. Verdict: precisely the inherited
  pro-etale/fpqc coverings and their Grothendieck topology.

Edge cases: the empty affine scheme and zero ring are allowed; no `Nontrivial`
or `Nonempty` hypothesis restricts the objects. Empty covering families keep
ambient behavior: they cover an empty object, not a nonempty one. Filtered
presentation indices are nonempty as required for ind-etale presentations;
covering-family indices may be empty. There is no n, characteristic, coefficient
field, or module parameter to restrict. Arbitrary scheme universes u are
available, with objects in `Type (u + 1)` and presentation indices in `Type u`,
matching the dependencies' convention. There is no extra universe or instance
restriction hidden in the recorded signature.

Independent searches, using different queries from the worker:

- LeanFinder: "affine objects inverse limits of etale schemes full subcategory
  induced Grothendieck topology" returned eight ordinary etale/Zariski-site
  and affine-limit declarations, none defining this notion.
- Loogle: "GrothendieckTopology, Functor" returned no hits (unknown identifier
  in its index); this is not evidence of absence.
- Direct `rg` for `affine.*[ée]tale.*site`, `AffineProEt`, and
  `proAffineEtale.Over` in upstream `WeilConjectures` and project `lean/Sheaf`
  found the existing comparison module and no competing project definition.
  Direct Mathlib searches and source reads found the ambient site and generic
  topology restriction. I checked the matching declarations in the group
  clone rather than relying on the remote index or the older source tree.

No mismatch was found; no Lean or node field needed repair. There are no new
nodes, dependency modules, or statement corrections to audit, and no corrected
citer verdicts. No new proof, sorry, or hollow data definition is introduced.
The existing upstream module is reused unchanged; new-module docstring rules
do not require editing read-only upstream sources. The stored `lean.statement`
is verbatim the existing definition's signature. Second reading changes only
this report, adding the independent source, dependency, and edge-case audit.

I reran the scratch `ExistingChecks.lean` probe with `scompile.py`. It prints
the actual definition, inclusion, precoverage and topology bodies and checks
the category instance and spectrum equivalence. It passed without warnings in
1.7 seconds on the server, nice 19, two threads, 60 seconds per file. No local
compiler or library build was run. There are no delivered Lean files; delivery
also checks every recorded existing declaration in a fresh server probe.

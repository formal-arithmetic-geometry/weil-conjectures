## Worker report

The module states `AlgebraicGeometry.Scheme.isIso_proper_open_derived_support` with a
single `sorry` proof. It introduces no definitions, helper hypotheses, new nodes or
statement corrections. The declaration docstring retains all ten proof steps and their
named dependencies, including the separate injective acyclicity obligation. This is the
agent-extracted ambient support assertion, not an attribution of higher vanishing to
Stacks 09AG. I read that tag at https://stacks.math.columbia.edu/tag/09AG; it asserts the
degree-zero specialization vanishing only. The literature source tree is absent in this
read-only clone; the full node source record and proof were read here.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes X, T₁, T₂ | `{X T₁ T₂ : Scheme.{u}}` |
| Proper u : T₁ → T₂ | `(f : T₁ ⟶ T₂) [IsProper f]` (f renames u) |
| Open immersions j₁ and j₂ | `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)` and the two `IsOpenImmersion` instances |
| Both opens quasi-compact | `[QuasiCompact j₁] [QuasiCompact j₂]` |
| u composed with j₁ equals j₂ | `(_comm : j₁ ≫ f = j₂)` |
| Finite commutative coefficient ring | `(A : Type u) [CommRing A] [Finite A]` |
| Every unbounded K on the small pro-etale site | `(K : proEtaleDerivedCategory X A)` |
| Exact termwise j₁! | `(sfIntrinsicDerivedOpen A j₁).obj K`, the existing `sfIntrinsicExtensionByZero.mapDerivedCategory` |
| M = Ru_* j₁! K, ordinary and uncompleted | `(proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K)` |
| Actual canonical j₂! j₂* M → M | `(exceptionalOpenAdjunction j₂ A).counit.app M` with M expanded |
| This specified arrow is an isomorphism | `IsIso` of that component |
| No etale origin or boundedness restriction | No additional property of K is a binder |

Dependency declarations read and used (also through the transitive public imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- The scheme-conventions record is a convention, with no module/declaration;
  the class `AlgebraicGeometry.QuasiCompact` comes from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (not a new definition here).
- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`:
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`, read with `scompile.py --source`.
  The primary site record currently uses the equivalent fixed-scalar presentation.
  Our objects use the existing intrinsic `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`
  from `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, as all recorded operation and
  open-adjunction dependencies do. Its body is the ordinary Mathlib derived category of
  intrinsic modules over the constant sheaf of `ULift A`. The existing canonical
  `sfIntrinsicModuleEquivalence` identifies these with fixed-scalar sheaves of modules
  over `ULift A`; no category is copied and no equivalence is supplied as a hypothesis.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  underlying Mathlib `SheafOfModules` and its morphisms and abelian category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory.standard`, which the recorded intrinsic category uses verbatim.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback`, exact termwise inverse image.
  This publicly reexports `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`:
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`, defined as the K-injective
  right derived functor of the canonical constant-section module direct image.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence` and `sfIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact` and its three instances.
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`:
  `AlgebraicGeometry.Scheme.exceptionalOpenAdjunction`. Its left functor is the existing
  `sfIntrinsicDerivedOpen` from `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`.
  The counit is the localized actual termwise open-adjunction counit, not a chosen map.

All currently recorded proof-dependency modules are imported, including the product,
K-injective and truncation-limit interfaces. Proof nodes with no Lean record are left
for their own statements; none is needed to type this statement and no missing proof
node is assumed as a new hypothesis.

Edge cases: the empty scheme/open is allowed (all categories and functors still have
the recorded definitions); the zero ring is allowed (no `Nontrivial A`); K may be zero,
unbounded above and below, or without etale origin. Identity proper maps and either
identity open are included. There is no Noetherian, qcqs-scheme, cohomological-dimension,
constructibility or Tor hypothesis. Universes are explicit: schemes and the finite ring
are in u, the small site's objects in u+1 and morphisms in u, module values in u+1;
the published `ULift` realizes the same finite ring in the module universe. No equality
of the site's object and morphism universes is imposed. `autoImplicit false` is set.

Searches for an existing exact statement:

- `msearch.py leansearch`, query `proper direct image of extension by zero supported on
  open subscheme`: 8 hits, about function support, scheme open restriction, ideal-sheaf
  support and restriction of proper morphisms; no derived pro-etale statement.
- `msearch.py leanfinder`, query `proper direct image extension by zero counit isomorphism`:
  8 hits, mostly condensed equivalences and scheme-module restriction adjunctions;
  none concerns this extension-by-zero support assertion. The longer query recorded in
  searches.jsonl also returned only generic truncation/adjunction statements.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.counit`: 12 hits for the generic
  counit and adjunction API; this is the API used, not the geometric support result.
  The combined query `CategoryTheory.IsIso, CategoryTheory.Adjunction.counit` likewise
  returned generic adjunction equivalence results.
- `msearch.py grep`, query `proper.*[Ss]upport|[Pp]ro[Ee]tale.*[Cc]ounit`: 7 unrelated
  Mathlib function/ring support hits.
- `rg` on `lean/Sheaf` and `WeilConjectures`, for proper support, proper-open counits,
  intrinsic derived operations and the exact node id: no existing matching theorem.
  The bounded-below etale-origin comparison in `Sheaf.Paper.ProEtaleProperOpenComparison`
  was inspected; it has a different domain and conclusion. `FullCdAmbientAdjoint` only
  cites this node in its proof docstring. The upstream source has no node-id hit.

Validation: `scompile.py Q35 lem-sp-proper-open-derived-support` compiled the delivered
module cleanly as a separate library file (7.7 seconds); only the authorized wrapper
was used. No direct Lean/global build or Git command was run in the shared repository.
No `STATEMENT-DISPUTED` flag or node fault remains.

## Second reading by Q35

Independent reading of the node JSON and `ProperOpenDerivedSupport.lean`: the Lean
statement matches the node. No mathematical or Lean change was needed; this section
records the second reader's checks. The original worker report is retained.

Source check: I read the blueprint's `sk-prop-sf-existence/_section.md` in the local
literature mirror at `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`;
its text agrees with `dag/units/sk-prop-sf-existence.json`. Clause (b) is conditional
on FullCD and concerns compactification independence. This node isolates the proper/open
support input, rather than asserting the existence of that conditional adjoint. FullCD
is therefore not a hypothesis of this support lemma. I also read `proetale.tex`,
`section-extension-by-zero`, `definition-extension-zero` and `lemma-jshriek-zero`
(Tag 09AG), in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`, and checked
[09AG](https://stacks.math.columbia.edu/tag/09AG) and the current upstream TeX online.
There is no ambient Noetherian or characteristic assumption there. The specialization
lemma is only a sheaf-section vanishing result; neither the node nor the Lean docstring
claims that it proves higher vanishing. The separately named injective acyclicity step
remains a proof dependency, without becoming an extra hypothesis of the theorem.

The node's objects, hypotheses and conclusion, matched in order:

| Node item | Lean rendering and verdict |
| --- | --- |
| Three schemes X, T₁, T₂ | `{X T₁ T₂ : Scheme.{u}}`; exact, no scheme finiteness assumption. |
| Proper u : T₁ → T₂ | `(f : T₁ ⟶ T₂) [IsProper f]`; exact after renaming u. Mathlib's universally closed condition implies quasi-compactness, so its locally finite type formulation agrees with properness. |
| Open immersions j₁ and j₂ with common source X | `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]`; exact. These are the recorded scheme open immersions, not merely open maps. |
| Both open immersions quasi-compact | `[QuasiCompact j₁] [QuasiCompact j₂]`; exact, with no assumption that the schemes themselves are quasi-compact. |
| u ∘ j₁ = j₂ | `(_comm : j₁ ≫ f = j₂)`; exact categorical order. The underscore does not remove the hypothesis. |
| Finite commutative ring A | `(A : Type u) [CommRing A] [Finite A]`; exact, including the zero ring. |
| Constant coefficient module sheaves on the small pro-etale site | `proEtaleDerivedCategory X A` and the corresponding categories on T₁ and T₂; exact intrinsic constant-ring presentation, as checked below. |
| Ordinary unbounded derived categories, arbitrary K | `(K : proEtaleDerivedCategory X A)`; no Plus subcategory, constructibility, Tor, etale-origin or completeness predicate. |
| Exact termwise j₁!K | `(sfIntrinsicDerivedOpen A j₁).obj K`; this unfolds to the existing extension-by-zero functor's `mapDerivedCategory`. |
| M = Ru_* j₁!K | `(proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K)`; exact ordinary K-injective right derived direct image. |
| j₂* followed by j₂! | The source of `(exceptionalOpenAdjunction j₂ A).counit.app M` is definitionally `(sfIntrinsicDerivedOpen A j₂).obj ((sfIntrinsicDerivedPullback A j₂).obj M)`; exact order and object. |
| The actual canonical counit to M | That same `counit.app M`; exact specified arrow, with no freely supplied map, arbitrary adjunction or mere object isomorphism. |
| The specified arrow is invertible for every K | `IsIso (...)`, under the universal K binder; exactly the sole conclusion. |

I opened every statement-dependency node and the declarations serving it. In particular:

- `Scheme`, `IsProper`, `IsOpenImmersion`, `QuasiCompact`, `SheafOfModules`, and
  `DerivedCategory`/`HasDerivedCategory.standard` were read in the pinned Mathlib source.
  The scheme-conventions node expressly introduces no separate definition.
- The current recorded `ProEtale.ModuleDerivedCategory` was read using
  `scompile.py --source WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`.
  It is the fixed-scalar sheaf presentation of the same module category. I also opened
  `ProEtaleDerivedCategory.lean`: the intrinsic presentation used here is the ordinary
  derived category of `SheafOfModules` over the constant sheaf of `ULift A`.
  `RingedSiteModules.lean` transparently abbreviates that Mathlib module notion.
  These are published equivalent presentations, not definitions introduced by this delivery.
- I opened `ProEtaleIntrinsicExtensionByZero.lean`,
  `ProEtaleFiniteModuleIntrinsicComparison.lean`, and
  `ProEtaleIntrinsicExtensionByZeroExact.lean`. The equivalence is the canonical
  associated-module-sheaf realization, with inverse determined by equivalence; its
  data are not chosen from a bare existence claim. Extension by zero transports the
  existing localization/sheafification construction, and exactness provides termwise
  derived descent. No private replacement is present.
- I opened `ProEtaleIntrinsicFiniteOperations.lean` and
  `ProEtaleOpenSquareExchange.lean`: inverse image is the existing fixed-scalar
  inverse image transported by those same equivalences, and `sfIntrinsicDerivedOpen`
  is precisely `(sfIntrinsicExtensionByZero j A).mapDerivedCategory`.
- I opened `ProEtaleInverseImage.lean`, `ProEtaleConstantDerivedDirectImage.lean`,
  and the upstream right-derived K-injective API. Direct image uses base-change
  precomposition and the canonical constant-section ring map, followed by
  `rightDerivedFunctor`. There is no completion or replacement coefficient map.
- I opened `IntrinsicDerivedOpenAdjunction.lean` in full. Its actual definition
  localizes the termwise complex adjunction of `sfIntrinsicOpenAdjunction`; that
  sheaf adjunction composes the published open adjunction with the realization
  equivalences. Hence its counit is the node's canonical derived open counit.

Edge cases: empty X, empty ambient schemes when the morphisms exist, the zero complex,
identity proper maps, identity opens, and empty closed complements are allowed. There
is no nonempty-site or nontrivial-ring binder. The coefficient characteristic is
unrestricted. No integer n or index set occurs in the statement, so there is no
positive-degree or nonempty-index exclusion. Universes are bound explicitly by
`universe u` and `autoImplicit false`: schemes and A are in u, small-site objects in
u+1 and morphisms in u, module values in u+1 through `ULift`. In particular the site
universes have not been equated. Using a common universe for the finite ring and
schemes is the published finite-coefficient convention and excludes no finite ring
up to its canonical size realization. K is unbounded in both directions.

Independent duplicate searches (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: `counit extension by zero proper pushforward support derived sheaves`:
  eight hits, for generic module adjunction/section maps and scheme O-module
  restriction. None states this geometric pro-etale derived support assertion.
- Loogle: `CategoryTheory.Adjunction.counit, CategoryTheory.IsIso`: twelve generic
  equivalence/fully-faithful adjunction results. These do not give proper support.
- LeanSearch: `If a proper morphism is the identity on an open subscheme then its
  derived direct image of extension by zero is supported on that open`: eight
  scheme restriction, ideal-sheaf support and morphism-locality hits; no match.
- Grep: `proper.*[Ss]hriek|[Cc]ounit.*[Ss]upport|[Ss]upport.*[Dd]irect[Ii]mage`:
  no Mathlib hits. Independent `rg` over the pinned Mathlib, upstream
  `WeilConjectures`, side `lean/WeilConjectures`, and `lean/Sheaf` used proper/open,
  direct-image/support and counit combinations, plus the exact proposed declaration
  and blueprint id. No existing exact theorem was found.
- I opened `Sheaf.Paper.ProEtaleProperOpenComparison`: its comparison applies only to
  bounded-below objects pulled back from the etale site, so cannot replace this node.
  `FullCdAmbientAdjoint.lean` uses the support input in its proof discussion; it does
  not already state this theorem. `DeltaProperPushforward.lean` concerns the etale
  ambient duality comparison, with different categories and conclusion.

H5/H6/H8/H9 checks: this delivery contains one theorem and no definition or helper;
its sole proof is `sorry`. The module and declaration docstrings name the source and
this blueprint id. I matched all ten proof paragraphs against the node, including
sheaf support, separately named injective acyclicity, countable products, and the
canonical truncation-triangle/counit argument. Recorded proof modules are imported;
unrecorded proof prerequisites are not new assumptions. Every Lean line is at most
100 characters. There are no local aliases, local instances, hidden let binders in
the statement, or unbound variables. The node's `lean.statement` is verbatim equal
to the source signature, checked by extraction. Compared with the shared node, only
`lean` changed. There is no `statement_change`, new node or dependency-module delivery
to audit, and no citer audit is required. No mismatch or unresolved statement dispute
was found; only this second-reading report was added.

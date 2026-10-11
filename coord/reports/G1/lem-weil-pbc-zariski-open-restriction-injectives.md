## Worker report

The module `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives` states the entire
node in three named theorems, all with `sorry` proofs. No definitions or nodes were added,
and no statement correction was needed.

Hypotheses and clauses:

- The scheme is `(X : Scheme.{u})`; the arbitrary open subscheme is `(U : X.Opens)`.
  `Opens.grothendieckTopology X` and `Opens.grothendieckTopology U` are their Zariski sites.
  `Sheaf ... AddCommGrpCat.{u}` gives their abelian sheaf categories.
- The functor is Mathlib's `U.sheafRestrict (C := AddCommGrpCat.{u})`, not a new definition.
  Its definition in `Topology.Sheaves.SheafCondition.Sites` uses the image-of-opens functor
  of the open inclusion and `sheafPushforwardContinuous`, so on W it is F(W viewed in X),
  and on morphisms it is the component at that same open. The sheaf condition uses exactly
  the open coverings inherited from X.
- Clause (1), additivity: `zariski_open_restriction_additive` asserts `Functor.Additive`.
  It has an instance attribute so the other statements can use the mapped short complexes
  and complexes, without an extra additivity hypothesis or any file-local instance.
- Clause (1), exactness at a middle object: the first conjunct of
  `zariski_open_restriction_injectives` quantifies over every `ShortComplex`, and asserts
  `S.Exact → (S.map ...).Exact`. Thus there is no restriction to short exact sequences.
- Clause (2): its second conjunct quantifies over every sheaf I and asserts
  `Injective I → Injective (restriction.obj I)`.
- Clause (3): `zariski_open_restriction_injectiveResolution` takes any F and
  `I : InjectiveResolution F`, and supplies `J : InjectiveResolution (restriction.obj F)`.
  The equality `h` identifies its cocomplex with `restriction.mapHomologicalComplex`
  applied to I, so all terms and all differentials are the restricted ones. Its next
  equation identifies the augmentation at zero with `restriction.map (I.ι.f 0)`, transported
  along h. Other components of an augmentation from `single₀` are zero automatically.
  Mathlib's nonnegative indexing expresses the node's vanishing in negative degrees.
- Clause (3), sections: the last conjunct is an equality of whole cochain complexes of
  abelian groups. The left side evaluates the restricted complex at the terminal open
  `⊤ : Opens U`, the right side evaluates I at `U : Opens X`, using `sheafSections` on
  each site. This includes differentials, not merely equality of terms or cohomology.

Dependency declarations read and used:

- `def-sc-zariski-site`: `Opens.grothendieckTopology` from
  `Mathlib.CategoryTheory.Sites.Spaces`; `CategoryTheory.Sheaf` is the site form of the
  same sheaf category as the recorded `TopCat.Sheaf` wrapper.
- `def-weil-pbc-sites-and-cohomology`: `CategoryTheory.Sheaf` and
  `CategoryTheory.sheafSections` from `Mathlib.CategoryTheory.Sites.Sheaf`, imported via
  the recorded `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. The node's cohomology
  `Sheaf.H'` is not needed in this restriction lemma.
- `def-weil-pbc-exact-sequence`: `CategoryTheory.ShortComplex.Exact` from
  `Mathlib.Algebra.Homology.ShortComplex.Exact` (imported through the resolution module),
  exactly the recorded middle-exactness notion.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` from
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `CategoryTheory.InjectiveResolution`
  from `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The latter bundles an
  N-indexed complex, injective terms, and a quasi-isomorphism from `single₀ F`.

Edge cases checked before writing: U empty, U all of X, X empty, the zero sheaf,
zero differentials and a zero resolution, and degree zero. None is excluded by any
binder. At the empty open the sheaf category is trivial; at the full open restriction
is canonically the identity. No separatedness, finiteness, nonemptiness or characteristic
hypothesis is imposed. Universe u is arbitrary; coefficients are in the same universe
as the small Zariski site, as in the recorded site convention. The equality of section
complexes is appropriate: the image of the terminal open of U is U as an open of X,
and equality of those open objects transports evaluation to the same abelian groups.

Source read: the local Stacks sources, `sites-cohomology.tex`, Lemma
`lemma-cohomology-of-open` (03F3), and `cohomology.tex`, the same label (01E1), including
both proofs. They state injective restriction and use the restricted resolution and
section equality. Their ringed-site assertion is applied to the constant integer ring,
as the DAG requests. The docstrings record each of the DAG's four proof steps.

Searches for an existing statement:

- msearch leansearch: "restriction of abelian sheaves to an open subset preserves
  injective resolutions"; unavailable, Internal Server Error.
- msearch leanfinder: "restriction to an open subset of abelian sheaves is exact preserves
  injective objects and injective resolutions"; eight hits on general right derived
  functors and injective resolutions, none giving this statement.
- msearch loogle: "TopCat.Sheaf.restrict, TopologicalSpace.Opens.sheafRestrict,
  CategoryTheory.InjectiveResolution"; no hits, unknown first identifier.
- msearch grep: `sheafRestrict|overPullback` in `Topology/Sheaves`; found existing
  `Opens.sheafRestrict` and comparison with the slice-site restriction, no theorem covering
  the three clauses.
- rg over Mathlib Sites, Topology/Sheaves and Injective/Resolution: inspected
  `sheafRestrict`, `sheafPushforwardContinuous`, `sheafSections`, and resolution signatures.
- rg `sheafRestrict|restrict.*[Ii]njective|[Ii]njective.*restrict|` followed by the item id,
  over `WeilConjectures` and `lean/Sheaf`: found étale and pro-étale analogues and ringed-space
  module analogues, none stating this abelian Zariski result. Searching the exact item id
  in the upstream source gave no match. No second definition was introduced.

Validation: local single-module compile; final server compile and preflight via
`deliver2.py G1 lem-weil-pbc-zariski-open-restriction-injectives --no-push`.
No disputed statements or dependency faults found.


## Second reading by G1

Independent second reader: I opened the sandbox node and all three theorem signatures,
the four dependency nodes and the Mathlib declarations they record. I read the source
proofs of Stacks 03F3 and 01E1 in the available local Stacks source copy (the literature
checkout in this clone is absent). Both lemmas assume only a ringed site/space and an
arbitrary object/open. Specializing the ring to the constant integers gives abelian
sheaves; neither proof assumes Noetherianity, separation, quasi-compactness, or a field.

The node's objects, hypotheses, and conclusions, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})` in each theorem | Exact; no property instances required. |
| Arbitrary open subscheme U | `(U : X.Opens)` | Exact; its subtype is the underlying open space. |
| Small Zariski sites of X and U | `Opens.grothendieckTopology X` and `Opens.grothendieckTopology U` | Exact; read Spaces.lean: covering sieves cover each point, morphisms are inclusions. |
| Categories of abelian sheaves | `Sheaf ... AddCommGrpCat.{u}` | Exact; the dependency's full subcategory of abelian presheaves satisfying the sheaf condition. |
| Restriction of objects, maps and restriction maps | `U.sheafRestrict (C := AddCommGrpCat.{u})` | Exact; read Sites.lean and Continuous.lean: precomposition with the image-of-opens functor, including natural transformation components. |
| (1) Additive functor | `zariski_open_restriction_additive`, result `.Additive` | Exact; globally registered theorem instance supports later mapped complexes, without adding a hypothesis. |
| (1) Preserve exactness at every middle term | First conjunct of `zariski_open_restriction_injectives`, `∀ S : ShortComplex ..., S.Exact → (S.map ...).Exact` | Exact; not restricted to short exact sequences. |
| (2) Every injective sheaf remains injective | Second conjunct, `∀ I : Sheaf ..., Injective I → Injective (...obj I)` | Exact; uses categorical injectivity, not injectivity of a morphism of sheaves. |
| (3) Every F and every injective resolution | Binders `F : Sheaf ...` and `I : InjectiveResolution F` | Exact; no chosen or special resolution. |
| (3) Termwise restricted complex, with restricted differentials | Existential `J`, equality `h : J.cocomplex = (...mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex` | Exact; equality identifies the entire complex. |
| (3) Restricted augmentation | `J.ι.f 0 ≫ eqToHom (congrArg (fun K ↦ K.X 0) h) = ...map (I.ι.f 0)` | Exact; target transport is necessary, and positive-degree components from single-zero are zero. |
| (3) Equality of section complexes | Last equality in `zariski_open_restriction_injectiveResolution`, evaluation at `op ⊤` on U versus `op U` on X, both mapped as complexes | Exact; compares differentials as well as terms, with no cohomology-only weakening. |

Dependency checks: `def-sc-zariski-site` records `Opens.grothendieckTopology` and
`TopCat.Sheaf`; the latter is the wrapper for the same site-sheaf category used here.
For `def-weil-pbc-sites-and-cohomology`, I read `Sheaf`, `sheafSections` (the flipped
inclusion into presheaves), and `sheafPushforwardContinuous`; no alternative section
functor is introduced. For `def-weil-pbc-exact-sequence`, I read `ShortComplex.Exact`
and `ShortComplex.exact_iff_image_eq_kernel` in Abelian/Exact.lean: this is precisely
image = kernel at the middle term. For `def-sp-injective-resolutions`, I read
`Injective.factors` and every field of `InjectiveResolution`: a nonnegative cochain
complex of injectives with quasi-isomorphic augmentation from `single₀ F`. This is the
recorded nonnegative resolution convention, not an extra boundedness hypothesis.
There are no new definition nodes, dependency modules, or statement corrections to audit.

Edge cases: U empty, U = X, and X empty are allowed by the same binders; the zero
sheaf and every resolution of it are allowed. Degree zero is explicitly handled by
the augmentation equation; all positive degrees and their differentials occur in the
complex equality. Negative degrees are zero in the dependency's ℕ-indexed encoding.
Empty coverings are part of the existing sheaf condition, and no covering index set
is constrained here. No characteristic is mentioned or excluded. The universe `u` is
bound and arbitrary, and `AddCommGrpCat.{u}` is the dependency's small-site convention;
there is no independent lower test universe making a hypothesis vacuous.

Independent searches (different conceptual wording from the first reader):

- LeanFinder via msearch: "inverse image along an open embedding of topological spaces
  preserves injective abelian sheaves". Eight hits: the open-embedding sheaf-condition
  lemma and locally injective morphism lemmas, not injective objects or this result.
- Loogle via msearch: `TopologicalSpace.Opens.sheafRestrict`. Ten hits: the existing
  restriction definition, component equations, slice-site comparison and conditional
  right-adjoint instance; no theorem giving all the node's clauses.
- LeanSearch via msearch: "An open subspace restriction functor on abelian sheaves
  preserves injective resolutions". Service unavailable (Internal Server Error);
  no mathematical verdict inferred from this failure.
- `rg` over Mathlib Topology/Sheaves and CategoryTheory/Sites, upstream
  WeilConjectures, and project lean/Sheaf for `sheafRestrict` and both orders of
  restriction/injective. Read the upstream Cohomology/Clopen.lean restriction wrapper,
  its additive instance and adjunction to direct image. These reuse continuous
  pushforward and do not assert injective preservation or the resolution/section
  conclusion. Read the project's RestrictInjectiveResolution.lean and
  ModuleOpenRestrictionInjectives.lean: they concern modules over the structure sheaf,
  not the abelian-sheaf category here. Étale/pro-étale analogues use different sites.
  No existing declaration realizes this entire node; no definition is duplicated here.

No mismatch found. I left the Lean module and node record unchanged. Every proof is
`sorry`; there are no hollow definitions, private notions, local notation, or unbound
variables/universes. The source-bearing docstrings cover the four proof steps and their
DAG references. The node's `lean.statement` matches the main theorem signature verbatim.
Local single-file compilation passed cleanly (exit 0). Delivery dry run and final
server compilation/preflight are performed after this report is appended.

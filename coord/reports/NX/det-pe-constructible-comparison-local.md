## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal` states
`AlgebraicGeometry.ProEtale.proEtaleClassical_zariskiLocal`, with one `sorry` and no
new definitions. The statement is unchanged from the DAG and its current blueprint
source, `main-20261015`, detail `sk-thm-pe-constructible-comparison-local` and its proof.
The node copy changes only `lean`.

Hypotheses and conclusions, clause by clause:

- “Let X be a scheme” is `(X : Scheme.{u})`, with no finiteness, separation, or
  nonemptiness assumption.
- “Λ a discrete commutative ring” is `(Λ : Type (u + 1)) [CommRing Λ]`. The coefficient
  category is `ModuleCat.{u + 1} Λ`, exactly as in the recorded module comparison
  dependency. Discrete coefficients carry no additional topology. As explained in that
  dependency's source and record, a sheaf valued in fixed Λ-modules encodes a module
  over the constant ring sheaf; scalar action extends uniquely through sheafification.
- “F a Λ_X-module sheaf on X_Proet” is
  `(F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))`, using the actual
  small pro-etale site, not an arbitrary equivalent site or coefficient ring.
- “X = union_a X_a is an open covering” is the first conjunct's
  `∀ (I : Type w) (U : I → X.Opens), (⨆ i : I, U i) = ⊤ → ...`.
  The index universe `w` is explicitly bound and independent, so covers of any size,
  empty indices, repeated opens, and empty opens are permitted. The opens have their
  canonical open-subscheme structures `(U i).toScheme` and inclusions `(U i).ι`.
- “each restriction F|_{X_a} is classical” is the next premise `∀ i : I, IsClassical ...`.
  Its argument is the underlying set sheaf of
  `(openImmersionRestriction (ModuleCat.{u + 1} Λ) (U i).ι).obj F`.
  This is the existing sectionwise restriction, which on an object `T → U i` evaluates
  F at `T → U i → X`; it is not an arbitrary pullback or local model.
- “then F is classical” is the first conjunct's conclusion
  `IsClassical ((sheafCompose (Scheme.ProEt.topology X)
  (forget (ModuleCat.{u + 1} Λ))).obj F)`.
- “Conversely the restriction of a classical sheaf to an open subscheme is classical”
  is the second conjunct, from the same global `IsClassical` predicate to
  `∀ U : X.Opens, IsClassical ...` on its sectionwise restriction. This conjunct has
  no cover premise. Canonical open subschemes represent every open subscheme up to
  its canonical isomorphism; `IsClassical` is invariant under isomorphism.

The statement dependency is used through its recorded public module
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`, declaration
`AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules`. I read its full docstring
and signature: arbitrary discrete coefficients, adjunction, finite-limit and
finite-colimit preservation, Hom-set bijectivity, canonical counit criterion, and
essential-image characterization. Its underlying-set `IsClassical` is the predicate
`AlgebraicGeometry.ProEtale.IsClassical` from
`Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, defined by bijective continuity maps
for every affine presentation. No second classicality predicate is introduced.

The other public import is
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`, for
`AlgebraicGeometry.ProEtale.openImmersionRestriction`. I read its definition, its
`localizationRestriction` implementation, section formula, and the canonical
`upperStarIsoOpenImmersionRestriction`. It uses composition of structure maps and
continuous sheaf pushforward, with no Kan extension or sheafification needed to
define restriction. The open-immersion and weakly-etale instances are supplied by
the canonical inclusion of an open subscheme, with no extra hypotheses.

The stated proof dependencies are imported without `public`:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`:
  `AlgebraicGeometry.Scheme.Etale.overEquiv` and the recorded localization companions.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison` and its module specialization.
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`:
  `CategoryTheory.GrothendieckTopology.plus_sheafification_theorem`.
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`:
  `SheafOfModules.exists_moduleSheaf_of_cover`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`:
  `SheafOfModules.existsUnique_hom_of_cover`.

The Mathlib match for `sk-def-pe-site` is the already imported
`AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`, in
`Mathlib.AlgebraicGeometry.Sites.Proetale`. No separate module is required for this
Mathlib leaf. The declaration docstring records all four DAG proof steps, including
coefficient-compatible restriction, lifting the overlap cocycle, effective etale
module descent, and gluing the comparison isomorphisms and inverses.

Edge cases checked before writing: the empty scheme admits an empty open covering,
and the first clause does not impose `Nonempty I`; a nonempty scheme does not satisfy
the empty cover equation. Empty open members and the empty open in the converse
are allowed. The full open gives identity restriction. Neither finite covers nor
affine covers are required. Zero rings and zero sheaves are allowed, since there is
no `Nontrivial` or nonzero premise. The converse is independent of a chosen cover.
The coefficient and module universes agree with the recorded dependency, while the
cover index has its own unrestricted universe. No statement dispute, missing notion,
or unusable dependency was found.

Searches for existing declarations (2026-10-17):

- `msearch.py ... leanfinder "classicality of a pro-etale module sheaf is local for an
  open covering and restriction preserves classicality"`: eight hits on the etale
  topology, local properties of ring/scheme morphisms, and module local generators;
  no matching classicality theorem.
- `msearch.py ... leansearch "classicality of proetale module sheaves is local on open
  covers"`: eight hits on local morphism properties and `iff_of_openCover`; no match.
- `msearch.py ... loogle '"sheafPullback"'`: ten generic site pullback/adjunction and
  topological open-embedding hits; none states this theorem.
- `msearch.py ... grep 'proetale|pro.etale' AlgebraicGeometry`: ten hits in Mathlib's
  pro-etale-site and ell-adic-cohomology modules; site definitions only, no match.
- `rg -n 'IsClassical|isClassical|classicality'` in the named slopmaster2
  `WeilConjectures/` source: only three unrelated triangulated classical-generator
  hits. A search for this item's id in the same tree had no hits.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for classical restriction/locality names
  found the module comparison and image files, continuity predicates, and
  `ProEtaleLocallyClassicalEtaleCover`. I read that latter module: its theorem concerns
  locally classical set sheaves on a pro-etale covering and etale-local inhabitedness,
  with no arbitrary-open restriction clause; it is not an exact match for this node.
- `rg` in the named source trees for `upperStarIsoOpenImmersionRestriction` found the
  existing canonical restriction API used here. Its definition and section formula
  give precisely the required restriction, so no helper definition was added.

Validation: `scompile.py NX det-pe-constructible-comparison-local` compiled the delivered
file cleanly, including the current dependency overlay and the file's library-path
check, with no errors or warnings. `autoImplicit false` is set in the module, and
both universes and every variable are explicitly bound. Only the theorem proof is
postponed. The second reader must supply the independent reading before delivery.


## Second reading by NX

Independent second reading, 2026-10-17. I opened the sandbox node, its Lean module,
the blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-thm-pe-constructible-comparison/sk-thm-pe-constructible-comparison-local.md`
and `.proof.md`, and the containing unit and chapter. The detail explicitly assumes
only a scheme and a discrete commutative ring. The qcqs and Noetherian hypotheses
in the containing constructible-comparison theorem belong to that theorem; this
locality detail does not assume them. The Lean faithfully states the detail.

Object/hypothesis/conclusion inventory and match (H3):

1. Scheme X: `(X : Scheme.{u})`. Verdict: exact; no affine, qcqs, Noetherian,
   separated, connected, or nonempty condition.
2. Discrete commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`.
   Verdict: exact in the recorded fixed-coefficient encoding. Discreteness is
   expressed by using ordinary modules, with no coefficient topology. No field,
   finite-ring, Noetherian-ring, characteristic, or `Nontrivial` assumption.
3. Module sheaf F over the constant coefficient sheaf on the small pro-etale site:
   `(F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))`.
   Verdict: the same category as `proEtaleClassicalSheavesModules`, not a sheaf on
   the big site or a module over the scheme structure sheaf. The dependency record
   `def-weil-pbc-etale-sheaves` expressly permits this encoding alongside intrinsic
   constant-ring `SheafOfModules`; the scalar actions extend through sheafification.
4. Arbitrary open covering: `∀ (I : Type w) (U : I → X.Opens),
   (⨆ i : I, U i) = ⊤ → ...`. Verdict: union equals X, with every index and open
   bound and no finite, affine, small-relative-to-u, or nonempty-index premise.
   The canonical schemes `(U i).toScheme` and arrows `(U i).ι` are the open
   subschemes and their inclusions.
5. Classical restrictions on every member: the next premise is `∀ i : I,
   IsClassical ((sheafCompose ... (forget (ModuleCat.{u + 1} Λ))).obj
   ((openImmersionRestriction (ModuleCat.{u + 1} Λ) (U i).ι).obj F))`.
   Verdict: genuine restriction and exactly the existing classicality predicate.
   The module structure is retained by restriction; forgetting it only expresses
   the equivalent underlying-set criterion of the classical-definition node.
6. Global conclusion: the first conjunct ends in `IsClassical
   ((sheafCompose (Scheme.ProEt.topology X)
   (forget (ModuleCat.{u + 1} Λ))).obj F)`. Verdict: exactly global classicality,
   without an extra local model or compatibility assumption.
7. Converse: the second conjunct assumes this same global predicate and concludes
   `∀ U : X.Opens, IsClassical ...` for its restricted module sheaf. Verdict: every
   open subscheme, independently of a covering. Opens represent arbitrary open
   immersions up to their canonical image isomorphism, and classicality is invariant
   under isomorphism. The two conjuncts express precisely the two source clauses;
   their quantifier order does not require choosing a cover before the converse.

Dependency reading, including actual signatures and data:

- I read `det-pe-classical-sheaves-modules` and
  `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules` in full. Its theorem
  accepts exactly `X : Scheme.{u}` and `Λ : Type (u+1)` with `CommRing Λ`; it gives
  the canonical comparison adjunction, finite-limit/finite-colimit preservation,
  full faithfulness, the counit criterion and essential image. The last two
  clauses use the same underlying-set `IsClassical` as this item.
- I opened `det-pe-classical-definition-continuity-map` and its module
  `ClassicalContinuityMap`. `IsClassical` quantifies over every cofiltered affine
  etale presentation in the common larger universe and tests bijectivity of the
  canonical colimit restriction map. Its statement explicitly equates module
  classicality with classicality of the underlying set sheaf. Thus the predicate
  in this item is neither a private substitute nor constructibility.
- The group-clone `LowerShriek.OpenImmersion.Defs` is a compatibility re-export.
  I followed it to the actual framework source
  `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Open/Defs.lean`
  and read `localizationRestriction`, `openImmersionRestriction`, and their section
  formulas, also comparing the older source. Restriction is continuous pushforward
  along `MorphismProperty.Over.map`: at `T → U` it gives F at `T → U → X`.
  Despite the directory name, the declaration accepts an arbitrary coefficient
  category `A` with `Category.{u+1} A`; no finiteness of Λ is required. The open
  inclusion supplies `IsOpenImmersion` and hence weak etaleness, without adding a
  hypothesis to the item. I read `coord/pefw-upstream-framework.md` as required.
- I opened all eight proof-dependency nodes and their recorded signatures/modules:
  `Scheme.Etale.overEquiv` and its cocontinuity/sheaf equivalences,
  `Scheme.ProEt.weaklyEtale_localization`, `Scheme.proEtaleSiteComparison`,
  `GrothendieckTopology.plus_sheafification_theorem`,
  `SheafOfModules.exists_moduleSheaf_of_cover`,
  `SheafOfModules.existsUnique_hom_of_cover`, and the Mathlib `Scheme.ProEt`
  site/topology match, together with the module-comparison dependency above.
  I read the Stacks text for Sites localization 00XZ, double-plus theorem 00WB,
  gluing 04TR and morphism gluing 04TQ, Modules on Sites 03EM, and pro-etale cover
  comparison 098B. These do not add global finiteness assumptions. The module's
  docstring follows the node's four proof steps: restriction compatibility,
  uniquely lifted overlap cocycles, effective module descent, and gluing the
  comparison maps and their inverses. All recorded proof imports are present.

Edge cases: an empty index type makes the union bottom, so the cover premise allows
it precisely for an empty scheme; there is no `Nonempty I`. Empty cover members,
repeated opens and the empty open in the converse are allowed. The full open yields
identity restriction up to its canonical isomorphism. The zero sheaf and zero ring
are included. There is no n parameter, degree bound or characteristic restriction.
The declared `u` and `w` bind all universes. `Scheme.ProEt` keeps site objects in
u+1 and morphisms in u; `ModuleCat.{u+1} Λ` and the underlying `Type (u+1)` sheaf
match the dependency's coefficient convention without identifying site universes.
The index universe w is independent: this is a union of opens, not a diagram of
schemes whose limit could require a size restriction. A large redundant cover can
be replaced by its set of distinct opens, so no larger coefficient sheaf is forced.

Independent H4 searches, using queries different from the first worker:

- `msearch.py NX det-pe-constructible-comparison-local leanfinder
  "pro-etale classical sheaves descend over Zariski open subsets"`: eight hits on
  etale sites, their objects and forgetful functors; no locality theorem.
- `msearch.py ... loogle '"IsClassical"'`: three triangulated-generator hits;
  no pro-etale statement.
- `msearch.py ... leansearch "An etale inverse image sheaf on the proetale site
  remains in the essential image after open restriction"`: eight ringed-space
  restriction, stalk and open-immersion hits; no matching theorem.
- `msearch.py ... grep 'classical|[Zz]ariski.*[Ll]ocal' AlgebraicGeometry/Sites`:
  fourteen site and morphism-locality hits; none states classicality locality.
  Direct `rg` on Mathlib's `CategoryTheory/Sites` for `IsClassical`, `isClassical`
  and `classicality` found no match.
- Direct `rg` over the named slopmaster2 `WeilConjectures`, the group framework and
  `lean/Sheaf/AlgebraicGeometry`, including classical/local/restriction variants,
  found only unrelated triangulated generators upstream and the existing
  continuity, comparison and locally-classical modules in this project.
  I opened `ProEtaleLocallyClassicalEtaleCover` in full: its set-sheaf theorem
  concerns a pro-etale cover and etale-local sections, not these two arbitrary-open
  module-sheaf clauses. It is a related tool, not an exact existing match.

No new definition node, dependency-module delivery, statement correction, private
copy, or hollow definition is present or needed. I found no mismatch requiring a
Lean or node edit. The only change of this second reading is this report section;
`## Worker report` is preserved. The postponed theorem alone has `by sorry`.
Module and theorem docstrings carry the source and blueprint id; every source line
is at most 100 characters, and `autoImplicit false` plus explicitly declared
universes leave no unbound variables. I checked programmatically that
`lean.statement` is verbatim equal to the theorem signature.

Validation: `scompile.py NX det-pe-constructible-comparison-local` with the absolute
sandbox module path passed both sandbox and library-path compilation (1.8 s and
2.0 s), without errors or warnings. No live source or global build was changed.

## Worker report

Item: `lem-weil-pbc-ringed-hypercover-injective-augmentation`.
Module: `Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation`.
Declaration: `CategoryTheory.ringedHypercover_injective_augmentation_exact`.
The only declaration is a theorem with `sorry`; no definition or instance is added.
The original node is unchanged except for `lean`.

### Hypotheses and conclusions

- Small site: `{C : Type u} [SmallCategory C]`, `J : Precoverage C`, and
  `[J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
  [J.HasPullbacks]` are precisely the recorded site axioms. Sheaves use
  `J.toGrothendieck`. The usual reindexing convention is built into presieves.
- Subcanonical: `[J.toGrothendieck.Subcanonical]`, so each `yoneda.obj V` is a sheaf.
- Universes: explicit `u v r`; rings in `max u r`, modules in `max u v r`.
  The module universe contains the site and ring universes. Arbitrary small sites
  fit after the skeleton/size convention; no independent smaller testing universe
  can make the matching-cover condition vacuous. Matching tests range over ALL
  `T : C`, including every representable test of the sheaf condition.
- Commutative ring sheaf: `R : Sheaf J.toGrothendieck CommRingCat.{max u r}`.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` supplies the very same sheaf
  viewed as a ring sheaf for Mathlib's module-sheaf definition.
- Injective R-module sheaf: `I : ringedSiteModules ...` and `[Injective I]`.
  This uses the dependency's recorded general-site abbreviation verbatim, whose
  objects and morphisms are exactly `SheafOfModules`. No constant coefficients,
  scheme, or additional acyclicity hypothesis is substituted.
- Object and augmented simplicial object: `W : C`, `U : SimplicialObject C`,
  and the natural transformation `e : U ⟶ (Functor.const ...).obj W`.
  Naturality says the augmentation commutes with every simplex operator, including
  all face and degeneracy maps.
- Hypercover: `hcover` spells out local surjectivity onto each sheaf matching limit.
  For a test `T`, `w : T ⟶ W`, and every lower simplex operator
  `θ : Δ ⟶ [n]` with `Δ.len < n`, `p Δ h θ : T ⟶ U_Δ` is its section.
  The first implication says all these sections are over `w`; the second is their
  compatibility under all lower simplex operators. The conclusion gives a covering
  sieve `S` and a local lift `t` with both the specified augmentation and all the
  specified faces. This is equivalent to the epimorphism of sheaves of sets in
  the node by its existing proof-dependency records:
  `Sheaf.createsLimitsOfShape` (matching limits sectionwise) and
  `Sheaf.isLocallySurjective_iff_epi` (local lifting iff epi).
  For `n = 0` the lower tuple is empty, so this says exactly `h_U₀ → h_W` is epi.
  For `n = 1` the two vertex sections have a common augmentation and lift locally.
  Higher tuples are the same finite proper-face matching objects: a lower simplex
  map factors as a degeneracy followed by a proper face, and compatibility makes
  extension from proper faces unique. There is no representability assumption on
  the matching sheaf and no existence assumption for matching limits inside C.
  Covering sieves contain covering families by the site's recorded axioms.
- Cochain terms and differential: each lambda has domain
  `I.val.obj (op (U _⦋n⦌)) = I(U_n)`, and its value is
  `∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s`.
  Thus it is precisely the sum of all n+2 face restrictions with alternating signs.
- Canonical augmentation: `I.val.map (e.app (op (SimplexCategory.mk 0))).op`.
  Its source is I(W), target I(U₀); it is the actual restriction, not an arbitrary
  morphism or mere existence of some comparison isomorphism.
- Exactness at I(W): the first conjunct is `Function.Injective` of this restriction.
  This is exactness after the left zero in `0 → I(W)`.
- Exactness at I(U₀): the second conjunct is `Function.Exact` of the augmentation
  and the displayed degree-zero differential.
- Exactness at every I(U_p), p>0: `∀ n : ℕ, Function.Exact δⁿ δⁿ⁺¹` is exactness
  at I(U_(n+1)). Every positive degree is included.
- R(W)-modules and quasi-isomorphism: the node explicitly states the equivalent
  exact augmented sequence, which is the conclusion used here. Every I(U_n)
  already has its R(U_n)-module structure and hence the R(W)-module structure
  by restriction along e_n. Semilinearity of `I.val.map` and naturality of `e`
  make all these displayed maps R(W)-linear. `Function.Exact` is equality of
  kernel and image on their carriers, exactly module exactness for these maps.
  No action is quantified arbitrarily. For the complex stipulated in the node
  (zero in negative degrees), augmented exactness is equivalent to the canonical
  augmentation being a quasi-isomorphism: H⁰ is I(W) via that restriction, positive
  homology is zero, and negative degrees are zero. No separate choice of complex
  or new spelling of quasi-isomorphism is needed to state this explicit equivalent
  conclusion, and no extra assertion is added.
- No weak contractibility, affineness, finite splitting, or constant-ring
  hypotheses appear.

### Dependencies read and used

Read every statement dependency node and its record, then the signatures/docstrings:

- `def-weil-size-convention`: metatheoretic record, no module/declaration;
  rendered by explicit universes and the small-site bound above.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` (its `factors` field).
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`; read the full abbreviation and
  Mathlib `SheafOfModules`, `PresheafOfModules.obj`, `map`, and semilinearity.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the explicit exact-sequence
  form avoids choosing a derived localization. Its module remains imported.
- `def-weil-pbc-sites-and-cohomology`: the recorded `Precoverage` site classes,
  `Precoverage.toGrothendieck`, and `Sheaf`; the recorded main module
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` is imported. The statement
  does not concern H' or site morphisms, so it does not use those other clauses.
- `def-weil-pbc-simplicial-object`: `CategoryTheory.SimplicialObject` and `δ`,
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`.

The recorded modules of all stated proof dependencies are imported, with proof-only
imports non-public: module sheafification, free Yoneda, underlying-set sheafification,
exact sheafification, sheaf epimorphisms, limits, and
`Sheaf.Paper.SiteSheafificationSectionsLocal`. For Mathlib leaves without a `lean`
record, their `mathlib_match` gives the import. The theorem's docstring carries
all eight proof steps, including finite support, compatible local cones, the cone
identity, fixed-Z underlying-abelian sheafification, injective Hom, and R(W)-linearity.

### Edge cases

Checked n=0 (empty matching tuple, augmentation epi), n=1 (two vertices over W),
exactness at degree zero, and every positive degree. Negative degrees are the
stipulated zero terms, not an omitted acyclicity hypothesis. The zero sheaf and
zero coefficient ring cause no exclusion. The empty category has no W so the
universal theorem has no instance there, exactly as in the node. Empty covering
families/sieves are allowed when the site admits them. No nonempty, finite,
contractible, affine, or positive-characteristic restriction is introduced.

### Searches

Commands used `msearch.py NN lem-weil-pbc-ringed-hypercover-injective-augmentation`:

- LeanFinder: "Injective sheaves of modules have exact augmented alternating section
  complexes on simplicial hypercovers"; eight hits (generic injective resolutions,
  Mayer-Vietoris, constant alternating complexes, K-injectivity), no exact match.
- Loogle: `"Injective", "Hypercover"`; zero hits.
- Mathlib grep: `hypercover.*(acyclic|exact|cohomology)|injective.*hypercover|hypercover.*injective`;
  only `Sites/CoproductSheafCondition` and `Sites/Hypercover/Saturate`, neither the
  all-degree variable-ring injective augmentation theorem.
- LeanSearch: "The augmented alternating sections sequence of an injective sheaf
  of modules on a ringed-site hypercover is exact"; unavailable, Internal Server Error.
- `rg` in upstream `WeilConjectures` and this project's `lean/Sheaf`: searched
  hypercover, matching objects, ringed hypercovers and injective hypercover declarations.
  The existing `SplitEtaleHypercover.injective_module_section_cohomology` in
  `Sheaf.Paper.HypercoverFreeResolution` requires split etale hypercovers and constant
  coefficients; it is not this node. General matching diagrams are written inline,
  as in the existing etale-hypercover statements. No new predicate is defined.
- `rg` for the exact proposed full declaration name in Mathlib, upstream and project:
  no pre-existing declaration; upstream search for this blueprint id also had no hit.

No statement correction, dependency replacement, or disputed statement was needed.

### Validation

All compiles use `scompile.py` on the server, nice 19, two threads, 60 seconds per file.
The final module compiles cleanly with its single expected `sorry` proof. No local
compiler or Lake build was run. `deliver2.py --no-push` is the final validation;
the second reader supplies the independent second-reading section and delivers.

## Second reading by NN

Independent second reader, 2026-10-15. I opened the item JSON, the full Lean
module, all six statement-dependency nodes, and their actual declarations. I read
Stacks hypercovering.tex, lemma-acyclic-hypercover-sheaves (01GE) and
lemma-injective-trivial-cech (01GW), including their proofs. The former is the
sheaf-matching formulation on an arbitrary site; the latter supplies the
free-sheaf/injective-Hom argument. Its fibre-product assumption serves its
representable-family presentation; the present node instead takes matching limits
in sheaves and does not require those limits to be represented in C. The ringed
analogue is justified by the node's eight-step variable-coefficient proof, not by
assuming that an injective R-module sheaf is injective as an abelian sheaf.

Object/hypothesis/conclusion inventory, with Lean rendering and verdict:

1. Small site, in the size convention: `{C : Type u} [SmallCategory C]`,
   `(J : Precoverage C)` and the four instances `HasIsos`,
   `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`.
   Pass. I read these classes in Mathlib/Sites/Precoverage. They are the exact
   recorded site interface of def-weil-pbc-sites-and-cohomology, including
   pullbacks of covering arrows rather than all finite limits in C. The skeleton
   size convention permits one bound for objects and arrows. The ring and module
   bounds `max u r` and `max u v r` contain that bound and permit arbitrary larger
   coefficients; there is no independent undersized matching-test universe.
2. Subcanonical site: `[J.toGrothendieck.Subcanonical]`. Pass: precisely every
   represented Hom presheaf is a sheaf, so representable matching sections are
   literal morphisms of C. No topology is replaced by the trivial topology.
3. Commutative ring sheaf: `(R : Sheaf J.toGrothendieck CommRingCat.{max u r})`.
   Pass. `sheafCompose ... (forget₂ CommRingCat RingCat)` changes only the
   coefficient category, retaining the same sections and restrictions.
4. Injective sheaf of R-modules: `I : ringedSiteModules ...` and `[Injective I]`.
   Pass. I read RingedSiteModules: it is transparently `SheafOfModules R`, not a
   constant-module sheaf category. Mathlib's `SheafOfModules.val` is a
   `PresheafOfModules` with an abelian sheaf condition. Its `obj` and `map` have
   precisely the variable-ring module and restricted-scalar types required here.
   `Injective.factors` extends every map along every mono, exactly the node's
   injectivity, with no extra acyclicity assumption.
5. Object W, simplicial U, compatible augmentation: `(W : C)`
   `(U : SimplicialObject C)` and
   `(e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)`. Pass.
   I read `SimplicialObject := SimplexCategoryᵒᵖ ⥤ C` and its face definition.
   Naturality of e includes all face and degeneracy operators.
6. All hypercover matching epimorphisms: `hcover`, for every n, T, w and p.
   Pass. Its first implication puts each lower simplex over w; its second is
   compatibility under every lower simplex operator. Its covering sieve S and
   local t prescribe the augmentation and every matching component. I read
   `Sheaf.createsLimitsOfShape` and `Sheaf.isLocallySurjective_iff_epi`: matching
   sections are computed sectionwise and epi means local lifts. For n=0 the
   tuple has no entries, leaving exactly local lifting of w. For n=1 its entries
   are the two vertices over w. For higher n any noninjective lower operator
   factors as a surjection followed by its injective image; the corresponding
   section is forced by the degeneracy map from the proper-face section.
   Thus quantifying over all lower operators is equivalent to the finite
   proper-face matching diagram, not a stronger lift assumption. Compatibility
   is oriented correctly: `p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)`.
   No matching object or fibre product is required to exist inside C.
7. Cochain terms, negative zeros, alternating differential: the lambda domains
   `I.val.obj (op (U _⦋n⦌))` are I(U_n), and the sums over `Fin (n+2)` are
   exactly all n+2 face restrictions with coefficients `(-1 : ℤ)^j.val`.
   Pass. `U.δ j` goes from degree n+1 to n and `I.val.map` reverses it.
   The explicit augmented sequence needs only nonnegative terms; the stipulated
   zero negative terms add no further exactness condition.
8. Canonical augmentation: `I.val.map (e.app (op (SimplexCategory.mk 0))).op`.
   Pass. This is restriction from I(W), rather than an arbitrary map or an
   existential identification.
9. Exactness at I(W): the first conjunct `Function.Injective` of that restriction.
   Pass: exactly the initial zero of the augmented sequence.
10. Exactness at I(U_0): `Function.Exact` of that restriction and the degree-zero
    alternating sum. Pass: equality of image and kernel, with the canonical map.
11. Exactness at every positive term: `∀ n : ℕ, Function.Exact δⁿ δⁿ⁺¹`.
    Pass: this tests I(U_(n+1)), covering every positive degree with no truncation.
12. R(W)-modules and quasi-isomorphism: pass via the node's explicitly equivalent
    exact augmented sequence. I read `PresheafOfModules.map_smul` and its
    restricted-scalar map type. Pullback of scalars along e_n gives the specified
    R(W)-action, and naturality of e makes the displayed sums R(W)-linear.
    `Function.Exact` is equality of the same kernel and image carriers for those
    linear maps, hence exactly module exactness. The first two conjuncts identify
    H⁰ canonically with I(W); the remaining conjuncts kill all positive cohomology.
    With zero negative terms this is the specified quasi-isomorphism, using the
    recorded derived-category notion, whose declarations I also opened. No
    affineness, weak contractibility, splitting, or fixed-ring hypothesis occurs.

Edge cases: n=0 and n=1 were checked in the matching condition and conclusion
separately; the outer exactness quantifier starts at zero and covers degree one
onwards. Empty matching tuples and empty covering sieves/families are permitted.
An empty site has no W, exactly as the node. A site with an empty object causes
no extra exclusion. The zero module sheaf and the zero coefficient ring are
allowed. No characteristic condition, finite index restriction or nonempty
instance is present. All variables and universes are explicitly bound.

Independent searches, with different wording from the first reader:

- LeanFinder via msearch.py: "An injective sheaf on a ringed site satisfies
  descent along an augmented simplicial hyperresolution". Eight hits, concerning
  local injectivity and one-step hypercover sheaf conditions; no all-degree
  injective ringed-module augmentation theorem.
- Loogle via msearch.py: `"Function.Exact", "Injective"`. Two hits:
  `Function.Exact.comp_injective` and `Function.Exact.splitInjectiveEquiv`;
  neither states hypercover descent.
- LeanSearch via msearch.py: "An injective module sheaf has an exact augmented
  alternating section sequence on a hypercover". Service unavailable (Internal
  Server Error); no mathematical verdict inferred from the failed search.
- Independent rg in Mathlib's Sites, upstream WeilConjectures and project
  lean/Sheaf for hypercover/hyperresolution with injective, acyclic or exact,
  and augmentation with exact. The actual close candidate is
  Sheaf.Paper.HypercoverFreeResolution. I opened both
  `injective_abelian_section_cohomology` and
  `injective_module_section_cohomology`: these require SplitEtaleHypercover on
  a compact quasi-separated scheme, and the module theorem has constant R.
  They do not give the present arbitrary-site, variable-ring statement.
  Mathlib's remaining hypercover hits concern 0/1-hypercovers, not this theorem.
  Therefore dropping this module in favor of those declarations would lose the
  node's objects and generality.

No mismatch found; no Lean or node correction made. No new nodes or dependency
modules are part of this delivery. The existing general ringed-site module is
used directly; there is no private copy, new predicate, hollow definition or
proved auxiliary theorem. The sole theorem has `sorry`. Its docstring follows
all eight proof steps, including finite original labels, local matching cones,
the cone identity, fixed-Z sheafification of underlying abelian presheaves,
canonical free-Yoneda evaluation, injective extension and scalar compatibility.
The module and declaration docstrings contain the source and blueprint id.
The node's lean.statement was checked verbatim against the declaration signature.

Validation: scompile.py from the sandbox compiled the delivered module cleanly
on the server (4.3 s), nice 19, two threads, 60 seconds per file. Its published
RingedSiteModules dependency was resolved and compiled by the same tool (1.0 s).
No local compiler or global build was used.

## Worker report

Stage 2, item `lem-sf-ext-sheaf-constructible`, group NS. The delivery writes
`Sheaf.Paper.EtaleSitePerfectConstructibleHom`, containing two theorem statements,
both with `sorry` proofs. No definitions, helper axioms, new nodes, or dependency
modules are introduced. The node is changed only in `lean`. In particular this is
not a second stage-1 split: NC's reviewed natural-language statement and proof are
retained verbatim. The previous worker's duplicate-splitting refusal concerned a
stage-1 operation; this delivery uses `deliver2.py --no-push` as required.

The main declaration is
`AlgebraicGeometry.Etale.constructible_cohomology_derivedHom_of_etale_sitePerfect`.
The second is
`AlgebraicGeometry.Etale.extSheaf_vanish_and_hom_constructible_of_etale_finiteLocallyFree`.

Hypothesis and clause correspondence for the first declaration:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type (u + 1)) [Field E]`,
  `[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The field and its
  quotient live in the coefficient universe required by the recorded etale API.
  The scheme universe remains `u`, so the site object and arrow universes have
  not been equated. The universe is explicit, not auto-bound.
- Integer n at least one: `(n : ℕ) (hn : 1 ≤ n)`; this parametrizes exactly the
  positive integers. `Padic.coefficientExtensionRing l E n` is the recorded
  quotient by the power of the recorded chosen uniformizer, rather than an
  arbitrary finite ring. Its `CommRing` structure is inherited from the quotient.
  `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness directly to
  each constructibility predicate; no additional finite-ring hypothesis is added.
- Scheme X: `(X : Scheme.{u})`; no finite-type, separatedness, quasi-compactness,
  dimension, characteristic, or invertibility hypothesis is imposed.
- Objects of D(X_et,A): `K M : DerivedCategoryModule (coefficientExtensionRing ...) X`.
  The abbreviation is the recorded derived category of
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- An etale covering: the existential `_hK` begins with
  `U : Scheme.Cover.{u} Scheme.etalePrecoverage X`. This packages joint
  surjectivity and etaleness; the cover is not required to have a finite index.
- For every cover member: `∀ α : U.I₀, ∃ P : CochainComplex ... ℤ`.
  Its category is the sheaf category on `(U.X α).smallEtaleTopology`.
- Local identification of K: `Nonempty (DerivedCategory.Q.obj P ≅
  (upperStar ... (U.f α)).mapDerivedCategory.obj K)`.
  The exact constant-coefficient inverse image induces the derived restriction;
  there is no arbitrary replacement restriction functor or assumed equivalence.
- Bounded cochain model: `∃ a b : ℤ, a ≤ b ∧ ∀ p : ℤ,
  (p < a ∨ b < p) → IsZero (P.X p)`.
  This is boundedness of the terms, not merely of the model's cohomology.
  These bounds occur after `∀ α`, so they may depend on the cover member.
- Every term a direct summand of a finite sum of A: `∀ p : ℤ, ∃ r : ℕ, ∃ ι, ∃ π,
  ι ≫ π = 𝟙 (P.X p)`. The middle object of the splitting is the constant sheaf
  with value `ModuleCat.of A (Fin r → A)`. The finite coordinate module is A^r,
  the finite sum of copies of A, not a general locally free or projective object.
  Its constant sheaf is A_U^r. Both arrows are sheaf-of-A-module morphisms.
  The quantifiers allow the rank to depend on both α and p, as required.
- Bounded constructibility of M: `_hM` is the exact recorded
  `DerivedCategory.isBoundedConstructible A X M`, with its finiteness argument
  explicitly supplied from the coefficient dependency. Its definition requires
  constructible cohomology and a bounded cohomology interval. No Tor-amplitude
  condition is used.
- Every integer i: the conclusion begins `∀ i : ℤ`.
- The ith cohomology sheaf of RHom: `DerivedCategory.homologyFunctor ... i`, applied
  to `((derivedHom ... X).obj (op K)).obj M`.
- Constructibility: `Scheme.IsConstructibleEtaleModuleSheaf` is the recorded
  global finite-stratification predicate, not the upstream geometric-stalk
  predicate and not a merely local constructibility predicate.
- There is no claim that RHom is globally bounded: the conclusion concerns each
  individual cohomology sheaf, including when local perfect bounds vary.

Hypothesis and clause correspondence for the second declaration:

- The same l, E, n, hn and X binders give precisely the same coefficient and
  scheme hypotheses as in the first declaration.
- Module sheaves F,G: `F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- Finite local freeness of F: `_hF` gives an etale cover U and, for each α, a
  natural-number rank r and a sheaf isomorphism between the pullback of F and
  the constant sheaf with value `Fin r → A`. The ranks may vary with α.
- Constructibility of G: `_hG : Scheme.IsConstructibleEtaleModuleSheaf G`, using
  exactly the same finite coefficient instance as the main assertion.
- F,G as degree-zero complexes: `DerivedCategory.singleFunctor _ 0` applied to
  F and G respectively, in the two arguments of the existing `derivedHom`.
- Ext^j is H^j of that internal derived Hom: the displayed `homologyFunctor ... j`
  object is precisely this sheaf, not a global Ext group.
- Vanishing for every nonzero integer j: `∀ j : ℤ, j ≠ 0 → IsZero (...)`.
  This includes both positive and negative degrees. Categorical zero is stated
  with `IsZero` on a sheaf object, not `Subsingleton` on a global section type.
- Constructibility of ordinary sheaf Hom: the second conjunct is
  `Scheme.IsConstructibleEtaleModuleSheaf ((ihom F).obj G)`. This is the existing
  internal Hom in the module-sheaf category, not a constant sheaf on the global
  Hom set. Its tensor-Hom adjunction characterizes the same sectionwise Hom
  notion of `def-pur-sheaf-hom`.

Dependency declarations used (source signatures and docstrings were opened):

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `coefficientExtensionIdeal` from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-derived-categories`:
  `Sheaf.AlgebraicGeometry.DerivedCategories`, with
  `AlgebraicGeometry.Etale.DerivedCategoryModule` imported from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-pur-derived-internal-hom`:
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses` (imported general ringed-site
  encoding). In the recorded etale ModuleCat-sheaf encoding the existing
  `AlgebraicGeometry.Etale.derivedHom` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom` is used, as in the landed
  `Sheaf.Paper.FiniteConstructibleHom`. This is the right adjoint to derived
  tensor; its upstream construction derives ordinary internal Hom using
  K-injective resolutions. Stacks 08J7 characterizes the node's construction
  by this same adjunction. No second derived-Hom construction is defined.
- `def-weil-derived-cohomology-sheaves`: the Mathlib match is
  `DerivedCategory.homologyFunctor`, from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `def-weil-pbc-etale-constructible-sheaf`:
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `def-pur-sheaf-hom`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj` (imported general ringed-site encoding). For the
  existing etale ModuleCat-sheaf category ordinary internal Hom is its existing
  `ihom`, characterized by the same tensor-Hom adjunction and sectionwise
  restriction description. No private copy of sheaf Hom is introduced.
- Local restriction uses `AlgebraicGeometry.Etale.upperStar` and
  `CategoryTheory.Functor.mapDerivedCategory` through
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`. Finite etale covers
  are not assumed: the cover construction is Mathlib's `Scheme.Cover`.

The module includes the recorded modules of all already-stated proof dependencies
as non-public proof imports (including the finite-value bridge, finite locally
constant Serre and biproduct closure, refinement, exact inverse image, and
ringed internal-Hom restriction). The two docstrings retain the node's complete
fixed-stratification proof: finite-column Hom-complex filtration, exact
finite-summand Hom, inverse image on strata, lisse kernel/cokernel/extension
closure, covering descent, and the one-term free case. Nothing is proved here.

Edge cases checked before writing:

- Empty X and empty covering index: the existential cover and universal local
  model clauses allow the empty cover of the empty scheme. No Nonempty binder
  or chosen cover member is needed.
- Zero K, M, F or G, and rank zero: r ranges over ℕ, so A^0 and its splittings
  are allowed; termwise zero models fit any nonempty finite degree interval.
- Nonuniform local bounds and ranks on infinitely many components: a,b are
  quantified after α, and r after α,p. No finite subcover, uniform support
  interval for K, or bounded conclusion for RHom is added.
- One-term and two-term models: arbitrary differentials in P are retained;
  no replacement of site-perfectness by dualizability or by globally projective
  terms is made.
- Arbitrary cohomology degrees: i,j range over ℤ; Ext vanishing is for j≠0,
  not just positive j, and degree zero is not incorrectly asserted zero.
- n=1 is included; n=0 is excluded by the source's positive-level hypothesis.
  No assumption that l is invertible on X or that X has a chosen base field
  is present in the node or in either Lean statement.
- M may have infinite Tor dimension. For example over a point with A=Z/4,
  G=Z/2 and F=A, the degree-zero Hom is G and other sheaf Ext degrees vanish.
  The statements require no false finite-Tor assumption on G.

Searches for an existing statement:

- `msearch.py NS lem-sf-ext-sheaf-constructible leanfinder` with query
  "Internal derived Hom from an etale locally bounded finite projective complex
  into a bounded constructible complex has constructible cohomology": eight
  results, headed by `CochainComplex.IsKProjective` and global Ext/projective
  results. None is the etale constructibility assertion.
- `msearch.py ... loogle "IsConstructibleSheaf, derivedHom"`: no results;
  the Mathlib service does not know the project identifier IsConstructibleSheaf.
- `msearch.py ... grep "constructible.*(Hom|Ext)|(Hom|Ext).*constructible"`:
  ten results about constructible subsets and Chevalley complexity, no match.
- `rg` of the upstream source for the exact blueprint id: no match. Concept
  searches found `Etale.boundedConstructible_derivedHom` and related theorems
  in `SixFunctors/Etale/Derived/Stability/DirectImage.lean`. The signatures
  require both inputs to have finite Tor amplitude and impose geometric
  finite-type/dimension hypotheses, so they do not state this item.
- `rg` of `lean/Sheaf` found `Sheaf.Paper.FiniteConstructibleHom`; its etale
  theorem also requires both Tor intervals and separated finite-type geometric
  hypotheses. Its pro-etale theorem is on the other site. Neither is a match.
- Searches for `sitePerfect`, `SitePerfect`, `site.perfect` and finite-projective
  Hom also found the ordinary O_X strictly-perfect-Hom theorem. It is a model
  computation on an affine open, not a constructible constant-coefficient
  etale-sheaf assertion. No existing whole-item declaration was found.

Source check: the blueprint node's markdown file is absent in this checkout;
the complete node, NC's reviewed split, and `dag/units/sk-thm-sf-hom-ctf.json`
were read. The official Stacks pages https://stacks.math.columbia.edu/tag/08J7,
https://stacks.math.columbia.edu/tag/03EM and
https://stacks.math.columbia.edu/tag/03RX were opened to check the internal-Hom
meaning, K-injective computation and finite locally constant closure.
No statement correction or mathematical dispute is proposed.


## Second reading by NS

I independently read the base node, sandbox node and entire Lean file, all eight
statement-dependency records and their declaration sources, the ten proof steps,
and the unit sk-thm-sf-hom-ctf. No mathematical mismatch was found. I changed only
this report; the module, natural statement, proof, dependency lists and lean record
are retained. There is no statement_change, new node or dependency module to audit.

Object/hypothesis/conclusion checklist (the node's order):

1. Prime ell: `(l : ℕ) [Fact l.Prime]` in both declarations. Exact.
2. Finite extension E/Q_ell: `(E : Type (u + 1)) [Field E]` with
   `[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact; no extra
   topology, valuation or field-structure hypothesis is imposed. The recorded
   coefficient construction supplies the spectral absolute value and integer ring.
3. Chosen integer ring, uniformizer and quotient A: both statements use precisely
   `Padic.coefficientExtensionRing l E n`. I read its reducible definition as
   `coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n`, with the
   latter the nth power of the ideal generated by the recorded uniformizer.
   The chosen integer ring is characterized by the absolute-value inequality in
   `extension_integers_dvr`, so this is the recorded object, not an arbitrary ring.
   Exact. The positive-level finiteness theorem supplies every required Finite
   argument, rather than adding a hypothesis.
4. Positive level: `(n : ℕ) (hn : 1 ≤ n)`. Exactly all integers n >= 1.
5. Arbitrary scheme X: `(X : Scheme.{u})`. Exact; no base field, Noetherian,
   separated, finite-type, dimension or invertibility condition is added.
6. K,M in D(X_et,A): `K M : DerivedCategoryModule ... X`. I read the abbreviation
   in Derived/Coefficients: `DerivedCategory (Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} A))`. This is the recorded coefficient category. Exact.
7. Etale covering: `_hK` existentially quantifies `Scheme.Cover.{u}
   Scheme.etalePrecoverage X`, then universally quantifies `α : U.I₀`.
   Scheme.Cover packages the covering/surjectivity and etale conditions; it does
   not require a finite indexing set. Exact.
8. Local bounded complex: after α, an existential `P : CochainComplex
   (Sheaf (U.X α).smallEtaleTopology (ModuleCat ...)) ℤ`, with `Nonempty
   (DerivedCategory.Q.obj P ≅ (upperStar ... (U.f α)).mapDerivedCategory.obj K)`.
   I checked the exact-functor derived-restriction API in Derived/UpperLowerStar;
   it is restriction of this K, not an unspecified comparison functor. Exact.
9. Bounded terms: `∃ a b : ℤ, a ≤ b ∧ ∀ p, (p < a ∨ b < p) → IsZero (P.X p)`.
   Bounds follow α, so they are local; this is term boundedness, not cohomological
   boundedness. Requiring a <= b excludes no bounded or zero complex. Exact.
10. Each term a finite summand: `∀ p : ℤ, ∃ r : ℕ, ∃ ι, ∃ π, ι ≫ π = 𝟙 (P.X p)`.
    The middle object is the existing constant module sheaf of `Fin r → A`.
    This finite product module is also A^r, the finite direct sum in the node.
    The arrows are module-sheaf morphisms, and the equation makes P.X p a retract.
    The rank depends on α,p. No global projectivity or uniform rank is assumed.
    Exact; the separately recorded site-perfect node is for the pro-etale and
    completed coefficient settings, so substituting its predicate would be wrong.
11. Bounded constructible M: `_hM : @DerivedCategory.isBoundedConstructible ... X M`.
    I read the definition: all cohomology sheaves satisfy the recorded finite
    stratification predicate, and vanish off some finite interval. It does not
    assert finite Tor amplitude or use the other upstream stalk predicate. Exact.
12. Every integer degree: conclusion `∀ i : ℤ`. Exact.
13. Internal derived Hom and its cohomology: `homologyFunctor ... i` applied to
    `((derivedHom ... X).obj (op K)).obj M`. The contravariant and covariant
    arguments are in the right order. I read Derived/Hom, Monoidal/Closed and the
    recorded DerivedInternalHomOfUniverses. The existing etale object is the
    K-injective-derived internal Hom, characterized by the derived tensor-Hom
    adjunction; Stacks 08J7 characterizes the same object uniquely. The generic
    SheafOfModules and fixed-coefficient ModuleCat encodings are different Lean
    categories of the same module-sheaf notion, not two invented constructions.
    Exact; this is neither global Hom nor a global Ext group.
14. Constructible cohomology sheaves: `Scheme.IsConstructibleEtaleModuleSheaf`
    on that object. I read its finite locally closed immersed stratification,
    constructible subsets, and finite constant module values after restriction.
    Exact. The conclusion deliberately imposes no global bound on RHom.
15. Particular case F,G: both are in the same module-sheaf category. `_hF` gives
    an etale cover and `∃ r : ℕ, Nonempty (upperStar ... F ≅ constantSheaf (A^r))`
    for each member. This is precisely the node's finite local freeness, with
    locally varying rank. `_hG` is the same constructibility predicate. Exact.
16. Regard F,G in degree zero: both arguments of derivedHom are values of the
    existing `DerivedCategory.singleFunctor _ 0`. Exact.
17. All nonzero-degree sheaf Ext vanish: the first conjunct is `∀ j : ℤ,
    j ≠ 0 → IsZero ((homologyFunctor ... j).obj (derivedHom(F[0],G[0])))`.
    Exact, including negative degrees; degree zero is not declared zero.
18. Ordinary sheaf Hom is constructible: the second conjunct applies the same
    predicate to `((ihom F).obj G)`. I read the recorded SheafOfModules.homObj
    and Mathlib's sheaf monoidal/enriched-Hom construction, including the relation
    to presheafHom over slices. For ModuleCat coefficients this existing ihom is
    precisely the module sheaf of local linear maps. It is not the constant sheaf
    of global morphisms. Exact. No extra degree-zero identification is asserted
    as a third conclusion (the node only uses it in the proof).

Source and proof check:

The blueprint markdown and local stacks-project checkout are absent. In addition
to reading the complete DAG statement and proof, I fetched the official Stacks
repository's `sites-cohomology.tex`, `sites-modules.tex`, and `etale-cohomology.tex`
into this item's scratchpad and read the relevant source passages. The checked
places are sites-cohomology, section-internal-hom and lemma-restriction-RHom-to-U
([08J7](https://stacks.math.columbia.edu/tag/08J7),
[08JB](https://stacks.math.columbia.edu/tag/08JB)); sites-modules,
section-internal-hom and lemma-internal-hom
([03EM](https://stacks.math.columbia.edu/tag/03EM)); and etale-cohomology,
lemma-kernel-finite-locally-constant
([03RX](https://stacks.math.columbia.edu/tag/03RX)). There is no ambient geometric
finiteness condition in these passages. The Noetherian coefficient hypothesis of
03RX(3) follows from finiteness of A; it is not a new scheme assumption.

The first docstring retains proof steps 1-9: one common finite stratification,
local K-injective Hom model, finite retract exactness, exact inverse image on
strata with no claim of preserved K-injectivity, lisse cohomology, finite sums
and idempotent kernels, the finite column filtration, its long exact sequence,
and cover composition on each fixed stratum. The second retains step 10, the
one-term free calculation and descent. I checked the displayed filtration
against the node's differential formula. All already-recorded proof dependency
modules are imported. No missing definition or helper is required merely to
state either theorem. There are no new data definitions or axioms; both theorem
proofs are exactly `by sorry`, as required at stage 2. Source and blueprint
references are present on the module and both declarations.

Edge cases:

- Empty scheme and its empty cover are allowed: neither U.I₀ nor X has a
  Nonempty assumption, and no cover member is chosen in the statement.
- Zero objects, zero complex terms and rank r=0 are included. A zero complex
  satisfies any one-point bounding interval; summand ranks are naturals.
- Infinitely many cover members, unbounded variation of local support intervals,
  and unbounded variation of local ranks are included. Neither RHom boundedness
  nor a finite subcover is concluded.
- All integer degrees, negative Ext and degree zero have the node's quantifiers.
- n=1 is included; n=0 is outside the node. No residue-characteristic case of X
  is excluded, including characteristic ell.
- u is explicitly bound. E and the coefficient sheaves occupy the recorded
  etale API's u+1 universe while Scheme occupies u. No site object/morphism
  universe equality, hidden independent small index universe, or auto-implicit
  variable is imposed. Small coefficient fields can be represented in this
  universe by lifting; no mathematical extension is omitted.
- M and G may have infinite Tor dimension: there is no Tor-amplitude binder.

Independent duplicate searches, using different wording from the first worker:

- LeanFinder: "Sheaf internal Ext from locally free finite rank sheaves vanishes
  outside degree zero and Hom preserves constructibility": eight hits, including
  CategoryTheory.Sheaf.H, isZero_Ext_succ_of_projective, injective/projective
  dimension and singleFunctor projectivity lemmas. These concern different
  assertions and do not give constructibility of internal sheaf Hom here.
- Loogle: `"LocallyConstant", "hom"`: twelve hits, including
  Scheme.Hom.isLocallyConstant_finrank, CompHausLike and Condensed locally constant
  constructions. No matching sheaf constructibility statement.
- LeanSearch: "Internal sheaf Ext of a finite locally free sheaf is zero in
  nonzero degrees": service returned Internal Server Error, recorded unavailable.
- msearch grep: `locally.free.*[Hh]om|[Ee]xt.*locally.free`: zero hits.
- Direct rg over upstream WeilConjectures, repository lean/Sheaf and Mathlib's
  algebra/category and homology directories, for constructible Hom/Ext and
  sitePerfect/SitePerfect, plus the exact item id in dag/lean_names_upstream.json.
  The exact id has no declaration. I opened the apparent matches:
  Etale.boundedConstructible_derivedHom requires both finite-Tor inputs and
  finite-type geometry/invertible exponent, and its constructibility predicate
  differs; Sheaf.Paper.FiniteConstructibleHom has geometric/Tor hypotheses and
  its other assertion is pro-etale; FiniteFreeHomComparison is a comparison
  across sites, not constructibility or vanishing. None states this node.

Validation: the prescribed scompile.py compiled the delivered file cleanly in
both its sandbox and library paths (10.7 s and 27.7 s, respectively); no warnings
were reported. A direct text check confirmed that lean.statement is verbatim
the main theorem signature, every Lean line has at most 100 characters, and
there are exactly two sorry bodies. Both declarations have explicit binders and
`set_option autoImplicit false`. No repair of correct Lean was made.

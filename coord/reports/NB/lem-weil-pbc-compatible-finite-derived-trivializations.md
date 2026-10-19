## Worker report

Item: `lem-weil-pbc-compatible-finite-derived-trivializations`, group NB.
The main module is `Sheaf.Paper.CompatibleFiniteDerivedTrivializations`; its sole
statement is `AlgebraicGeometry.Scheme.compatible_finite_derived_trivializations`.
This is stage 2: every theorem has `by sorry`. Definitions contain their actual
constructions. All universes and variables are explicitly bound; `autoImplicit` is false.
No original statement, proof, proof dependency, or other metadata is changed. The
item gains the two new definition dependencies described below and its Lean record.

### Hypotheses and conclusions, clause by clause

* Scheme: `(X : Scheme.{u})`, with its existing `X.smallEtaleTopology`.
* Positive levels: `n : ℕ` in Lean denotes the paper's level `n+1`. This is a
  reindexing bijection, so there is no extra level or missing identity case.
* Finite commutative rings: `B : ℕ → Type (u+1)`, the instances
  `[∀ n, CommRing (B n)]` and `[∀ n, Finite (B n)]`.
* Specified quotient maps: `q : ∀ n, B (n+1) →+* B n`; `hq` says each is
  `Function.Surjective`. No additional algebra structure or split quotient is assumed.
* Objects: `E n : DerivedCategory (ModuleCat (B n))` and
  `K n : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat (B n)))`.
  These are the existing derived categories with the upstream Grothendieck-abelian
  localization instance, not independently chosen replacements.
* Boundedness: `hE` and `hK` give integers `a,b` with `.IsGE a ∧ .IsLE b` for
  each level separately. There is no common amplitude assumption and no connective
  or perfect-complex assumption.
* Finite module cohomology: `hEf n i` is `Module.Finite (B n)` on the existing
  derived `homologyFunctor` at integer degree `i`.
* Finite locally constant cohomology of K: `hKf n i` is the upstream
  `IsFiniteLocallyConstantSheaf` on that cohomology sheaf. In this module-coefficient
  API it means local constancy and finite generation of geometric stalk modules;
  since B n is a finite ring, these stalks are finite sets as well. This is the
  fixed-coefficient encoding authorized in `def-weil-pbc-etale-sheaves`.
* Specified eta and rho, including quotient compatibility: `dE n` and `dK n`
  are their adjunct arrows into exact derived restriction of scalars;
  `hη n` and `hρ n` are `Nonempty (StructuredArrow.IsUniversal
  (StructuredArrow.mk ...))`. These retain the actual normalization maps; they
  do not merely assert existence of some identification. See the equivalence
  calculation below. Iteration gives the quotient cocycles, rather than adding
  independent incoherent comparison choices for composite quotients.
* The isomorphism sheaf is the actual
  `derivedLocalIsomorphismSheaf ((normalizationConstant ...).obj (E n)) (K n)`.
  Its presheaf values are actual isomorphisms in D(V_et,B n) for etale V/X;
  restriction uses the exact pullback and its canonical composition isomorphism.
  `presheafToSheaf` then sheafifies it. This is not a replacement arbitrary torsor.
* Finite local constancy of I: `hI n` is the existing
  `IsLisseEtaleSheafOfSets` (finite locally constant underlying sets).
* Nonempty stalks: `hInonempty` quantifies over every separably closed field Ω
  in the scheme universe and every `s : Spec Ω ⟶ X`, and asserts `Nonempty` of
  `(pointSmallEtale s).sheafFiber.obj I`. These are the actual geometric stalks.
* Cover: the existential `𝒰 : Cover.{u} proetalePrecoverage X` is precisely a
  pro-etale covering family, not just a collection of weakly etale morphisms.
* Actual trivializations: `e j n` is an isomorphism between the images of the
  constant E n and K n under `localProEtaleComparison (𝒰.f j) (B n)`.
  That functor is the existing derived comparison inverse image ν_X^*, followed
  by existing derived pro-etale pullback to U_j. Thus the displayed constants,
  as well as K, are pulled from X_et exactly as the node's last sentence specifies.
* The final equation is, in Lean's composition order,
  `e_next.hom ≫ localProEtaleNormalization ... (dK n) =
  localProEtaleNormalization ... (normalizationConstantArrow ... (dE n)) ≫
  (normalizationRestrict ...).map (e j n).hom`.
  Both sides use the same canonical coefficient-interchange map. Its adjoint
  is exactly `rho ∘ (e_next ⊗ᴸ B_n) ∘ eta⁻¹ = e_n`, not equality after an
  arbitrary forgetful map. No surjectivity of reductions on I is assumed.

### Why the universal-arrow presentation is equivalent

For q:R→S write L=-⊗ᴸ_R S and U for exact restriction. By L ⊣ U,
Iso(LM,N) corresponds to arrows d:M→UN for which (N,d) is initial in
(M↓U): if alpha:LM≅N, d=unit_M followed by U(alpha.hom), and the unique
factorization to (T,t) is the adjoint of t composed with alpha.inv. Conversely,
initiality identifies (N,d) with (LM,unit_M), uniquely over M. The property
is exactly Mathlib `StructuredArrow.IsUniversal`; its structure is unique, so
`Nonempty` here loses no normalization data. There is no Nonempty choice of
an object from an existence-only theorem.

The same adjunction applies to fixed-coefficient sheaves. Constants and inverse
image commute with restriction via the explicitly constructed comparisons.
Consequently `e_R ≫ d_K = d_E ≫ U(e_S)` is adjoint to
`L(e_R) ≫ rho = eta ≫ e_S`. Since eta is invertible, this is exactly the
node's reduction equation. This reasoning does not require U to be faithful.
For successive quotients, composites of these universal arrows are universal:
initiality identifies their left adjoints with successive scalar extension.
Uniqueness of this identification gives the usual associativity/quotient
cocycles and their identity cases. There is no extra freely chosen cocycle
in a sequence specified only by adjacent normalizations.

### Dependency declarations read and used

* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, with `DerivedCategory.homologyFunctor` and `.IsGE/.IsLE`
  from `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, `Scheme.pointSmallEtale`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`. Its full interface
  constructs derived change of coefficients by K-flat resolutions independently
  of the three universes. The statement here uses the equivalent universal-arrow
  presentation of specified normalizations, and does not force those universes
  equal or select an unspecified functor from its existence statement.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and the published upstream
  `WeilConjectures.SixFunctors.ProEtale` framework: `Scheme.ProEt`,
  `ProEt.topology`, `proetalePrecoverage`, `ProEtale.upperStar`,
  `ProEtale.comparisonUpperStar`. The site remains object universe u+1,
  morphism universe u. The local continuity instance for pro-etale pullback is
  the existing `ProEt.isContinuous_overPullback`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`.
  The latter is the existing `ProEtale.comparisonAdjunction`, whose left adjoint
  is the canonical `comparisonUpperStar` used in the definitions here.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  `constantCommuteCompose`. `normalizationConstant` is an abbreviation for its
  existing exact localization, not a new constant-sheaf notion.
* `WeilConjectures.AlgebraicGeometry.EtaleSheaves`:
  `Scheme.IsLisseEtaleSheafOfSets`, whose definition is the existing finite
  locally constant sheaf-of-types predicate. The actual upstream declaration,
  not the obsolete finite-local-constant alias in the recorded declaration list,
  is used.
* `WeilConjectures.ConstructibleSheaf.Defs`:
  `IsLocallyConstantSheaf`, `IsFiniteLocallyConstantSheaf` and their local-constant
  data and stalk-finiteness definitions.
* `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryCompIso`,
  `mapDerivedCategoryNatIso`; all derived transports use these localizations.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`:
  `Etale.upperStar`, `Etale.upperStarComp` for actual etale restrictions.
* `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`:
  `StructuredArrow.mk`, `StructuredArrow.IsUniversal`; this is initiality as
  in the initial-object part of `def-galois-initial-mono`, whose Mathlib
  `Limits.IsInitial` declaration and full docstring were read.
* `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction` has the exact
  Mathlib match `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  in `Mathlib.CategoryTheory.Sites.Pullback`, with `Functor.IsContinuous`
  from `Sites.Continuous`. Their full signatures and docstrings were read.
  This exact interface is cited by the new normalization node.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `TwoSquare.mk`.
  The coefficient comparison uses the identity square for sectionwise direct
  image and the canonical `sheafPullbackConstruction.sheafAdjunctionContinuous`.
  Its inverse is `asIso` of that particular mate, not a chosen natural isomorphism.

The statement imports the stated modules of its proof plan privately: finite
locally constant representability, ind-etale algebra and stability, weakly
contractible covers, and canonical tensor pullback; also the Mathlib modules
for Yoneda, finite-etale comma categories, algebra colimits, Spec/Γ, finite and
weakly etale morphisms, finite inverse systems, and site points. The
`lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation` node has no
recorded declaration, and so has no import; it is a proof dependency only,
not needed to type this stage-2 statement. Its intended use is fully recorded
in the main theorem's natural-language proof. No dependency interface repair
was necessary.

### Edge cases checked before finalizing

* Empty X permits the empty covering and makes the e-family vacuous.
* The zero ring is allowed; so are zero complexes and identically zero cohomology.
* Identity quotient maps and isomorphism quotients have their usual identity
  universal arrows. Universal-arrow encoding does not discard these cases.
* One-term and shifted complexes are included; integer bounds can differ at
  every level. No unjustified flatness or finite Tor dimension is assumed.
* Disconnected and non-quasicompact X are allowed. Finite stalk images stabilize
  pointwise; the proof does not assume a uniform stabilization index on X.
* Reduction maps on isomorphism sheaves can fail to be surjective. Only the
  coefficient quotient maps q are assumed surjective; stable finite stalk
  images supply the inverse-limit construction.
* The new isomorphism presheaf is defined for all derived objects, although its
  finite-local-constant/nonempty properties are hypotheses of the main theorem.
* Sites have object universe u+1 and morphism universe u. Coefficients and
  modules are in u+1, the existing constructible-sheaf convention. No equality
  between the site's object and morphism universes is imposed.

### Searches and validation

The sandbox `searches.jsonl` records the literal msearch queries and returned
names. Both new nodes carry these searches, including unsuccessful services.

* LeanFinder: "Compatible trivializations of inverse systems of finite derived
  local systems on a pro etale covering" returned profinite locally constant
  functions, condensed colimits and partial sections; no theorem matching this
  statement. Loogle `DerivedCategory, IsIso` reported unknown identifier IsIso.
* Mathlib grep `Isom.*[Ss]heaf|[Ss]heaf.*Isom|[Ii]somorphism.*[Pp]resheaf`
  in CategoryTheory returned 25 ambient comma, enriched and sheafification
  occurrences, no derived local isomorphism sheaf.
* LeanFinder on universal arrows into coefficient restriction returned ordinary
  ModuleCat extension/restriction adjunctions. Grep
  `IsScalarNormalization|UniversalArrow|[Uu]niversal.*[Aa]rrow` found
  `StructuredArrow.IsUniversal`, which is reused. No new universal-arrow
  predicate was added.
* LeanFinder on sheafification of local derived isomorphisms returned general
  sheafification and topology-W results, no exact construction.
* LeanSearch queries "sheaf of derived isomorphisms of complexes" and
  "universal arrow derived extension restriction of scalars normalization"
  both returned service unavailable: Internal Server Error. Other independent
  searches completed; this service failure does not obstruct the delivery.
* `rg` in the upstream source, Mathlib and `lean/Sheaf` found no declarations
  with the proposed names. The item ID had no upstream declaration. DAG grep
  and `tools/blueprint_refs.py search` for "derived isomorphism" and
  "normalization arrow" found no existing definition node for these notions.
  The recorded ancestors identify the proper-base-change amplification unit.
* Current server source and delivery refs were checked for a previously supplied
  derived isomorphism-sheaf module before supplying the missing construction;
  no usable such module was present. The pro-etale framework sources read are
  the current side-project files, not the older slopmaster2 framework.
* Every delivered module was compiled separately in dependency order through
  `scompile.py NB lem-weil-pbc-compatible-finite-derived-trivializations`.
  Clean compile and the prescribed `deliver2.py --no-push` dry run are the final
  validation; no global build, direct live-file mutation or direct git command
  was run. Expected sorry warnings are the only allowed warnings.

The first dry run found three grouped citations that the new-node validator
requires as separate bracketed references; these were repaired. Its remaining
second-reading requirement is intentionally left to the independent reader.

No STATEMENT-DISPUTED claim or source-statement correction is made. The
universal-arrow presentation is an equivalent encoding, with the exact
compatibility equation retained. The stage-3 evaluation bridge remains a
substantive proof obligation of the existing proof plan.

## New nodes

`def-weil-pbc-derived-normalization-arrows`, module
`Sheaf.Paper.DerivedNormalizationArrows`, supplies canonical derived constants,
exact ordinary and sheaf coefficient restriction, their canonical interchange,
and the constant normalization arrow. It also supplies the canonical coefficient
mate for inverse image and its inverse. The proof obligations named
`normalizationCoefficientExactness`, `normalizationModuleRestrictExactness` and
`normalizationPullbackMate_isIso` state precisely the exactness and invertibility
properties explicitly included in this node's statement; each has a full
natural-language proof docstring. Instances extract proof fields from these
named statements. All functor and natural-transformation data are real
constructions from existing APIs. Sources are Stacks Tags 06YY/07A6 and Section 06Y5 for
coefficient derivation and its adjunction, Tag 093J for exact constants, and
Tags 00WX/03DA for canonical inverse image and the module category. Search results above found the existing abstract
universal-arrow predicate, which is reused, but not these canonical derived
normalization-arrow constructions. This is a definition node serving the
amplification proof, not another target or a restated local-effectivity theorem.

`def-weil-pbc-derived-local-isomorphism-sheaf`, module
`Sheaf.Paper.DerivedLocalIsomorphismSheaf`, defines the actual local derived
isomorphism presheaf, its canonical restriction maps and sheafification. The
named `localIsomorphismMap_laws` states the restriction identity and composition
laws explicitly included in the new node's statement, with a complete proof
outline via canonical pullback coherence and localization. It additionally
defines the exact local pro-etale comparison functor and canonical coefficient
interchanges and pulled normalization arrows, required to state the main
compatibility equation. Source is the bounded-derived adaptation of Stacks
Tag 09BV already specified by the parent node, with Tags 03ED, 099R and 098K
for localization/comparison. Searches found ambient inverse-image and
sheafification APIs, which are reused, but no existing node or declaration of
this sheaf of actual derived isomorphisms. Neither an arbitrary sheaf nor an
arbitrary reduction map is introduced. Both new nodes are cited directly in
the item's augmented stmt_deps; each cites exactly the prerequisite IDs
appearing in its own self-contained statement.

## Second reading by NB

I read the item record in `dag/nodes/sec-proper-base-change/lem-weil-pbc-compatible-finite-derived-trivializations.json`, the two added definition records, the Stacks source at `proetale.tex` Tag 09BV (together with the cited bounded-derived adaptation), and all three delivered modules. The item statement decomposes as follows.

* The base object is an arbitrary scheme `X : Scheme.{u}`. The coefficient tower is
  `B : ℕ → Type (u+1)` with `[∀ n, CommRing (B n)]` and `[∀ n, Finite (B n)]`, and
  quotient maps `q n : B (n+1) →+* B n` with `hq n : Function.Surjective (q n)`.
* The two towers are `E n : DerivedCategory (ModuleCat (B n))` and
  `K n : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat (B n)))`.
  The arrows `dE n` and `dK n` in the theorem are the specified normalization arrows
  into exact restriction of scalars (`normalizationModuleRestrict` and
  `normalizationRestrict`); `hη` and `hρ` require their `StructuredArrow.IsUniversal`
  properties. This is the universal-arrow encoding of the specified derived
  scalar-extension isomorphisms, and uniqueness gives the quotient cocycles described
  by the node.
* `hE` and `hK` give independent integer lower and upper bounds at every level.
  `hEf` gives finite `B n`-module cohomology of every `E n`, while `hKf` gives finite
  locally constant module cohomology of every `K n`.
* `hI` says each actual sheaf
  `derivedLocalIsomorphismSheaf (normalizationConstant ... (E n)) (K n)` is finite
  locally constant (`IsLisseEtaleSheafOfSets` is the existing finite-locally-constant
  set-sheaf predicate). `hInonempty` says every separably closed geometric point
  `Spec Ω ⟶ X` has a nonempty fiber of that same sheaf.
* The conclusion is a pro-etale cover `𝒰 : Cover.{u} proetalePrecoverage X`, actual
  isomorphisms `e j n` between the pulled constant `E n` and pulled `K n`, and for
  every `j,n` the displayed equality between the pulled `dK` square and the pulled
  constant `dE` square. `localProEtaleComparison` is precisely comparison inverse image
  followed by pro-etale restriction, and `localProEtaleNormalization` uses the
  canonical coefficient interchange. Thus the equality is adjoint to
  `ρ n ∘ (e j (n+1) ⊗ᴸ B n) ∘ η n⁻¹ = e j n`; it does not assume surjectivity of the
  isomorphism-sheaf reductions.

The Lean signature renders every object, hypothesis, and quantifier in that list. It
uses the paper's levels `n ≥ 1` through the harmless reindexing `n : ℕ` with maps
`n+1 → n`; no level is omitted. It keeps the site's object universe `u+1` and morphism
universe `u`, and the geometric-point field universe `Type u`. No extra Noetherian,
quasi-compactness, connectedness, flatness, Tor-dimension, or common-amplitude
hypothesis appears. The conclusion quantifies the cover first and the entire compatible
family second, as in the node.

Edge cases checked: the empty scheme admits the empty cover; zero rings and zero
complexes are admitted by the stated typeclasses; identity/isomorphism quotient maps
are admitted and their universal arrows give the identity normalization cases; one-term
and shifted complexes are covered by the integer bounds; disconnected schemes and
non-quasi-compact schemes are not excluded; finite stalk images need only stabilize
pointwise, so no uniform index is introduced; and no surjectivity of the maps on
isomorphism sheaves is assumed.

For the one-definition check I searched the upstream `WeilConjectures` tree, the live
`lean/Sheaf` tree, Mathlib, and DAG records. LeanFinder searches for compatible finite
derived trivializations, universal derived restriction arrows, and sheaves of derived
isomorphisms found no matching declaration. Loogle searches found only ambient derived
category and restriction APIs. Grep searches found only the ambient
`StructuredArrow.IsUniversal`, sheafification, and inverse-image APIs. LeanSearch was
attempted for both the derived-isomorphism-sheaf and universal-normalization notions;
that service returned `Internal Server Error`. The existing `IsLisseEtaleSheafOfSets`
abbreviation was reused rather than copied. No existing declaration duplicates either
new helper notion.

The two helper definition records were read against their source places. Their data are
real constructions: `DerivedNormalizationArrows` localizes the exact constant and
restriction functors and the canonical mates, while `DerivedLocalIsomorphismSheaf`
builds the actual restriction presheaf of derived isomorphisms and applies the existing
presheaf-to-sheaf functor. Their postponed exactness/coherence facts are named theorems
with source and blueprint docstrings; no definition contains `sorry` data. The main
statement theorem remains `by sorry` as required for stage 2.

No statement mismatch was found, so no node or Lean declaration was changed during this
second reading. The only worker-report clarification is that the universal-arrow
encoding is justified by the adjunction and is not an arbitrary `Nonempty` choice: the
specified arrows `dE,dK` remain in the theorem and determine the normalization maps.
The two citers checked were `lem-weil-pbc-normalized-constructible-local-effectivity`
(step 3 uses exactly this finite normalized tower conclusion; holds) and
`lem-weil-pbc-residue-lisse-perfect-lift` (its proof dependency uses the same compatible
trivializations; holds). The derived-isomorphism-sheaf evaluation node also uses this
item as its blueprint/proof dependency and remains compatible (holds).

All three files compiled separately with the required `scompile.py` wrapper; only the
permitted `sorry` declarations remain.

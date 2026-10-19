## Worker report

The item is stated in `Sheaf.Paper.LocalHomTowerCriterion`, declaration
`CategoryTheory.localHom_zero_iff_multiplicationTower_zero`. Its proof is `sorry`.
The original statement is unchanged. One definition node supplies the coefficient
localization and the local multiplication and restriction constructions missing from
the stated dependency interfaces. No dependency record is replaced.

Read the item, all five statement dependencies, their full recorded declarations and
docstrings, the proof dependency records, Stacks algebraization.tex lines 825–873
(Tag 0997, lemma-hom-from-Af), and sites-modules.tex section-localize and
lemma-extension-by-zero-exact. Tag 0997 applies to the slice as a ringed site.

Hypothesis and clause matching:

- A small ringed site is `{C : Type u} [SmallCategory C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{u}`. The coefficient
  commutativity is the convention of the dependency `derivedInternalHom` and the
  Stacks source's ringed-site setting. No scheme or spatial assumption is imposed.
- An object and section are `(U : C)` and `(f : R.obj.obj (op U))`.
- The original derived object is `(K : DerivedCategory (ringedSiteModules ...))`.
  `ringedSiteModules` is the recorded general-site module category, transparently
  Mathlib's `SheafOfModules`. Derived-category choices for the base and slice use
  independent explicitly bound morphism universes `w` and `wSlice`.
- The slice topology and coefficient sheaf are `J.over U` and `R.over U`.
  `localCoefficientDerivedRestriction R U` is exactly the descent of
  `SheafOfModules.overFunctor`, so its value on `K` is `K|_U`.
- The localized coefficient module is `localCoefficientLocalization R U f`.
  It is placed in degree zero by `DerivedCategory.singleFunctor _ 0`.
  Its construction is a colimit of the unit modules with multiplication maps.
  On presheaves, stage `n` maps `a` to `a/f^n`. Equality at a later stage is
  precisely equality of fractions, including when powers of `f` kill elements.
  The module sheaf colimit is the sheafification of that presheaf colimit:
  this follows from the sheafification adjunction. Thus the construction is the
  source's coefficient localization, with no arbitrary existence choice.
- The constant inverse family in `IsDerivedLimit` is
  `fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K`; each transition
  is `(localSectionDerivedMultiplication R U f).app K`. The section's restrictions
  act by the existing `PresheafOfModules.sectionsSMul` and `overSections`.
  Localization of the resulting termwise natural transformation makes the actual
  multiplication map on the derived restriction. It is not a supplied endomorphism.
- `(T : DerivedCategory ...)` and `_hT : IsDerivedLimit ... T` specify any chosen
  derived limit, using the recorded Roos-triangle predicate. The `HasProduct`
  instance is the product needed to state that predicate, already part of being a
  derived limit in the node; it adds no exactness-of-products assumption.
  `ℕ` is the dependency's encoding of positive tower indices, by `n ↦ n+1`.
- `IsZero ((derivedInternalHom (J.over U) (R.over U)).obj (...)) ↔ IsZero T`
  expresses both zero-object clauses and their equivalence. The first object is
  internal RHom on the slice, not global derived Hom or a cohomology group.

Dependency interfaces used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and `singleFunctor`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`, `CategoryTheory.derivedInternalHom`.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`, `CategoryTheory.IsDerivedLimit`.
- `Mathlib.CategoryTheory.Functor.OfSequence`, `Functor.ofOpSequence` gives the
  inverse-system convention used by the family/transition interface; `ofSequence`
  builds the direct diagram in the new coefficient-localization definition.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`; `J.over` and `Sheaf.over` from Sites.Over.
- Existing multiplication: `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`,
  `PresheafOfModules.sectionsSMul` (lines 67–100), `overSections` (143–156).
- Colimits: `Mathlib.CategoryTheory.Limits.HasLimits`, `Limits.colimit`, and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`, the existing module-sheaf colimits.
  Descent: `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`; natural transformation
  descent: `Localization.liftNatTrans` and `NatTrans.mapHomologicalComplex`.

The stated proof dependencies are imported. The three proof nodes
`lem-weil-pbc-localization-free-resolution`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, and
`lem-pc-ringed-space-product-kinjective` have no Lean record, so no module can be
imported for them yet. They are not necessary to elaborate this stage-2 statement.
The theorem's docstring retains all five steps of the node's proof and its citations.

Edge cases checked mathematically: `f=0` and nilpotent `f` give zero localization
and zero homotopy limit; invertible `f` gives the coefficient unit and a tower
isomorphic to the identity tower, so the equivalence reduces to vanishing of the
restricted object. `K=0`, the zero ring, an arbitrary object of a small site, and
unbounded complexes are included. No nonempty-site assumption, injectivity of `f`,
boundedness assumption, or exact-countable-products assumption occurs. An empty
site has no object `U` and the universal statement has its appropriate empty case.

Searches actually run via msearch.py:

- LeanSearch: "derived internal Hom localization vanishes if and only if derived
  inverse limit multiplication tower vanishes" — HTTP Internal Server Error;
  recorded unavailable, not a no-match result.
- LeanFinder: "derived internal Hom localization equals homotopy limit of scalar
  multiplication tower" — eight hits on derived localization and linear structure,
  including `DerivedCategory.instLinear`; no localization/internal-Hom/tower criterion.
- Loogle: `CategoryTheory.IsDerivedLimit` — unknown identifier, zero hits.
- Mathlib grep: `localization.*tower|derived.*localization.*Hom` — ordinary scalar-tower
  and localization lemmas; no sheaf-derived criterion.
- New-notion LeanSearch: "localization of a sheaf of rings at a section as colimit
  of multiplication on slice modules" — Internal Server Error, unavailable.
- New-notion LeanFinder: "coefficient localization on a ringed site slice by a section
  colimit multiplication and derived restriction" — eight hits, including
  `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`. Read its full declaration
  in Mathlib/Topology/Sheaves/CommRingCat.lean lines 72–104: it requires a topological
  space and an Opens category, so cannot serve an arbitrary ringed site. Other hits
  concern affine tilde sheaves, not arbitrary sites.
- New-notion Mathlib grep: `localCoefficientLocalization|localSectionMultiplication|sectionsSMul`
  — no hits. Direct rg searches in the source project and lean/Sheaf found the
  presheaf scalar multiplication reused here, but no general-site coefficient
  localization. Grep of the upstream source for the item id returned no hits;
  the proposed declaration names are absent from dag/lean_names_upstream.json,
  upstream source and lean/Sheaf.
- DAG and full-blueprint searches for localization and multiplication tower found
  no definition node giving this notion. `lem-weil-pbc-localization-free-resolution`
  mentions the coefficient localization in a theorem statement but provides no
  definition declaration. The new node does not restate that theorem.

Server validation: both delivered modules compile separately in dependency order
with scompile.py, nice 19, two threads, within 60 seconds each, without errors or
warnings. No local Lean command or global build was run.

## New nodes

`def-weil-pbc-local-coefficient-localization` defines the slice coefficient localization,
the actual local section multiplication maps, and their induced derived restriction
and multiplication. Source: Tag 0997 and the exact slice restriction of Tags 03DI/03DJ.
The three new-notion searches above and the blueprint/DAG searches found no usable
existing definition. It reuses existing presheaf scalar multiplication, categorical
colimits, slice restriction, and localization of categories instead of copying them.
Its supporting named proof obligations are
`localCoefficientRestriction_exact` and `localSectionMultiplication_naturality`, each
with a complete natural-language proof and `sorry`. These are the proofs needed by
the data constructions; the definitions contain no sorry or arbitrary undetermined
data choice. `localCoefficientOver_hasDerivedCategory` merely exposes the definitional
equality between forgetting commutativity before and after restriction to typeclass
search; it supplies no extra mathematical assumption. No dependency modules or
statement correction are needed.

## Second reading by NO

Independently read the node, both modules and the new definition node against
algebraization.tex, Tag 0997 (lemma-hom-from-Af), lines 825–873. Also read
sites-modules.tex, section-localize, definition-localize-ringed-site and
lemma-extension-by-zero-exact. Tag 0997 has a global section; on the slice,
the restrictions of the specified local section form precisely such a section.
The source and the internal-Hom dependency use commutative ring coefficients.
No statement correction was necessary.

Object, hypothesis and conclusion checklist, with verdicts:

1. Small ringed site: `{C : Type u} [SmallCategory C]`,
   `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{u}`. Pass:
   arbitrary topology, no space/scheme, finiteness or Noetherian assumption.
2. U and its section: `(U : C)` and `(f : R.obj.obj (op U))`. Pass.
3. Arbitrary unbounded K: the binder uses `DerivedCategory
   (ringedSiteModules (localCoefficientRings R))`. Opened RingedSiteModules:
   it is transparently the general Mathlib SheafOfModules category. Pass.
4. Slice coefficients and restriction: `J.over U`, `R.over U`, and
   `(localCoefficientDerivedRestriction R U).obj K`. Opened Mathlib
   `SheafOfModules.overFunctor`, `over`, and the slice declarations:
   sections at V/U are sections at V, as in the source. The derived functor
   is the existing `mapDerivedCategory` of that exact restriction. Pass.
5. Localized coefficient module in degree zero:
   `(DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization R U f)`.
   The construction is a colimit of unit modules with f-multiplication.
   Before sheafification its stage-n representative a maps to a/f^n;
   the direct-sequence relation is the equality-of-fractions relation,
   including f-torsion. Sheafification preserves the colimit as a left
   adjoint. Thus it is the source's localized coefficient module. Pass.
6. Constant inverse family: `K := fun _ : ℕ ↦
   (localCoefficientDerivedRestriction R U).obj K`. Transitions are
   `fun _ ↦ (localSectionDerivedMultiplication R U f).app K`. Opened upstream
   `PresheafOfModules.overSections` and `sectionsSMul`: they multiply over
   a:V→U by R(a)(f). The delivered transformation descends this termwise
   action through quasi-isomorphism localization, so the endomorphism is
   the actual f-action, not a free parameter. Pass.
7. Any derived limit: `(T : DerivedCategory ...)` and `_hT : IsDerivedLimit
   ... T`. Read IsDerivedLimit and its triangle predicate, together with
   towerTransitionEndomorphism: the required distinguished triangle has
   middle map 1-s, with coordinate pr_n - pr_(n+1) followed by f. The
   HasProduct binder supplies the product required by that predicate;
   it does not assume products exact. Read `Functor.ofOpSequence`: the
   family/transition interface has precisely direction X(n+1)→X(n).
   ℕ reindexes positive tower indices by n↦n+1. Pass.
8. First clause: `IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
   (op (...localized coefficient in degree zero...), ...restricted K...))`.
   Opened derivedInternalHom: it is the localized internal sheaf Hom-complex
   into a K-injective replacement, not global Hom or one cohomology group.
   Both arguments and the slice category match. Pass.
9. Second clause and equivalence: `↔ IsZero T`. Pass: both vanishing
   clauses and both directions are present, universally for every T with
   the displayed derived-limit property, in the node's quantifier order.

Universe/edge-case review: u is arbitrary and SmallCategory makes the slice
small in u as well. The modules and rings are u-sized, matching the recorded
internal-Hom dependency's universe convention. Independent bound w and wSlice
specify the two derived localization models; HasDerivedCategory has a standard
model in a sufficiently large universe. They impose no geometric hypothesis.
K=0 and the zero ring are included. For f=0 or nilpotent f, localization and
the homotopy limit vanish; for invertible f both vanishing clauses reduce to
vanishing of K|U. There is no characteristic or boundedness restriction.
An empty site has no U, giving the appropriate vacuous universal assertion;
an empty scheme is not excluded. The tower's fixed index set is ℕ, never an
empty variable index set; its n=0 term corresponds to positive index 1.

Independent searches: msearch LeanFinder "homotopy inverse limit repeated
scalar action localization sheaf Hom" gave sheafification/localization
infrastructure, no criterion. LeanSearch "internal Hom inverted coefficient
sheaf repeated multiplication inverse limit" was unavailable (Internal Server
Error), not a no-match result. Loogle `CategoryTheory.Functor.mapDerivedCategory`
returned generic exact-functor descent, already reused here. LeanFinder
"localize coefficient module sheaf at one section on arbitrary site" returned
ModuleCat.Tilde declarations for affine schemes, not arbitrary sites.
Direct rg searches in Mathlib, upstream WeilConjectures and lean/Sheaf used
localization with homotopy/tower in both orders, localization presheaf,
section multiplication, derived restriction, and exact overFunctor. Opened
Mathlib `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`: it requires a
TopCat space and Opens category. It cannot supply the arbitrary-site notion.
The presheaf scalar action is reused. Opened moduleOverFunctor instances:
these concern ringed spaces. Also opened localized_restriction_adjunction
(exactness of the left adjoint) and localizedModule_adjunction_exact
(precoverage-generated topology). Neither defines the localization or derived
scalar action needed here. No matching statement or competing definition found.
DAG searches for coefficient/sheaf localization found theorem uses and
specializations, not another definition carrying the new notion.

New-node review: def-weil-pbc-local-coefficient-localization states precisely
the constructions in its module, with all objects introduced. Checked its
cited module category, slice, colimit and derived-category dependency nodes
and opened their recorded declarations. Its definition-kind/split status,
empty proof fields, null match, three search kinds, created record, chapter,
unit, audit states and Lean record satisfy the field rules. The ancestor
command confirms def-weil-pbc-completed-pullback and the via chain is the
item followed by its ancestor path. There are no dependency modules.
No data definition contains sorry or selects undetermined data from an
existence theorem. The two supporting named proof obligations have sources,
blueprint ids and full natural-language proofs. The definitional instance
only exposes equality of the two encodings of slice coefficient rings.

Conventions and docstrings pass: each declaration and module names its source
and blueprint node. The main theorem's docstring preserves all five node proof
steps, including products represented by K-injectives, reindexing, and derived
limit uniqueness. Every delivered theorem has proof sorry. Checked both
lean.statement fields verbatim against their source signatures; every line
is at most 100 characters and every universe/variable is explicitly bound.

No mathematical or Lean mismatch found; second reading changes this report
only. Both modules compile separately with scompile.py on the server, nice 19,
two threads, 60 seconds per file, without errors or warnings (2.4 and 1.9 s).
The initial invocation used the repository cwd and failed before compilation
because these new files exist only in the sandbox; rerunning from the sandbox
succeeded. No local compiler or global build was run.

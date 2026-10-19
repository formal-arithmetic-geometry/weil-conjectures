## Worker report

The module `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology` defines the canonical
natural transformation `AlgebraicGeometry.ProEtale.comparisonGlobalSections` and states
`AlgebraicGeometry.ProEtale.isIso_comparisonGlobalSections`, with `sorry` as its entire
proof. There are no other postponed proofs and no definitions with postponed data.

Hypothesis and clause correspondence:

- A scheme T: `(T : Scheme.{u})`, with no quasi-compactness, separation, characteristic,
  nonemptiness, or other geometric hypothesis.
- Finite discrete coefficient ring: `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`.
  Discreteness means coefficients in the ordinary category of left modules
  `ModuleCat.{u + 1} Λ`; this is not a condensed coefficient ring. `CommRing` is not assumed.
- All bounded-below etale complexes K: the source category of the natural transformation is
  `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  Quantification over this category in `IsIso` covers every lower bound, including negative
  bounds. The full-subcategory inclusion is `DerivedCategory.Plus.ι`.
- The specified exact inverse image ν*: the existing
  `(comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus`.
  This acts termwise, then localizes; it is not a new inverse-image functor.
- The derived unit: `(T.proEtaleSiteComparisonModules Λ).derivedPlus.unit`.
  This is `CategoryTheory.Adjunction.derivedPlus` for the dependency's actual canonical
  comparison adjunction, without extra structures on the coefficient category.
- The map induced by the unit: `comparisonGlobalSections` first uses `Functor.whiskerRight`
  to apply the ordinary derived etale sections functor to that unit. The displayed
  associators and `R.rightDerivedFunctorPlusCompatibility.hom` transport the bounded-below
  direct image through the full-subcategory inclusion to the unbounded derived direct image.
  It then uses `comparisonLowerStarCompRightDerivedGlobalSectionsIso.hom`, whiskered by
  that inclusion and inverse image. Thus its components are exactly RΓ_et(η_K) followed by
  the specified final-object comparison. No arbitrary morphism or chosen isomorphism occurs.
- Ordinary derived global sections on the left:
  `DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T`.
  The source definition is the total right derived functor of `Sheaf.Γ` on the etale site.
- Ordinary derived global sections on the right:
  `rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T`, after the exact inverse image and
  `DerivedCategory.Plus.ι`. The pro-etale source definition is the total right derived
  functor of `Sheaf.Γ (Scheme.ProEt.topology T)`.
- Natural isomorphism: `IsIso (comparisonGlobalSections T Λ)` states invertibility of the
  entire named natural transformation, hence invertibility for each K and naturality in
  every morphism of K. It does not merely assert some objectwise isomorphism.

Recorded statement dependencies used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, which
  records Mathlib's `DerivedCategory`, `DerivedCategory.Plus`, and `DerivedCategory.Plus.ι`
  in the module-valued sheaf encoding. The generic `Plus` construction works for left
  modules over arbitrary rings; this module's additional commutative-coefficient torsion
  predicate is not used.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`. Read its signature and docstring:
  it is ordinary RΓ at the terminal object, with no compactification requirement.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`. Read the full module and the
  underlying `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` declarations:
  `comparisonUpperStar`, `comparisonLowerStar`, and `comparisonAdjunction`.
- `lem-weil-pbc-derived-sections-pushforward`: the exact existing side-framework declaration
  `AlgebraicGeometry.ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso` in
  `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`. Its full
  signature and docstring, and the preceding underived terminal-object identification,
  were read both locally and using `scompile.py --source` to confirm the published source.
  The prerequisite is recorded in this delivery, rather than waiting for another worker.

Proof imports: the finite-level proposition is imported privately from
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`. The comparison adjunction is
already a public statement dependency. The Leray prerequisite is imported publicly because
its canonical comparison appears in the definition of the asserted map.
`thm-weil-pbc-site-comparison` has no recorded declaration on the base, so there is no
recorded proof module to import. Its conclusion is needed only for the postponed proof,
not to construct the unit. The upstream derived-unit theorem in
`WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` requires monoidal hypotheses;
we do not silently restrict Λ to commutative rings to use it. The generic bounded-below
adjunction used in this statement requires no such structure.

Edge cases checked before drafting: the empty scheme, the zero ring (whose modules are zero), the zero complex, sheaves in degree zero, a negative lower
bound, and arbitrary noncommutative finite rings. None is excluded. The site object's
universe and its morphism universe are left as supplied by the existing small sites;
the coefficient size u+1 is their common published convention. No new equality of site
universes is imposed. This is a statement about all bounded-below objects, with no
constructibility, finiteness of stalks, or torsion-freeness condition.

Searches performed:

- `msearch.py leanfinder`, query: "The derived unit induces a natural isomorphism between
  etale and proetale derived global sections of a bounded below complex". Eight hits,
  concerning generic derived-functor comparisons and unrelated algebraic etaleness; none
  states the item.
- `msearch.py loogle`, query: "CategoryTheory.Functor.rightDerivedFunctorCompIso".
  No hits; that project-specific identifier is unknown to the Mathlib service.
- `msearch.py grep`, query: "comparison.*[Gg]lobal|[Gg]lobal.*[Cc]omparison".
  No Mathlib hits.
- `rg` in the upstream `WeilConjectures` sources and the project's `lean/Sheaf` and side
  `lean/WeilConjectures` sources: found the exact prerequisite Leray comparison in
  `Comparison/CohomologicalDimension.lean`, but no theorem of invertibility of the
  composite induced by the unit for all bounded-below complexes.
- Searches by the item id in the upstream project found no matching declaration.
  Searches for `comparisonGlobalSections` and `isIso_comparisonGlobalSections` in Mathlib,
  upstream, and the side library found no name collision before writing the module.
- Read the generic `RightDerivedFunctor/PlusAdjunction`, `PlusCompatibility`, `PlusComp`,
  and `Comp` modules to check the signatures and the canonical normalization of the
  comparison maps. `ProEtale.isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj`
  only transfers vanishing in an individual degree for sheaves; it is not this statement.

Validation: `scompile.py ND lem-weil-pbc-comparison-global-cohomology` compiled the delivered
module in 2.3 seconds with no errors or warnings. All declarations bind their variables
and universes explicitly. The only `sorry` is the named theorem's entire proof. The prescribed `deliver2.py --no-push` dry run checks the existing-declaration probe,
server preflight, and each delivered file. Its only permitted outstanding requirement is
the independent second-reading section, which the second reader supplies.

## Dependency modules

`lem-weil-pbc-derived-sections-pushforward` had neither a Lean record nor a Mathlib match.
The existing published declaration
`AlgebraicGeometry.ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso` gives
exactly its canonical comparison: derive the natural terminal-object sections
identification, using preservation of K-injectives by the comparison direct image.
Its coefficient parameter may be `ModuleCat.{u + 1} Λ` for arbitrary `Ring Λ`; restriction
of its source to bounded-below J is the node's statement. The existing form is available
on all derived objects and does not require any extra mathematical assumption when
specialized to the node. Only the dependency's `lean` field is set, with `existing: true`
and an explanatory `note`. No dependency source module is copied or rewritten.

## Statement corrected

The original statement read:

> For a scheme $T$, finite $\Lambda$ and $K\in\Dplus(T_{\Et},\Lambda)$, the derived unit
> induces a natural isomorphism
>
> $$
> R\Gamma(T_{\Et},K)\xrightarrow{\sim}
> R\Gamma(T_{\Proet},\nu_T^*K).
> $$
>
> Both functors are ordinary derived sections.

The bare phrase "finite Λ" did not introduce its ring structure or left-module convention.
The recorded etale coefficient definition is written for commutative rings, while the
comparison-adjunction node and the finite-level theorem in this unit allow arbitrary
finite rings and left modules. The correction explicitly introduces Λ as a finite discrete
ring and specifies the composite intended by "the derived unit induces", adding the
already-existing Leray prerequisite to `stmt_deps`. This clarifies the source's coefficient
context and canonical arrow; it adds no commutativity, constructibility, or geometric
restriction. The source is the same blueprint item's statement and final proof sentence,
read with the finite-ring comparison context in this unit. No unit statement is changed.

Complete citer audit (all nodes whose `stmt_deps` or `proof_deps` contain the item, found
by searching all DAG JSON files and checking those fields):

- `lem-weil-pbc-comparison-direct-image-canonical-mate`: holds. Its finite commutative rings
  specialize the stated finite rings; the named derived-unit sections comparison is the
  one used in its canonical mate calculation.
- `prop-weil-pbc-comparison-direct-image`: holds. Both uses of derived sections in its proof
  still use the same bounded-below unit-induced comparison and its natural restriction
  maps, with identical hypotheses.

The prerequisite's `blueprint.from.node` names this item, but neither its statement nor
proof dependencies contains it, so it is not a citer in this audit and adding it creates
no cycle. No citer was edited. The `statement_change` record preserves the old statement
verbatim and lists these two citers, both with `holds: true`; only `statement`, `stmt_deps`,
and `statement_change` change in addition to `lean` on the item. Proof and proof dependencies
are preserved.

## Second reading by ND

I reread the corrected node statement, its source paragraph, every statement dependency,
and the two citers. The object and hypothesis list is:

- `T` is an arbitrary scheme, rendered by `(T : Scheme.{u})`; no quasi-compactness,
  separation, characteristic, nonemptiness, or field hypothesis is added.
- `Λ` is a finite discrete ring with left module coefficients, rendered by
  `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]` and `ModuleCat.{u + 1} Λ`. The module
  convention agrees with `def-weil-pbc-site-comparison-morphism` and the finite-level
  comparison; no commutativity or condensed coefficient structure is assumed.
- `K` ranges over all bounded-below etale complexes, rendered by the source category of
  `DerivedCategory.Plus.ι`; this includes every lower bound and does not impose
  constructibility, stalk finiteness, or torsion conditions.
- The inverse image is the existing canonical
  `(comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus`, and the unit is
  `(T.proEtaleSiteComparisonModules Λ).derivedPlus.unit`; neither is replaced by a private
  map or an arbitrary adjunction.
- The conclusion is the named natural transformation
  `comparisonGlobalSections`, whose source is etale ordinary derived sections after
  `DerivedCategory.Plus.ι` and whose target is pro-etale ordinary derived sections after
  the specified inverse image and inclusion. Its definition is the derived-unit map,
  transported by the associators and the recorded Leray comparison
  `comparisonLowerStarCompRightDerivedGlobalSectionsIso`. The theorem asserts
  `IsIso (comparisonGlobalSections T Λ)`, so it gives the natural isomorphism for every
  `K` and every morphism of `K`, in the same quantifier order as the node.

The source blueprint says exactly the derived-unit comparison and the final-object
sections identity. The corrected wording makes the coefficient convention and the
canonical final-object comparison explicit; it does not add a geometric hypothesis or
weaken the conclusion. The two audited citers remain valid: the canonical-mate lemma
specializes to its finite commutative coefficient case, and the direct-image proposition
uses the same bounded-below comparison. No citer requires editing.

Edge cases checked were the empty scheme, zero ring and zero module category, zero and
degree-zero complexes, negative lower bounds, empty coefficient/sheaf sections, and
noncommutative finite rings. The binders exclude none of these cases, and the site and
coefficient universes remain the published `u` and `u + 1` convention.

I repeated the three required searches with the worker's concept queries: LeanFinder found
only generic derived-functor or unrelated etale results; Loogle found no project-specific
global-comparison statement; and grep over Mathlib, the upstream `WeilConjectures` tree,
and this project's `lean` tree found no declaration of either comparison theorem. The
only matching ingredient is the published
`AlgebraicGeometry.ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso`, which
was read at its source and used directly.

The first reading's only delivery mismatch was mechanical: the newly added statement
dependency `lem-weil-pbc-derived-sections-pushforward` had no `lean` record on the base.
I supplied its existing declaration record, pointing to the published Leray isomorphism
and documenting its specialization to finite left `Λ`-modules; no duplicate module was
written. The item module itself compiled with `scompile.py` without errors or warnings,
has explicit universes and binders, and leaves only the named theorem proof as `sorry`.

## Worker report

Repair of return L, immutable head 40e52a6f4e32 (H3/H5). The former record
allowed arbitrary restriction functors, derived operations, projection arrows,
and source/target identifications. The replacement module is
`lean/Sheaf/Paper/RingedProjectionRestriction.lean`, with main theorem
`AlgebraicGeometry.Scheme.ringedProjectionRestriction`.

### Canonicality repair for H3/H5

The repaired interfaces now pin the previously free derived choices. `Operation.left`
is the exact functor `pullback.mapDerivedCategory`, `Operation.right` is the existing
`pushforward.rightDerivedFunctor`, and `Restriction.model` constructs the exact descent
of the existing `overFunctor`. The only models used in the conclusion are these
constructed models. `Operation.derivedAdjunction` is the actual
`moduleAdjunction.mapDerivedCategoryRightDerivedAdjunction`; its counit is also
identified on K-injective representatives. `TensorModel.descent` states full faithfulness
of restriction of natural transformations to all resolving pairs, and
`TensorModel.representative` gives the natural total-tensor comparison there.
This determines the tensor presentation up to its unique compatible isomorphism.
The projection equation uses only `derivedProjectionFormulaMate`, whose definition is
the existing adjoint-of-counit mate. Its tensor comparison is fixed on flat K-flat
representatives; source and target isomorphisms are actual composites of the
normalized restriction comparisons.

The repository's original statement, proof and dependency lists are restored.
In particular, the canonical shift clause is present. The earlier delivery's
statement_change removing that clause, its tautological shift field, and its
second-reading text have been removed. There is no statement correction in this
repair. This is the worker's report; independent second reading remains to be done.

Hypotheses and clauses, in the order of the node:

1. A morphism of arbitrary schemes is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   Coefficients are `R_Y`, `R_X : Sheaf (ProEt.topology _) CommRingCat.{u+1}`,
   with the specified `c : (proEtaleSheafInverseImage f _).obj R_Y ≅ R_X`.
   There is no finiteness, separatedness, boundedness, characteristic, or
   nonemptiness assumption. The site object universe remains u+1 and its
   morphism universe remains u; they have not been equated.
2. `Mod` abbreviates the recorded sheaf-of-modules category, forgetting the
   commutative ring sheaf to RingCat; `Der` is Mathlib's ordinary unbounded
   `DerivedCategory` with its standard localization size. The ordinary module
   operations in `Operation` are actual `SheafOfModules.pullback` and
   `SheafOfModules.pushforward`. `Global.coefficient_eq` fixes their ring map
   to the adjunct of c. `recordedDirectImage` identifies direct image with
   `proEtaleRingModuleDirectImage`. The coefficient map determines module pullback;
   no auxiliary isomorphism selects the derived operations, adjunction or projection map.
   `Operation.left` is actual `pullback.mapDerivedCategory`, and `right` is
   actual `pushforward.rightDerivedFunctor`, with its existing derived unit
   exposed by `rightComparison`. Exactness and K-injective existence are proof
   fields supplied by the existential conclusion, not added hypotheses.
3. `tensor` is the existing sheaf tensor; `total` is its existing signed direct-sum
   total complex from `map₂HomologicalComplex`. `resolving` uses exactly the
   recorded `CochainComplex.IsKFlat` and termwise `IsFlatOnSite` predicates.
   `TensorModel.representative` identifies the tensor functor naturally on the
   full subcategory of all pairs of flat K-flat complexes, including all its
   cochain maps. Thus it presents the localization of total tensor, rather
   than an arbitrary functor. This representative interface retains the small
   site's different object and morphism universes; the older tensor interface
   with a single site universe cannot be imposed as an additional hypothesis.
4. `Local g V` is indexed by every `V : Y.ProEt`. The localized X-object is
   literally `(proEtaleBaseChange f).obj V = X ×_Y V` in the recorded site
   construction. The site morphism is literally `Over.post (proEtaleBaseChange f)`.
   Coefficients are `R_Y.over V` and `R_X.over U`.
   `coefficient_sections` fixes the localized ring map to the restriction of
   the global one on each `T : Over V`. No unrelated localized scheme, site,
   or ring map is supplied as data.
5. `Restriction.model` constructs derived restriction using the actual
   `SheafOfModules.overFunctor ... V |>.mapDerivedCategory`; its factors and
   shift are Mathlib's fixed ones. The record supplies only exactness proofs
   and the tensor comparison, whose `pure_sections` equation fixes its value
   on every pure section to the sectionwise identity.
6. The first canonical natural isomorphism is `Local.directImage`:
   `g.operation.right ⋙ restrictionY.model.functor ≅
    restrictionX.model.functor ⋙ operation.right`.
   `ordinaryDirectImage_sections` fixes the ordinary comparison to identity on
   every section M(X ×_Y T). `restrictsKInjective` states preservation of the
   actual K-injective predicate. `directImage_representative` identifies the
   derived comparison, on every K-injective complex and naturally, with this
   ordinary comparison and the actual right-derived units. It cannot be
   replaced by an arbitrary automorphism of the same functors.
7. The second is `Local.pullback`, oriented
   `g.operation.left ⋙ restrictionX.model.functor ≅
    restrictionY.model.functor ⋙ operation.left`.
   `mate_counit` is the explicit exchange-mate equation. Derived adjunctions
   are normalized in `Operation.DerivedAdjunction.counit` to the actual
   ordinary module counit on every K-injective representative. Hence the
   exchange equation fixes the pullback comparison canonically.
8. The third is `restrictionTensorY.comparison`, and its X-analogue is also supplied.
   `OrdinaryTensor.pure_unit` determines the ordinary pullback/tensor
   comparison on generators by the actual module adjunction unit. `pure`
   constructs these generators using the existing presheaf tensor and
   sheafification unit. `totalComponent` uses the existing
   `tensorPullbackTotalComponent`; `totalMap` assembles exactly those degree
   maps into a chain map. `TensorComparison.representative` forces each
   derived tensor comparison to be its image on every pair of flat K-flat
   representatives. Naturality and the explicitly stated chain equation
   include both differentials and their signs.
9. `Local.ProjectionCompatible` is the restriction equation for the actual
   `derivedProjectionFormulaMate`, the existing adjoint-of-counit construction
   from ProjectionFormulaArrows, both globally and locally. There are no
   projection-map fields. `sourceIso` and `targetIso` are constructed from
   the tensor, direct-image and pullback comparisons in the required order;
   neither is an arbitrary field.
10. Canonical shifts are substantive equations. `TensorShifts.first/second`
    compare on resolving representatives with Mathlib's
    `CochainComplex.mapBifunctorShift₁Iso` and `mapBifunctorShift₂Iso`; the
    latter carries the Koszul sign. `TensorComparisonShifts.first/second`
    state the two commuting tensor-comparison squares for every integer.
    Exact functor shifts are the actual Mathlib shifts on the two constructed
    exact functors;
    `rightShift` is the actual right-derived shift. `directImage_shift`,
    `pullback_shift`, and `DerivedAdjunction.counit_shift` require the
    corresponding natural transformations to commute with those shifts.
    Applying the existing counit-mate formula therefore uses these same
    canonical structures, including the signed second tensor variable.
11. The final theorem clause quantifies every `a : A ⟶ B` in `Der R_Y`.
    For every V it assumes a `Sieve V` belonging to `ProEt.topology Y V`;
    for each `h : W ⟶ V` in that sieve it tests
    `IsIso ((data W).restrictionY.model.functor.map a)`, and concludes
    `IsIso a`. The restriction is over the covering object W. Covers may
    vary with V; no uniform cohomological bound is introduced.

All helper definitions have real data and source/blueprint docstrings. The only
`sorry` is the main theorem, whose docstring gives all seven proof steps. The
record types express normalized presentations of this node's canonical
constructions; they introduce no independent mathematical notion needing a new
DAG node. No dependency module or new node is delivered.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology` (reexported through the
  operations imports).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`, reexporting
  `ProEtaleOperations` and `ProEtaleOperationsCanonicalAdjunction`:
  `proEtaleRingDirectImageMap`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModulePullback`, `proEtaleRingModuleAdjunction` and the ordinary
  derived constructions. Their complete signatures and docstrings were read.
- `Sheaf.Algebra.Homology.KFlat` and
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.IsKFlat`, flat K-flat resolving complexes. The live source
  of the latter was read using `scompile.py --source`.
- Mathlib `Algebra.Homology.BifunctorShift`: the recorded
  `CochainComplex.mapBifunctor` total-tensor construction and its two shifts.
- Mathlib `Algebra.Homology.DerivedCategory.Basic` and `ExactFunctor`:
  `DerivedCategory`, `Q`, `Functor.mapDerivedCategory`, its factors and shifts.
- The localized ringed-site dependency's Mathlib matches:
  `SheafOfModules.over`, `SheafOfModules.overFunctor` and `Sheaf.over`.
- `Sheaf.Paper.ProjectionFormulaArrows`:
  `derivedProjectionFormulaMate`, `derivedPushforwardComplexComparison`, and
  the reexported `tensorPullbackTotalComponent` from
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`.

The recorded proof-dependency modules are imported non-publicly as required
by stages/2-statements.md section 3.7, including LocalizeRingedSiteMorphism,
LocalizedModuleAdjunctionExact, SitePullbackAbelianExact,
RingedSiteKInjectiveResolutions, KInjectiveRestrictLocalized,
KInjectiveTotalDerived, RingedExchangeTensorCoherence and ProjectionMateExact.
No unstated proof theorem is used to construct any definition.

Edge cases checked before formulating the replacement: empty schemes and empty
site objects remain valid; an empty sieve is allowed exactly when covering by
the topology; zero modules and complexes are allowed; all complexes are
unbounded; n=0, positive and negative integer shifts are included; coefficients
may be zero rings; the coefficient identification c is arbitrary, not assumed
identity; f may be identity or arbitrary, with no quasi-compactness assumption.
The sign normalization uses the actual Mathlib second-variable shift, rather
than a sign-free equation. Naturality of the representative comparisons is
essential: an objectwise family would not fix derived maps and is not used.

Searches made (also in searches.jsonl):

- `msearch.py ... leansearch` query “restriction to a slice ringed site commutes
  with derived tensor and the projection formula map”: service unavailable,
  Internal Server Error. Earlier LeanFinder queries on slice restriction,
  K-injectives and projection formulas found underived restriction/adjunction
  or abstract naturality lemmas, no theorem giving this statement.
- `msearch.py ... loogle "SheafOfModules.overFunctor"`: three underived
  overFunctor/overFunctorMap/overFunctorEquiv hits, no derived projection
  compatibility statement.
- `msearch.py ... grep "overFunctor|rightAdjointProjectionMap"
  Algebra/Category/ModuleCat/Sheaf`: five underived hits. These existing
  constructions are reused; no exact full-statement match was found.
- `rg` over upstream WeilConjectures (including SixFunctors/ProEtale), project
  lean/Sheaf and Mathlib for ringedProjectionRestriction, projection/restriction
  combinations, and this node id: no existing exact declaration. Related
  canonical tensor, exchange, projection, localization and module adjunction
  sources were opened, rather than inferred from names.

Source checks: Stacks [04J0](https://stacks.math.columbia.edu/tag/04J0),
[08FI](https://stacks.math.columbia.edu/tag/08FI),
[0FN5](https://stacks.math.columbia.edu/tag/0FN5),
[07A4](https://stacks.math.columbia.edu/tag/07A4),
[0B56](https://stacks.math.columbia.edu/tag/0B56),
[0E48](https://stacks.math.columbia.edu/tag/0E48), and the locality sentence
in [0944](https://stacks.math.columbia.edu/tag/0944).

Validation is being rerun for this repair. The previous second-reader text and
its obsolete compiler diagnosis are retained only in scratchpad; the next
independent reader will write the delivery's second-reading section.

The repair supplies explicit local additive proof instances while constructing
sourceIso, targetIso and ProjectionCompatible. These concern the actual
restriction functors and are not hypotheses of the main theorem. Constructor
size/injectivity generation is disabled only to reduce elaboration cost.

The representative universal properties are deliberate: a different presentation
of derived tensor is identified by the unique natural comparison compatible with
all signed total complexes, rather than a free bifunctor or free projection map.
The global coefficient adjunct and its sectionwise localization fix both ringed
morphisms. Thus all compatibility clauses concern these canonical constructions.

Current dependency-record audit: def-weil-pbc-proetale-operations now names
ProEtaleFiniteCoefficientDirectImage, whose record explicitly says it publicly
retains the arbitrary identified-coefficient operations. This item uses that
retained ProEtaleOperations/ProEtaleOperationsCanonicalAdjunction interface,
not the finite-coefficient specialization. def-pc-kflat-complex lists the retained
IsKFlat as well as the new independent-coefficient predicate; the existing IsKFlat
and the recorded IsFlatOnSite give the resolving-pair predicate in this module.
The statement retains the small site's object/morphism universes u+1/u.
No dependency node repair or new definition node is needed.

Validation of the final full-import module: the prescribed deliver2.py --no-push
has completed its scompile.run_many check without errors or non-sorry warnings
and has advanced to delivery bookkeeping/preflight. This includes the local
sandbox and library checks, or server confirmation as the wrapper requires.
The dry-run transcript is scratchpad/repair-final-dry-run.log. No delivery is
pushed by this worker. The earlier trimmed-import probe was discarded; the
explicit FlatOnSite import and all original proof-plan imports are retained.

## Second reading by NC

I did not write this statement. I read the repository node, the complete 708-line
module, the sandbox node record, the eight statement dependencies and the
declarations described below. The list below is my independent decomposition of
the node, followed by the corresponding Lean and verdict.

1. **Schemes, morphism and sites.** The objects are arbitrary schemes X and Y,
   a morphism f, and their small pro-etale sites. The theorem binds
   `{X Y : Scheme.{u}} (f : X ⟶ Y)` and uses `ProEt.topology` on `X.ProEt`
   and `Y.ProEt`. I opened `ProEtaleDerivedCategory` and `ProEtaleInverseImage`:
   `proEtaleBaseChange` is the recorded weakly-etale base-change functor, with
   no hypothesis on f. Its chosen fibre product has the variable factor first,
   canonically the same U as X times_Y V. Verdict: exact, including arbitrary f.
2. **Coefficients and their specified identification.** `R_Y` and `R_X` are
   commutative ring sheaves at universe u+1, and `c` is exactly the recorded
   inverse-image identification. `Global.coefficient_eq` fixes the module ring
   map to the adjunct `proEtaleRingDirectImageMap f R_Y R_X c`, after forgetting
   commutativity. It does not assert c is the identity. Verdict: exact.
3. **Ordinary unbounded derived operations.** `Mod` expands to
   `SheafOfModules.{u+1}` of the forgotten commutative ring sheaf, and `Der`
   expands to `DerivedCategory` with `HasDerivedCategory.standard`. I read
   `ProEtaleOperations` and `ProEtaleOperationsCanonicalAdjunction`, including
   the actual sectionwise direct image, tensor-extension pullback, and
   tensor-unit-normalized adjunction. `Operation.pushforward` is Mathlib's
   existing pushforward for the fixed ring map, and `recordedDirectImage`
   identifies it with the dependency's direct image. The existing
   `SheafOfModules.pullbackPushforwardAdjunction` gives its canonical module
   left adjoint (the Kan-extension/sheafification presentation of the same
   module pullback). `left` is its exact `mapDerivedCategory`, `right` is the
   actual `rightDerivedFunctor`, and `derivedAdjunction` is constructed by
   `mapDerivedCategoryRightDerivedAdjunction`. Exactness, additivity and
   K-injective resolution fields are in the existential conclusion, not extra
   assumptions on f or the coefficients. Verdict: the ordinary, uncompleted,
   unbounded operations, with no arbitrary derived functor or adjunction.
4. **Derived tensor on K-flat total complexes.** `tensor` uses the existing
   `SheafOfModules.monoidalCategory`; `total` uses the existing bifunctor total
   complex. I opened both forms of the K-flat predicate in `KFlat`, the
   independent-coefficient resolution signature, `FlatOnSite`, and Mathlib's
   `BifunctorShift`. `resolving` uses the retained recorded `IsKFlat` (total
   tensor against every acyclic complex) and flatness of every term.
   `TensorModel.representative` is a natural isomorphism on the full category
   of *all* resolving pairs, not merely a family of object isomorphisms.
   `descent` determines natural transformations after this restriction.
   Together these specify a presentation of the localized total tensor.
   `totalComponent` reuses `tensorPullbackTotalComponent`; its inverse ordinary
   comparison on every summand has the orientation in Stacks 07A4.
   `totalMap` uses those components and the stated differential equation.
   Verdict: the recorded tensor, with its direct sums and signs, not a new
   freely chosen tensor operation.
5. **Localization at every V, U and f_V.** `data : ∀ V : Y.ProEt, Local ... V`
   uses `U := (proEtaleBaseChange f).obj V` and `Over.post` of that very
   functor. The coefficients are `R_Y.over V` and `R_X.over U`.
   `Local.coefficient_sections` makes the local ring map the global map at
   `T.left` for every `T : Over V`. I opened Mathlib's `Sheaf.over`,
   `SheafOfModules.over`, `overFunctor`, and `pushforward`: these have exactly
   the slice topology and sectionwise actions in
   `def-pur-localized-ringed-site`. `Restriction.model` constructs
   `overFunctor.mapDerivedCategory` and its actual factorization; the record
   does not supply a substitute restriction functor. Verdict: exact slice
   localization, without assuming V or U is an open subscheme.
6. **First natural isomorphism, on every E.** `Local.directImage` has type
   `g.operation.right ⋙ restrictionY.model.functor ≅
   restrictionX.model.functor ⋙ operation.right`, the first displayed formula
   in the node. `ordinaryDirectImage_sections` requires identity on each
   section of E over the base-changed object. `restrictsKInjective` uses the
   actual K-injective predicate. `directImage_representative` identifies the
   derived isomorphism with that ordinary comparison and the actual derived
   units on every K-injective representative. Verdict: natural and canonical,
   rather than an unspecified automorphism of the endpoints.
7. **Second natural isomorphism, on every P.** `Local.pullback` is
   `g.operation.left ⋙ restrictionX.model.functor ≅
   restrictionY.model.functor ⋙ operation.left`, in the node's orientation.
   `mate_counit` is the exchange-mate counit equation.
   `Operation.DerivedAdjunction.counit` normalizes the constructed derived
   counit against the ordinary counit on K-injectives. Thus the normalized
   direct-image comparison fixes this pullback comparison by adjunction.
   Verdict: canonical comparison, with the same quantification over P.
8. **Third natural isomorphism, on every M,N.**
   `restrictionTensorY.comparison` has the required bifunctor type; the
   analogous X comparison is supplied for the projection target.
   `Restriction.pure_sections` identifies the ordinary comparison with the
   sectionwise identity on pure tensors. `TensorComparison.representative`
   fixes its derived value by the signed total comparison on every resolving
   pair. `preserves` supplies the needed preservation of flat K-flat pairs.
   Verdict: precisely restriction of derived tensor, with naturality in both
   variables and no perfection or boundedness hypothesis.
9. **Equality of the projection arrows.** I opened
   `ProjectionFormulaArrows.derivedProjectionFormulaMate`: it is the existing
   `Adjunction.rightAdjointProjectionMap`, obtained by transposing the
   pullback-tensor comparison followed by the counit. Both occurrences in
   `Local.ProjectionCompatible` use that definition and the constructed
   adjunctions. `sourceIso` is tensor restriction followed by direct-image
   restriction; `targetIso` is direct-image restriction, tensor restriction,
   then pullback restriction. Their components are composites in the file,
   not fields whose values could absorb an incorrect projection map. The
   equality is the node's commuting square for every E and P. Verdict: exact.
10. **Canonical shifts.** `TensorShifts.first/second` are normalized by
    `mapBifunctorShift₁Iso` and `mapBifunctorShift₂Iso` for every integer n.
    I checked Mathlib's definitions: the first is sign-free, the second has
    the total-complex Koszul sign. `TensorComparisonShifts.first/second`
    impose the two commuting comparison squares, globally, locally and for
    restriction. `leftShift`, `rightShift` and `Restriction.modelShift` are
    constructed from the actual exact/right-derived functors.
    `directImage_shift`, `pullback_shift` and `counit_shift` impose shift
    compatibility for the normalized maps used in the projection mate.
    Verdict: the shift clause is present and substantive; it has not been
    replaced by a reflexive equation or an unnormalized shift structure.
11. **Local detection of isomorphisms.** The last conjunct quantifies
    `{A B : Der R_Y} (a : A ⟶ B)`, then every V, then an existential covering
    sieve S on V, then every arrow h : W to V in S. It tests
    `IsIso (((data W).restrictionY.model).functor.map a)` and concludes
    `IsIso a`. In particular the test is at W, not merely at V. Covering
    sieves express the node's covering families, allowing different covers
    for different V. Verdict: same quantifier order and conclusion.

**Source reading.** The shared clone does not have the untracked Stacks tex
checkout. I located and read the corresponding files in
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/`, checking the tag map:
04J0 = `sites-modules`, `lemma-localize-morphism-ringed-sites`;
08FI = `sites-cohomology`, `lemma-restrict-K-injective-to-open`;
0FN5 = `lemma-localize-cartesian-square-modules`;
07A4 = `lemma-pullback-tensor-product`;
0B56 = `equation-projection-formula-map`;
0E48 = `remark-compatible-with-diagram`; and
0944 = `lemma-projection-formula`. I read the surrounding assumptions too:
the discussion before 08FI treats any object of a ringed site, exact
restriction and its exact extension-by-zero left adjoint. 04J0 localizes a
continuous site functor at V and u(V), with the restricted ring map, and
identifies the ordinary direct-image routes. 0FN5 itself is the cartesian
localization case, not an arbitrary scheme base-change theorem; here the
ordinary square is supplied by 04J0 and the proof repeats its K-injective
method. 07A4 has arbitrary ringed topoi and uses flat K-flat total complexes.
0B56 constructs the arrow without a projection-formula-isomorphism assumption;
0E48 states the comparison square. The first proof sentence of 0944 tests
isomorphisms on a covering of every object. No ambient Noetherian,
quasi-compactness, boundedness, characteristic or enough-points hypothesis is
being omitted. The perfectness assumption of 0944 belongs to its eventual
projection-isomorphism conclusion, not this locality/comparison lemma.

**Edge cases and universes.** Empty schemes and empty site objects are not
excluded. Empty covering sieves are used only when the topology declares
them covering. Zero rings, zero modules, acyclic complexes and the zero
morphism are admitted. Complexes are indexed by all of Z; n=0 and positive
and negative shifts are included. The identity morphism and arbitrary c
are admitted. Site objects have universe u+1 and site morphisms universe u;
the generic helper signatures retain this distinction. Coefficients and
module sections have universe u+1 and derived localization uses its standard
size. `autoImplicit false` and the successful compile check that no variable
or universe was silently introduced. There is no finite index, characteristic,
nonempty, finiteness, or uniform-bound restriction hidden in the theorem.

**Independent searches and dependency audit.** I ran the following fresh
queries through the prescribed `msearch.py`; they are in `searches.jsonl`:

- LeanFinder: "Derived direct image on a slice site is compatible with the
  tensor counit projection morphism". Eight hits, including ordinary
  pushforward-adjunction counit formulas and exponentiable-morphism
  identities; no full derived restriction/projection comparison theorem.
- Loogle: `"overFunctor"`. Seven hits, including the existing module
  restriction and its composition comparison, and unrelated over-functor
  constructions; no full theorem.
- Grep: `overFunctor|pullbackPushforwardAdjunction` in
  `Algebra/Category/ModuleCat/Sheaf`. Fifteen hits, the ordinary constructions
  that this module reuses. I opened their signatures and bodies.
- Independent `rg` across upstream `WeilConjectures`, project `lean/Sheaf`
  and Mathlib for projection together with slice/localization/restriction,
  and for the declaration name, found related finite/constant-coefficient
  operations, exchange and projection interfaces, but no exact full match.
  The prior worker's LeanSearch outage remains recorded as unavailable,
  not evidence of absence.

I also read `coord/pefw-upstream-framework.md` and the group clone's exact
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
source. Its finite-coefficient interfaces do not replace this arbitrary
commutative-ring-sheaf statement. The current operations dependency's record
explicitly retains the identified-coefficient modules read above, although
its primary declaration now names a finite specialization. The retained
`IsKFlat` has the same total-tensor acyclicity meaning needed here; the new
independent-coefficient resolution interface states the requisite general
resolution. `def-pc-tensor-complex-sheaves` and
`def-weil-abstract-derived-category` use the exact Mathlib constructions
opened above. No new node or dependency module is present in this packet.
The helper records present this node's normalized comparisons and universal
properties; they do not copy an existing mathematical operation's data.

**Mismatches, changes and validation.** I found no mathematical mismatch
requiring an edit. I retained the Lean file and node record unchanged and
added only this independent review. The only difference between the sandbox
node and the repository node is `lean`; there is no `statement_change`, no
changed dependency list, and no citer correction to audit. I checked the
recorded `lean.statement` byte-for-byte against the theorem's signature: it
matches. Every declaration has its source/blueprint docstring, the main
docstring gives all seven proof steps, all lines are at most 100 characters,
all definitions have real terms, and the sole `sorry` is the named main
theorem. The authorized `scompile.py NC ... RingedProjectionRestriction.lean`
completed successfully with no errors or non-sorry warnings: the item took
19.8 seconds, nice 19, two threads, 60-second limit. The wrapper also checked
the required current dependency overlays. The required
`deliver2.py NC lem-weil-pbc-ringed-projection-restriction --no-push` then
returned `OK`: commit `8f38ddf5e6` passed the server preflight and compilation,
with nothing pushed. The same authorized wrapper is used for final delivery.

## Worker report

Module: `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`. Main declaration:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap`. It defines the map on the
underlying abelian groups of the existing O-module cohomology, and its pullback,
restriction, and edge-map specializations. No statement correction is needed.
The item gains the landed dependency `lem-pc-module-pullback-adjunction` so the
pullback name uses the shared canonical tensor-pullback adjunction unit.

Hypothesis and clause correspondence:

- Schemes X and Y and their morphism h are `{X Y : Scheme.{u}} (h : X ⟶ Y)`.
  No field, finiteness, separatedness, properness, or smoothness assumption is added.
- G and F are respectively `SheafOfModules.{u} Y.ringCatSheaf` and
  `SheafOfModules.{u} X.ringCatSheaf`, the underlying carrier of the recorded
  `Y.Modules` and `X.Modules`. These ring sheaves are definitionally the shared
  `moduleRings Y.toRingedSpace` and `moduleRings X.toRingedSpace`.
- The h-map is `φ : G ⟶ (pushforward h).obj F`. Mathlib's pushforward evaluates F
  on the inverse image of an open, and equips it with scalars through h-sharp.
  Its equivalence to a map from tensorPullback follows from the dependency's
  adjunction, rather than imposing a second input map or extra hypothesis.
- The degree `p : ℕ` is exactly p ≥ 0. Source and target are the forgetful images
  of `(RingedSpace.moduleCohomology Y.toRingedSpace p).obj G` and
  `(RingedSpace.moduleCohomology X.toRingedSpace p).obj F`. Thus these are the
  cohomology groups of O-module resolutions, not abelian-sheaf Ext cohomology.
- `ModuleCohomologyFMapData.I` and `.J` are the recorded Mathlib
  `InjectiveResolution F` and `InjectiveResolution G`, including their degreewise
  injectivity and quasi-isomorphic augmentations `.ι`. Mathlib indexes these by
  ℕ; this is the standard encoding of a complex zero in all negative degrees.
  There is no omitted negative-degree datum or excluded bounded-below case.
- `.K` is J-prime, an ℕ-indexed cochain complex of O_Y-modules; `.injective` states
  injectivity of every term, and `.lambda` is the chain map from termwise h_*I
  into K. `.quasiIso : QuasiIso lambda` supplies exactly its quasi-isomorphism.
- `.β` is the chain map J → K, and `.compatible` is the specified equation
  `J.ι.f 0 ≫ β.f 0 = φ ≫ (pushforward h).map (I.ι.f 0) ≫ lambda.f 0`.
  Lean composes left-to-right; this is beta-zero after s_G equals lambda-zero
  after h_*(s_F) after phi.
- `.a` identifies Γ(X,I) with Γ(Y,h_*I) as abelian-group complexes.
  `.sections` pins its inverse in every degree to the presheaf restriction
  along the equality h-inverse(Y) = X. Thus its components are the canonical
  identity of sections, not arbitrary automorphisms of these complexes.
- In the definition, `μ = D.a.hom ≫ Γ(Y,D.lambda)` is the vertical arrow.
  `.invertible p` is invertibility of its degree-p homology map, the consequence
  of its quasi-isomorphism needed to form the inverse.
- The definition chooses the full resolution data through the named existence
  theorem and composes `bG = H^p(Γ(Y,β))` with `inv (H^p(μ))` in that order.
  `eG` and `eF` are Mathlib's standard `InjectiveResolution.isoRightDerivedObj`
  comparisons. The two `ShortComplex.mapHomologyIso` factors are the standard
  exact-forgetful-functor comparisons between module and group homology. They
  transport the formula onto the recorded cohomology carriers without changing it.
- (a) `moduleCohomologyPullback h G p` specializes phi to the unit of
  `Classical.choose (exists_tensorPullbackAdjunction h)`. Its target is
  cohomology of `(tensorPullback h).obj G`.
- (b) `moduleCohomologyRestriction U G p` specializes to the unit of
  `restrictAdjunction U.ι`. The restriction functor has exactly the sections
  G(V) on an open V inside U, and its unit is G(V) → G(V ∩ U), with the standard
  inclusion identifications. Its target is cohomology of `(restrictFunctor U.ι).obj G`.
- (c) `moduleCohomologyEdgeMap h F p` specializes phi to the identity of
  `(pushforward h).obj F`.
- The parenthesized independence, linearity, degree-zero, identity, and comparison
  properties are forward pointers to other nodes, not extra clauses of this
  definition. They have not been asserted or silently assumed in its signature.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules`,
  `Scheme.Modules.pushforward`, `restrictFunctor`, `restrictAdjunction`,
  `Scheme.Modules.presheaf`; their section formulas and restriction adjunction
  were read in full.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction` (including its sectionwise unit).
- `Sheaf.Paper.PQFCohomology`: the node's recorded
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, whose signature and
  docstring were read. Its cohomology carrier is imported from
  `Sheaf.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`,
  `RingedSpace.globalSectionsFunctor`, `RingedSpace.globalSectionsComplex`.
  Its imports also supply the shared Grothendieck structure/enough-injectives instances.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, its augmentations and injective fields.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, complex morphisms.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `InjectiveResolution.isoRightDerivedObj`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `ShortComplex.mapHomologyIso`.

The source is Stacks 01FB, read at https://stacks.math.columbia.edu/tag/01FB
(the literature TeX is not present in this checkout). It explicitly chooses the
three resolutions and beta, then applies global sections and inverts the vertical
quasi-isomorphism. The adjacent functoriality section defines the three cases.
The existing project module `PushforwardInjectivesSectionsQuasiIso` was read as
well; the existence theorem's docstring names that DAG lemma and all five proof
steps of this node. The sole sorry is
`Scheme.Modules.moduleCohomologyFMapData_nonempty`; every definition has actual data,
with no sorry in its body. Its existence theorem supplies specified resolution
choices and the invertibility proof; it does not postulate an unconstrained map.

Edge cases: p = 0 is included; no vanishing assertion is smuggled into that case.
The zero modules and empty schemes admit the same categorical construction.
U = empty and U = top are allowed, as are identity and arbitrary scheme morphisms.
There is no assumption that h_* preserves injectives: the separate complex K is
retained. No independent universe is imposed on the site or resolutions.

Searches for an existing declaration:

- `msearch.py ... leanfinder "map on cohomology of sheaves of modules induced by a morphism to pushforward"`:
  eight hits, all pushforward section/morphism formulas, such as
  `SheafOfModules.pushforward_map_val`, `pushforwardNatTrans`,
  `pushforwardSections`, and `Scheme.Modules.pushforward_map_app`; none defines
  the cohomology h-map.
- `msearch.py ... loogle "Functor.rightDerived, InjectiveResolution"`:
  zero hits (unknown identifier `Functor.rightDerived` in that search service).
- `msearch.py ... leansearch "Functoriality of cohomology of sheaves of modules under a morphism of ringed spaces"`:
  service unavailable, Internal Server Error. No negative verdict inferred from it.
- `msearch.py ... grep "cohomologyMap|rightDerived.*map" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` for fmap/cohomology maps in source `WeilConjectures` and project `lean/Sheaf`:
  found etale/abelian-sheaf cohomology maps and scalar-cohomology constructions;
  none defines the Zariski O-module h-map here. In particular etale
  `Etale.cohomologyMap` does not have this site's objects or resolution category.
- `rg` for the item id in source `WeilConjectures`, and for the proposed full
  declaration names in source, project Lean, and `dag/lean_names_upstream.json`:
  no hits. No exact existing declaration was found.

Validation: `scompile.py G1 def-weil-pbc-module-cohomology-fmap` on the module passed
with exit code 0, compiled in 13.3 s, no errors or warnings. `autoImplicit` is false;
all binders and the universe are explicit. Delivery is intentionally left for the
independent second reader.

## Earlier second reading (a previous round; superseded)

Pending independent second reader. This worker has not performed or claimed that reading;
the dispatcher must assign it before delivery.

## Second reading by G1

I read the node statement, its source reference (Stacks Cohomology, Tags 01F7--01FB,
01EZ), and the copied module independently. The objects and clauses match as follows:

- `h : X ⟶ Y`, with arbitrary schemes and no finiteness, separation, field, or
  characteristic assumptions, is rendered by the binders in `ModuleCohomologyFMapData`
  and `moduleCohomologyFMap`.
- `G` and `F` are `SheafOfModules` over `Y.ringCatSheaf` and `X.ringCatSheaf`; the
  h-map `φ : G ⟶ (pushforward h).obj F` is the corresponding structure field and map
  argument. The pushforward is Mathlib's `Scheme.Modules.pushforward`, with its stated
  sectionwise inverse-image action.
- `p ≥ 0` is represented by `p : ℕ`; the source and target are the underlying
  additive groups of `RingedSpace.moduleCohomology` at `Y` and `X`, respectively.
- The resolutions `I` and `J` are `InjectiveResolution F` and `InjectiveResolution G`,
  hence are natural-number indexed and zero in negative degrees by the recorded
  convention. `K`, `injective`, `lambda`, `quasiIso`, `β`, and `compatible` render the
  chosen injective target complex, quasi-isomorphism, lift, and augmentation equation.
- `a` and `sections` render the canonical identification of sections of `h_*I` on `Y`
  with sections of `I` on `X`; `invertible` records the homology invertibility needed
  for the inverse. The definition composes `H(Γβ)` with the inverse of `H(μ)` and the
  standard resolution and homology comparisons, exactly as Equation 01FA prescribes.
- `moduleCohomologyPullback` uses the shared
  `exists_tensorPullbackAdjunction` unit, `moduleCohomologyRestriction` uses the
  restriction adjunction unit (including `U = ⊥` and `U = ⊤`), and
  `moduleCohomologyEdgeMap` uses the identity of `h_*F`. These are the three named
  specializations in the node.

The empty scheme, zero sheaves, empty and total opens, identity morphisms, and `p = 0`
all remain admissible. No characteristic or independent universe restriction is added;
all objects use the single explicit universe `u`. The source's choice data is represented
by the nonempty choice theorem, whose only proof is the permitted `sorry`; no definition
body is hollow.

I searched Mathlib, `WeilConjectures`, and the project with `msearch.py` (LeanFinder,
Loogle, and grep queries for cohomology maps, right-derived maps, and `fmap`), and found
only unrelated abelian-sheaf or pushforward declarations. No exact existing declaration
was found. The dependency declarations were checked, including the shared
`Scheme.Modules.tensorPullback` and `exists_tensorPullbackAdjunction`; the latter is
recorded in `stmt_deps` as `lem-pc-module-pullback-adjunction` and avoids a duplicate
adjunction notion.

No mismatch was found. I changed no Lean statement or node field; I only added this
second-reading record. The module compiles cleanly with `scompile.py` (14.4 seconds,
exit code 0, no warnings other than the intentional `sorry`).

## Worker report

This is a stage-2 statement delivery, not a second stage-1 split. The live node has a
reviewed stage-1 proof (Q61, 2026-10-22) but no Lean record. There is no released repair
note for this item. The earlier worker's refusal to re-split therefore does not apply
to this statement task. The natural-language statement, proof, and proof dependencies
are retained verbatim. The single added statement dependency is the already landed
`def-weil-strict-roos-model`, whose explicit construction is reused throughout.

`Sheaf.CategoryTheory.AugmentedScalarRoosResolution` states
`CategoryTheory.augmentedScalarRoosResolution`, with one whole-proof `sorry`. All other
new declarations are transparent definitions or abbreviations with real data. They
merely name the categories, functor compositions and equations within this statement;
no independent mathematical notion or separate DAG node is introduced.

The theorem concludes the public transparent predicate `ScalarFormulas` specialized
EXACTLY to the two recorded module categories and Mathlib scalar restriction. Its body
is the full conjunction and existential package described below. Defining the formulas
first in abstract categories supplies local category structures while elaborating them;
it does not assert the formulas for arbitrary functors or add any theorem hypothesis.
This avoids repeated expensive unfolding of the sheaf-category structures. The default
60-second limit and default heartbeat budget are retained.

The hypothesis and clause correspondence is as follows.

- Scheme and small pro-etale site: `Z : AlgebraicGeometry.Scheme.{t}` and
  `AlgebraicGeometry.Scheme.ProEt.topology Z`. Modules and rings live in
  `max r (t + 1)`. The site's object universe is `t+1` and its morphism universe is `t`;
  these are not equated. The conventional chosen derived-category instances are explicit
  at a common arbitrary localization universe `w`. The standard `HasSheafify` and
  `WEqualsLocallyBijective` infrastructure is also explicit at `max r (t+1)`, as in
  the recorded general-site dependencies. These provide the usual abelian-category
  structures; they impose no geometric or coefficient restriction and no universe
  equality. This also avoids Lean selecting a smaller-universe sheafification instance.
- Commutative ring sheaves and scalar map: `C R : Sheaf ... RingCat` with pointwise
  commutativity `_hC`, `_hR`, and `i : C ⟶ R`. Forgetting the commutativity structure in
  the sheaf's category loses no data because commutativity is a proposition.
- The actual coefficient categories are `Modules Z R = ringedSiteModules R` and likewise
  for C. The complexes are `CochainComplex ... ℤ`; the towers use the same construction on
  `ℕᵒᵖ ⥤ Modules`. Natural index n denotes the paper's positive index n+1.
- Scalar restriction is exactly `SheafOfModules.restrictScalars i`. `F.mapHomologicalComplex (.up ℤ)` applies
  it degreewise and `mapTower F` applies it levelwise and degreewise. The first
  three conjuncts assert finite-limit, finite-colimit and finite-biproduct preservation.
  No flatness of i is assumed.
- The existing `roosP`, `roosU` and `roosF` give B, 1-s, and Cone(1-s)[-1]. Their source
  uses the recorded `towerTransitionEndomorphism`; `roosχ` gives the coordinate order
  `(y,x)` in degree p+1. The first conjunct of `ChainFormulas` spells out the differential
  `(-dy-Fx,dx)`, with the full integer-degree shifts.
- P is the product comparison as an isomorphism of complexes. Its projection equation
  says that it sends each restricted product projection to the corresponding projection
  of the restricted tower. This uniquely specifies the identity on tuples of sections,
  in both directions. It is an isomorphism of complexes, so it also respects differentials;
  the next conjunct separately records compatibility with 1-s.
- The chain isomorphism c is pinned by `ConeCoordinates`, its two-coordinate formula: restrict the existing
  coordinates, take the canonical finite-biproduct comparison, and apply P to both
  coordinates. Its strict-map naturality is a separate displayed equality.
- `ChainFormulas` is asserted for BOTH module categories. Its second and third conjuncts
  pin all strict maps diagonally by `roosPmap`, including the inverse of `roosF.mapIso f`,
  which uses the product of `f.inv`. Functoriality supplies composition and identity.
- A transition-compatible homotopy is precisely `Homotopy f g` in the category of tower
  complexes: every degree component is a natural transformation. `productHomotopy`
  uses the canonical evaluation/product isomorphisms and `Pi.map` of its components.
  The fourth conjunct of `ChainFormulas` asserts a Roos homotopy with components (-H,H).
  The target degree is written `p-1+1` where needed so the canonical coordinates type
  without a hidden cast; it is the integer degree p.
- A strict augmentation is the compatible family b and equation hb. The last conjunct
  of `ChainFormulas` is exactly `(0,b^Pi)`, using the existing chain map `roosAugment`.
  The preceding conjunct gives the one-ring naturality equation with any f and v.
- `RF_R`, `RF_C`, their units ηR, ηC and their `IsRightDerivedFunctor` properties mean
  the total right derived ordinary inverse-limit functors. These are given as universal
  pairs to allow every choice of the ordinary derived functor, not assumed comparison
  isomorphisms. `roosLimitFunctor` is the existing termwise ordinary limit on complexes.
  The ringed strict-tower dependency supplies such universal pairs.
- ρR and ρC are NATURAL ISOMORPHISMS from `roosF ⋙ Q` to `Q ⋙ RF`, not just per-degree
  cohomology comparisons. `ResolutionNormalized` is asserted for each. Its first
  conjunct quantifies over EVERY quasi-isomorphism q into a K-injective tower I, with
  no assumption of injective individual terms. Both `roosF.map q` and `roosι I` are
  asserted quasi-isomorphisms. ε is exactly Q(j_I), d is the isomorphism characterized
  by `d.hom ≫ RF.map (Q.map q) = η.app I`, and ρ is exactly Q(Roos(q)) ε.inv d.hom.
- The next normalization conjunct identifies `Q.map (roosAugment b hb) ≫ ρ.hom.app X`
  with `Q.map (roosAugmentLimit b hb) ≫ η.app X`. This is the actual canonical augmented
  map: if b is the corresponding constant-tower map, naturality of the UNIVERSAL unit
  rewrites it as the constant-tower unit followed by RF(Qb). Thus the unit has not been
  replaced by an unconstrained arrow or a chosen isomorphism of Roos triangles.
- The last normalization conjunct handles a separate resolution p of `constantTower L`
  into J, a comparison a:J→I and a supplied tower homotopy between p≫a and b≫q.
  The map lam:L→lim J is pinned by ALL its projections to the components of p. Its
  composite with Q(lim a) and the same normalized d equals the augmented map through ρ.
  Both resolutions are arbitrary K-injective resolutions; no termwise injectivity is
  imposed. The limit universal property supplies the specified lam for every p.
- Dr and φ are a localization of exact restriction with a fixed natural factorization
  `Q_R ⋙ Dr ≅ restriction i ⋙ Q_C`. Since Q_R is a localization, this is exactly D(r),
  independent up to the unique compatible isomorphism. β is an isomorphism in the
  DERIVED CATEGORY, and its defining equality is the conjugation by ρR inverse, φ,
  Q(c) and ρC. The next conjunct gives strict-map naturality.
- The final conjunct covers any f:rW→W', v:rL→L' with the componentwise augmented square.
  It states BOTH the chain equality and the derived equality. The latter includes φ at L
  explicitly, so its source is D(r)(Q_R L). The case f and v equal to identities is the
  unadorned compatibility of the canonical augmented maps. The preceding one-ring clause
  supplies the formula without r and c over either ring.
- There are no boundedness or completeness hypotheses anywhere; all complexes use ℤ.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `AlgebraicGeometry.Scheme.ProEt.topology` (`def-weil-pbc-proetale-site`).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, exactly
  Mathlib's `SheafOfModules` (`def-weil-sheaf-of-modules-category`).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (`def-pc-sheaf-restrict-scalars`).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`
  (`def-pc-cochain-complex-modules`).
- `Mathlib.CategoryTheory.Functor.OfSequence`: `CategoryTheory.Functor.ofOpSequence`,
  `CategoryTheory.NatTrans.ofOpSequence`; functors out of ℕᵒᵖ are the recorded inverse
  systems (`def-weil-inverse-system`).
- `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`:
  `CategoryTheory.towerProductShift`, `CategoryTheory.towerTransitionEndomorphism`,
  used inside the canonical model (`def-weil-tower-transition-endomorphism`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` (`def-weil-abstract-derived-category`).
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, for the actual
  universal derived-limit pair, with the ordinary-limit-on-complexes presentation
  (`lem-weil-pbc-ringed-strict-tower-homotopy-limit`).
- `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`
  (`lem-weil-strict-roos-comparison`). Its normalization and naturality determine the
  same ρ used here, now with the arbitrary-resolution extension below.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosU`, `roosPmap`, `roosχ`,
  `roosAugment`, `roosAugmentLimit`, `roosι`, `roosLimitFunctor`
  (`def-weil-strict-roos-model`, the only added statement dependency).

The module also imports the already stated proof dependencies, without `public`:
`CategoryTheory.strictRoosDerivedLimitComparison` from
`Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`, `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`,
`Functor.mapDerivedCategoryFactors` and the arbitrary-resolution right-derived-functor
module. `CochainComplex.IsKInjective` is imported publicly because the statement uses it.
All signatures and docstrings were read from the recorded local source modules.

Edge cases checked before writing: zero towers; zero coefficient sheaf; empty scheme;
identity coefficient map; identity and zero transition maps; identity and inverse strict
isomorphisms; all integer degrees, including degree zero and negative degrees; unbounded
towers; nonflat ring maps such as quotient maps; K-injective towers without injective
individual terms; separate resolutions whose comparison commutes only up to homotopy.
For zero transitions compatibility forces b=0, and 1-s is the identity, so the cone is
contractible. For identity transitions b is the diagonal constant tuple. The signed
homotopy calculation has mixed term HF-F'H=0. No excluded case or statement fault was
found. No STATEMENT-DISPUTED flag or statement correction is needed.

Searches actually run:

1. msearch.py leanfinder: "Scalar restriction gives a natural isomorphism of augmented
   Roos shifted mapping cones computing derived inverse limits with K-injective
   resolution normalization". Eight hits, principally `mappingCone.mapHomologicalComplexIso`
   and its component comparisons; these handle additive functors and cones but not
   sheaf products, augmentations or universal derived-limit units.
2. msearch.py loogle: `SheafOfModules.restrictScalars`. Four exact restriction-functor,
   additive-instance and value hits; this is the reused coefficient functor, not the
   normalized Roos theorem.
3. msearch.py grep: `Roos|roos|restrictScalars` in `Algebra/Homology`: zero hits.
4. rg over both `lean/WeilConjectures` and `lean/Sheaf` for the exact item id: no attached
   declaration. Searches for Roos/scalar combinations found `StrictScalarCompletionUnit`,
   `ScalarPullbackStrictConeNaturality`, `RestrictionOfScalarsExact`, `RoosConeCalculus`,
   `StrictRoosModel` and the comparison modules. These specialize to other coefficient
   data or supply individual components. Their full statements do not give every clause
   of this item. The existing generic strict Roos construction IS reused; the added
   dependency prevents a second definition of it.

5. msearch.py leansearch: "Restriction of scalars for sheaves of modules commutes
   naturally with augmented Roos complexes and the universal total derived inverse
   limit unit". Eight hits: RestrictScalars, the presheaf/module/sheaf restriction
   functors, a module-category pseudofunctor, and LinearMap.restrictScalars. The actual
   sheaf functor is reused; no hit states the normalized augmented comparison.

Compilation and delivery validation are recorded after running the prescribed wrappers.

Validation: `scompile.py O3 lem-sfb-augmented-scalar-roos-resolution` compiled the
sandbox module in 7.6 seconds and the actual library module name in 7.4 seconds,
with exit code 0 and no non-sorry warnings. The default heartbeat budget and the
60-second per-file limit were used. Earlier elaboration faults were repaired by
explicit category arguments on localization functors, the transparent formula package,
and the standard sheafification structures at the correct universe. No theorem was proved.

The prescribed `deliver2.py ... --no-push` returned:
`OK (dry run): commit 729d6541f76 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the module, the node record and this report. The delivery
wrapper supplies the honest second-reading status; independent mathematical review is
performed by the maintainer, as required for directly dispatched workers.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

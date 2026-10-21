## Worker report

The module `Sheaf.CategoryTheory.RingedDerivedPushforwardLinear` states
`CategoryTheory.ringedDerivedPushforward_linear`. It has one theorem, with `sorry`
as its entire proof, and introduces no definitions. The node changes only in `lean`.
No repair note for this item is present. No statement correction or disputed statement
is needed. The module docstring names the sources, and the theorem docstring gives
all six steps of the node's proof.

Clause-by-clause correspondence:

- The commutative scalar ring is `(R : Type v) [CommRing R]`. Its universe is
  independent of the site and module universe.
- Sites small in the module universe are `{C D : Type u} [SmallCategory C]
  [SmallCategory D]`, with topologies `J`, `K`, coefficient sheaves
  `A : Sheaf J RingCat.{u}`, `B : Sheaf K RingCat.{u}`, and modules in universe `u`.
  This follows the recorded ringed-topos interface and the size convention's
  replacement by small skeletons; it imposes no condition such as existence of
  terminal objects in the presenting sites.
- The morphism from `(Sh(D),B)` to `(Sh(C),A)` is
  `(u : RingedToposMorphism B A)`. The order is deliberate: its inverse image
  goes from sheaves on C to sheaves on D, `u.ringMap` goes from the inverse image
  of A to B, and `u.modules` goes from B-modules to A-modules. This is the
  recorded general geometric-morphism interface, without a site functor.
- The two unital global coefficient maps are `sA : R →+* RingCat.sectionsSubring A.obj`
  and `sB : R →+* RingCat.sectionsSubring B.obj`. A member of this subring is exactly
  a family indexed by opposite site objects compatible with every restriction.
  Thus `(sA r).val U` and `(sB r).val V` are the restrictions of the actual global
  sections, even when the site has no terminal object.
- `centralA` and `centralB` assert that these values commute with every element
  of each section ring, for every scalar and every object. Neither coefficient
  sheaf is assumed commutative.
- `compatible` expresses `c(u⁻¹sA(r)) = sB(r)` on generalized elements. For any
  sheaf T and map z to the underlying sheaf of A with constant section values
  `(sA r).val U`, it requires `(u.inverse.map z) ≫ u.ringMap` to have constant
  values `(sB r).val V` on every section of `u.inverse.obj T`. This is equivalent
  to the global-section equality: z is the global-section map precomposed with
  the unique map T to the terminal sheaf; conversely test T equal to the
  terminal sheaf. The inverse image preserves the terminal sheaf by the
  `leftExact` field of the recorded geometric morphism. Hence this neither
  adds a hypothesis nor assumes the site has a terminal object.
- The module categories are the recorded `ringedSiteModules.{u} A` and
  `ringedSiteModules.{u} B`, transparently Mathlib's `SheafOfModules`.
- The conclusion supplies `LA` and `LB` of type `Linear R` on these categories.
  Its first two conjuncts specify `(r • f).val.app U x = (sA r).val U • f.val.app U x`
  and the corresponding formula for B, for every M, N, f, r, object and section.
  These formulas characterize the scalar action on all morphisms; these are
  the prescribed central actions, not unconstrained linear structures.
- The ordinary unbounded derived categories are `DerivedCategory` of these
  module categories. `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wB}`
  are the recorded localization size choices. They do not add exactness,
  boundedness, constructibility or completeness hypotheses.
- The conclusion supplies `enough`, namely a quasi-isomorphism from every
  complex to a K-injective complex, rather than assuming such resolutions.
  The functor is exactly
  `u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough`. Reading its source
  shows that it chooses the universal pair of
  `exists_rightDerived_of_enough_isKInjective`; its unit is invertible on
  K-injectives, and its comparison is `RF(Qa)` followed by the inverse unit.
  This is the same functor and comparison used by the recorded arbitrary-resolution
  map-computation theorem. It is determined up to the unique unit-compatible
  isomorphism, not an arbitrary functor with an existence property.
- The instance-bound lambda installs LA and LB only inside the conclusion.
  Mathlib's `DerivedCategory.instLinear` then supplies the induced derived
  structures, with its linear localization Q and linear shifts. The third and
  fourth conjuncts are respectively `RF.Additive` and `Functor.Linear R RF`.
- The last conjunct explicitly states `RF.map (r • 𝟙 N) = r • 𝟙 (RF.obj N)`
  for every derived object and scalar. The first two conjuncts and linear Q
  identify these identity multiples with multiplication by the actual sections.
  No preservation of exact sequences by `u.modules` is assumed anywhere.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including `adj`, `ringMap`, `module_linear`,
  `modules`, its additive instance and natural underlying-sheaf comparison.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  reusing Mathlib `SheafOfModules` with its Hom and abelian structures.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`; and
  `Mathlib.CategoryTheory.Linear.LinearFunctor`: `CategoryTheory.Functor.Linear`.
  These are the recorded Mathlib matches for the two linearity definitions.
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`: `DerivedCategory.instLinear`,
  linear Q/Qh and linear shift instances, the recorded match for
  `lem-weil-linear-abelian-derived-category`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `Functor.kInjectiveDerivedMapComputation`, its `kInjectiveResolutionHomTarget`,
  `kInjectiveHomotopyImage`, `kInjectiveDerivedResolutionMap` and transition helpers;
  also read its imported `RightDerivedFunctorOfQuasiIsoResolutions` construction,
  universal property, invertible unit and resolution comparison.
- Proof-only imports are
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
  (`SheafOfModules.isGrothendieckAbelianOfUniverses`) and
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
  (the functorial replacements, their monomorphic quasi-isomorphisms, K-injectivity
  and injective terms recorded for `lem-pur-kinjective-degreewise-existence`).
- `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit` publicly supplies the existing
  `siteAbelianHasSheafify` and `siteAbelianWEqualsLocallyBijective` transport
  instances. These make the abelian module categories available without additional
  sheafification hypotheses; no instances are copied into this module.

Edge cases checked mathematically: R can be the zero ring (a unital map then forces
all coefficient section rings to be zero); either coefficient sheaf may be zero;
r=0 and r=1 give zero and identity maps; zero complexes and arbitrary unbounded
complexes remain included. Empty sites and sites with empty covering families are
included. No site terminal object, nonempty object set or chosen resolution is an
input hypothesis. On a point topos with noncommutative matrix coefficients the
centrality hypothesis is essential: multiplication by diag(1,0) fails to commute
with E12, so multiplication by that section is not an endomorphism of the regular
left module. Both centrality binders are retained. Scalar and derived morphism
universes remain independent. The existential resolution condition is a conclusion
and contains no monomorphism, exactness or boundedness restriction.

Searches (all remote Mathlib searches used the prescribed `msearch.py` wrapper and
are logged in `searches.jsonl`):

- LeanFinder: "The unbounded right derived direct image of a morphism of ringed
  topoi preserves compatible central scalar actions over a commutative ring";
  eight results about ordinary module pushforward, its adjunction and sections,
  including `SheafOfModules.pushforward`; no derived central-scalar theorem.
- Loogle: `CategoryTheory.Functor.Linear, CategoryTheory.Functor.totalRightDerived`;
  zero results.
- LeanSearch: "A category of sheaves of modules is linear over compatible central
  global scalar sections"; eight module-category and sheafification results;
  no theorem on this arbitrary ringed-topos derived functor.
- Mathlib grep: `central|Linear` in `Algebra/Category/ModuleCat/Sheaf`: zero hits.
  `Linear|linear` in `CategoryTheory/Triangulated/DerivedFunctor`: zero hits.
  The same query in `Algebra/Homology/DerivedCategory`: 23 hits, including the
  reused derived linear structures and `Functor.instLinearDerivedCategoryMapDerivedCategory`.
  Read `ExactFunctor.lean`: the latter requires an exact underived functor,
  so it is not the theorem here.
- Project/source rg: `Central.*(Scalar|Action)|central.*(Scalar|Action)|centralSection|
  central.*[Ss]ection|compatibleCentral|CompatibleCentral|section.*Linear|Sections.*Linear`,
  and searches for ringed/derived/pushforward linearity, in `lean/WeilConjectures`
  and `lean/Sheaf`. Read `SheafOfModules.homLinear` in the upstream HomModule
  module: it requires commutative coefficient sheaves. Read
  `proEtaleRingDerivedOperations_scalarLinearity`: it concerns the small pro-etale
  sites of schemes, commutative coefficients, and a structural isomorphism.
  The etale/pro-etale `linear_rightDerivedLowerStar` instances also concern those
  specific sites and coefficient-valued sheaves. None states the arbitrary
  geometric-morphism, possibly noncommutative ring-sheaf statement.
- `grep -rn` for this item's blueprint id in `lean/WeilConjectures` found no match.
  Searches for the new declaration name in Mathlib, `lean/WeilConjectures` and
  `lean/Sheaf` found no collision.

Validation: the final module is compiled with the prescribed `scompile.py`, on the
server against the live published library. All variables and universes are explicitly
bound (`autoImplicit false`). No local notation, local instance, private definition,
`let` statement binder or postponed construction is used. Only the theorem proof
is postponed. The required delivery dry run follows this report.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

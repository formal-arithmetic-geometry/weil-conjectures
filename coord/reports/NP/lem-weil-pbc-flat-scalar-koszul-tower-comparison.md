## Worker report

The module `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison` states
`CategoryTheory.FlatScalarKoszul.flatScalarKoszulTowerComparison`, with `sorry` as
its entire proof. The node's mathematical statement, dependencies and proof are
unchanged. There is exactly one postponed theorem. All helper definitions have real
data and belong to this node's specified coordinate or comparison constructions.
No new independent notion, dependency repair, or statement correction is needed.

Sources read: Stacks algebraization.tex, lemma-derived-completion-koszul (0A0E),
including the identification of the finite dual Koszul model; sites-cohomology.tex,
lemma-Rf-commutes-with-Rlim (0A07), including its diagram-topos proof and warning
that derived inverse limit is not an ordinary derived-category limit. The recorded
Koszul-system and strict-tower interfaces and their docstrings were read in full.
The stage instructions and the CompactObject example were read; that example's
Sheaf module is now withdrawn, so its node's current upstream record was also read.
There was no repair note for this item.

Hypotheses and objects, matched individually:

- A small site is `{S : Type u} [SmallCategory S] {J : GrothendieckTopology S}`.
  The existing small-site Koszul interface uses this common site/coefficient
  universe. There is no extra property of the topology or of its points.
- Ring sheaves and their map are `{R B : Sheaf J CommRingCat.{u}}` and
  `(φ : R ⟶ B)`; the functor `restriction` is precisely Mathlib's
  `SheafOfModules.restrictScalars` applied to the underlying ring-sheaf map.
- Flatness means exactness of `B tensor_R -`: `_hflat` is the conjunction of
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for the published
  `SheafOfModules.RingedTensor.tensorFunctor φ`, the sheafified extension of
  scalars. No regular-sequence, nonzero-ring or finite-generation assumption is
  added. This hypothesis is retained even though the finite coordinate part of
  the comparison itself does not need flatness.
- The finite generator list is `(r : ℕ)` and
  `(a : Fin r → (R.obj ⋙ forget CommRingCat).sections)`.
  `imageSections φ a` applies the actual ring-sheaf morphism sectionwise.
- `Modules` transparently abbreviates the recorded `ringedSiteModules`, not a
  separately constructed module category; complexes are the recorded
  `ringedSiteComplex`, with all integer degrees. There is no boundedness on N.
- The four `HasDerivedCategory.{w}` parameters choose the same arbitrary
  localization morphism universe for modules and strict towers over both rings.
  The categories are the recorded ordinary unbounded `DerivedCategory`.
- `ringedKoszulDualTower` is the recorded finite dual ordered Koszul tensor.
  Its index `op m`, for `m : ℕ`, denotes power `m+1`, exactly the positive powers
  in the item. Its transitions are the recorded dual transitions (a_j,1).
  `ringedKoszulTensorTowerFunctor` is the recorded degreewise transpose of the
  actual total tensor complexes into complexes of strict towers.

Conclusions, matched clause by clause in the order of the theorem:

1. `h` is a natural isomorphism between the actual tensor-tower functor followed
   by `restrictTowerComplex φ`, and `restrictComplex φ` followed by the actual
   R tensor-tower functor. A morphism in this category is a chain map whose
   degree maps are natural transformations of strict towers. Thus h and its
   inverse commute with all differentials and transitions, and are natural in N.
2. The first conjunct fixes the identity on every exterior coordinate. A Boolean
   vector `e : Fin r → Bool` is the corresponding subset. `positiveBasis` is
   constructed recursively from the double-complex basis inclusions, unitors,
   tensor maps and `CochainComplex.ιMapBifunctor`. `dualCoordinate` evaluates
   `homComplexπ` on that actual positive basis vector, followed by evaluation at
   one, in the correct dual degree, and is zero elsewhere. `coordinate` uses
   `HomologicalComplex.mapBifunctorDesc` and the ordinary right unitor to project
   the total tensor onto `N.X (n + degree r e)`. The equality says the h-component
   followed by the R projection is the restriction of that exact B projection.
   These are actual coordinate maps, not unspecified isomorphisms of graded
   objects or a simultaneous arbitrary choice of two bases.
3. The second conjunct is equality of the components of the strict degree-zero
   maps: the restricted `ringedKoszulTensorUnitComponent` followed by h equals
   the R component. It is quantified over every degree and every tower index,
   hence is equality of the strict coaugmentation chain maps.
4. `DB` and `DR` are the existing `RingedKoszulLimitPresentation` structures.
   Their tensorFactors identify localization of the actual strict tensor towers
   with the derived tensor-tower functors. Their inverseLimit, comparison,
   isRightDerived and comparison_isIso fields are the total right derived
   inverse limit, its universal property, and its computation on K-injective
   tower complexes. No ordinary limit on the derived category is substituted.
5. `hD` is the natural isomorphism on D(B). The third conjunct identifies its
   localization with Q(h) for every representative N, using the actual
   tensorFactors and exact restriction localization comparisons. This supplies
   the asserted descent and independence of the representative.
6. `alpha` is the comparison between restricted total inverse limit and total
   inverse limit after tower restriction. The fourth conjunct normalizes it on
   every complex X by `limitComparison φ`, obtained by applying
   `NatTrans.mapHomologicalComplex` to `preservesLimitNatIso` of restriction.
   That is the canonical `limit.post`, identity on compatible families. The
   equation includes both defining right-derived comparisons and the exact
   tower-restriction factorization. It fixes a natural derived arrow before
   considering evaluations.
7. `gamma` has exactly source `DB.completion ⋙ restrictDerived φ` and target
   `restrictDerived φ ⋙ DR.completion`. The fifth conjunct defines its map to be
   alpha at the tensor tower followed by `DR.inverseLimit.map (hD.hom.app E)`.
   Thus it is induced by the specified strict comparison.
8. The sixth conjunct is the required actual derived-arrow equation
   `Res(DB.unit E) ≫ gamma_E = DR.unit(Res E)`. The units are the recorded
   `RingedKoszulLimitPresentation.unit`, obtained from `ringedKoszulLimitUnit`
   followed by the right-derived comparison and representative isomorphisms.
9. `pB` and `pR` are natural transformations from total inverse limit to exact
   derived evaluation. Conjuncts seven and eight normalize each against
   `limitProjection`, the degreewise ordinary limit projection, on every tower
   complex. Conjunct nine is the derived evaluation square for every E and m.
   `evaluationComparison` consists of the canonical exact-functor composition
   comparisons, using the identical underived evaluation/restriction composite.
   The theorem never claims that projections determine arbitrary derived arrows.
10. The final conjunct retains `r=0` and supplies the constant-completion
    identifications `eB` and `eR`, with unit composed with each identification
    equal to identity. Its last equation says gamma becomes identity under
    these identifications. For the strict h, the earlier actual coordinate
    condition already specializes to the sole empty-subset coordinate, so it
    is identity under the constant-tower tensor-unit identifications as well.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `CochainComplex.ιMapBifunctor`; the total coordinate descendent is the
  corresponding `HomologicalComplex.mapBifunctorDesc`.
- `Sheaf.CategoryTheory.RingedKoszulSystem`: `ringedKoszulFactor`,
  `ringedKoszulDiagram`, `ringedKoszulDualTower`, `ringedKoszulTensorTowerComplex`,
  `ringedKoszulTensorTowerFunctor`, `ringedKoszulTensorUnitComponent`,
  `RingedKoszulLimitPresentation`, its `completion` and its `unit`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, whose statement
  supplies total inverse limit and computation on K-injective strict towers.
- The coordinate helpers also use the existing
  `WeilConjectures.Algebra.Homology.HomComplexComponents.homComplexπ` API
  (declaration `CategoryTheory.homComplexπ`) and
  `SheafOfModules.homObjUnitIso`; no replacement Hom complex is defined.
- `Sheaf.Paper.RingedTopoiTensorSections`:
  `SheafOfModules.RingedTensor.tensorFunctor` for the stated flatness hypothesis.
- `Sheaf.Paper.RestrictionDerivedProducts`: the published limit/colimit
  preservation instances for restriction, used to form the exact derived maps
  and the ordinary compatible-family comparison.

All already-stated proof dependencies are imported: bounded-above flat K-flatness,
fixed K-flat tensor triangulatedness, flat ringed diagram restriction, derived
restriction products, right-adjoint K-injective preservation, ringed tower
pushforward/limit comparison, levelwise tower abelianness, and general-site
K-injective resolutions. Their recorded signatures and docstrings were read.
The theorem's docstring carries all eight proof steps with their dependency ids.

Edge cases checked mathematically before drafting:

- For r=0, `degree 0 e = 0`, the unique positive basis is the single-complex unit
  inclusion, and the dual and total coordinate maps are their ordinary unit
  evaluations. The final identity clause is explicitly present.
- For r=1, degrees are 0 and -1; the coordinate maps select C^n and C^(n+1).
  Both coefficient actions on the second coordinate are phi(a)^(m+1), and its
  transition is phi(a). The coaugmentation selects the empty coordinate.
- For r=2, the four coordinates have the ordered tensor signs. Dual evaluation
  uses the same ordered positive basis over both rings, so any dual Koszul sign
  convention is transported identically. No regularity of a_1,a_2 is needed.
- Repeated, zero and unit generators are allowed: none of the coordinate maps
  divides by a generator, and the transition/unit equations remain typed.
- Zero rings, zero complexes and empty underlying sites are not excluded by
  nontriviality or nonemptiness assumptions. No boundedness is imposed; each
  relevant total term has only finitely many Koszul coordinates.
- Arbitrary common derived localization universe w is retained. The canonical
  ordinary limit comparison uses `preservesSmallestLimits_of_preservesLimits`
  to restrict the published site-universe limit-preservation instance to the
  countable index universe; this is a size transport, not an extra hypothesis.

Searches actually run through msearch.py for NP and this item:

- LeanFinder: "Restriction of scalars along a flat morphism of ring sheaves
  identifies strict Koszul tensor towers and their derived inverse limits with
  completion units". Eight hits, mainly ordinary module adic completion plus
  `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`; none states this
  strict ring-sheaf tower or its units and normalized derived evaluations.
- Loogle: `"Koszul", "restrictScalars"`. Zero hits.
- Mathlib grep: `Koszul.*[Rr]estrict|[Rr]estrict.*Koszul|[Rr]estrict.*[Hh]omotopy[Ll]imit`.
  Zero hits.
- LeanSearch: "Restriction of scalars commutes with strict Koszul tensor towers
  and total derived inverse limit preserving the completion unit". Eight hits
  on ordinary restriction of scalars, including presheaf restriction and module
  limit preservation; no strict Koszul tower comparison.
- Project rg with the same Koszul/restriction expressions in WeilConjectures
  and Sheaf, and explicit grep for this blueprint id in WeilConjectures.
  No declaration for the item. Hits for Koszul open restriction and slice
  evaluation do not change coefficients. The broader scalar/Koszul search
  found `ExteriorAlgebra.nonempty_koszulBaseChangeIso`; its full statement was
  read. It concerns ordinary-ring chain complexes and scalar extension, with
  no sheaf strict tower, unit or derived inverse limit, so is not this node.
- The full namespace and theorem name were searched in Mathlib, both project
  source roots and dag/lean_names_upstream.json, with no existing declaration.

Validation: all compiles use the prescribed scompile.py on the live server,
with the unchanged 60-second single-file limit. The first elaboration exposed
one reversed naturality equation in imageSections; it was corrected. The next
exposed the countable-index limit-preservation size instance; it was supplied
using the existing smallest-limits transport. These were implementation errors,
not node faults. No statement is disputed. The final compile and delivery
preflight results are recorded below when complete.

Final validation: scompile.py passed both its sandbox check (42.3 seconds) and
its final-module check (29.7 seconds), with no warnings or errors. The required
deliver2.py --no-push dry run printed OK: the delivery passes the server preflight
and compilation. Only the module, the item's lean record and this report are
in the packet. The statement, proof and dependency lists remain byte-for-byte
unchanged from the read node.

The recorded Q is the finite dual of the positive Koszul tensor. The standard
signed tensor-dual identifications express it as the ordered tensor of negative
two-term factors appearing in the item and Stacks 0A0E. The same ordered positive
basis and its dual are used over R and B, so these identifications transport the
coordinate identity, transition maps and empty coordinate without any change of
coefficient-dependent signs.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

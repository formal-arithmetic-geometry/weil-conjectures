## Worker report

The delivery states `CategoryTheory.KoszulQuotientStrictResolution.koszulQuotientStrictResolutionBridge`
in `Sheaf.Algebra.Homology.KoszulQuotientStrictResolutionBridge`. Its proof alone is `sorry`.
The six helpers construct the specified strict left arrow, apply the recorded Roos functor,
reorder its coordinates, and form the actual ordinary and derived quotient towers using
existing normalized scalar-transition maps. No mathematical object is chosen from an
unspecified existence theorem. No existing node statement, proof, or proof dependency changes.

Sources read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`,
its reduction-as-cone and completeness sentences; Stacks `sites-cohomology.tex`,
`lemma-derived-tor-quasi-isomorphism-other-side` (06YT), `lemma-derived-base-change` (06YY),
and `lemma-derived-limit-is-ok` (0941); `algebraization.tex`,
`lemma-derived-completion-koszul` (0A0E). The node's seven proof steps are reproduced,
with the same dependency uses and the signed-interchange calculation, in the theorem docstring.

Hypotheses and objects, matched individually:

- A site small in the module universe: `{C : Type u} [Category.{v} C]`, topology `J`,
  `[EssentiallySmall.{r} C]`. The site-object, site-morphism and coefficient universes
  remain independent. The sheafification/composition instances specify the usual
  small-site category of modules; they do not assert an extra geometric condition.
- A commutative ring sheaf: `R : Sheaf J CommRingCat.{r}`. The common module category
  is the dependency's `SuccessiveDerivedQuotient.Modules R`, definitionally the
  recorded `ringedSiteModules` of the underlying ring sheaf.
- A global section: `s : (R.obj ⋙ forget CommRingCat.{r}).sections`. The recorded
  `KoszulRoos.unitSection R s` converts it to a section of the unit module without
  changing its components. Injective multiplication is exactly
  `hreg : Mono (globalSectionMultiplication R (unitSection R s))`.
- Exact countable products: `[HasExactLimitsOfShape (Discrete ℕ) (Modules R)]`.
- Unbounded derived categories: `[∀ S : Sheaf J CommRingCat.{r},
  HasDerivedCategory.{w} (Modules S)]`, with no boundedness predicate. These instances
  choose the localization categories used by the existing scalar interface.
  `localize R = HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh` is the
  existing localization, canonically compared to Q by `quotientCompQhIso`.
- `p` and `N : Normalization p` are the dependency's presentations of the actual
  scalar-extension universal pairs and their normalized adjunctions. Their ordinary
  objects/maps and units, derived counits, and restriction factorizations are fixed
  in that interface. Existence is already provided by
  `successive_derived_quotient_normalization`; the theorem works for every such
  normalized presentation. These are categorical presentation data, not flatness
  assumptions on coefficient maps or replacement conclusions.
- The actual rings B_j and quotient maps use `KoszulRoos.B` and `quotient`, aliases
  of `principalPowerRingQuotient` and `principalPowerRingProjection`. The harmless
  `[HasSheafify J CommRingCat.{r}]` is the chosen small-site ring sheafification.
  Lean index `n` always represents the positive power `j=n+1`.
- The actual L_j, their transitions and augmentation units are the recorded
  `principalKoszulTower`, `koszulTensorTower`, and `koszulRepresentativeAugmentation`.
  The shared convention is L_j tensor M, canonically symmetric to M tensor L_j;
  hence `1 tensor m` is exactly the requested `m tensor 1`. No second tensor is defined.
- An arbitrary complex and the given resolution: `M P : CochainComplex (Modules R) ℤ`,
  `f : P ⟶ M`, `hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P`,
  `hflat : ∀ i, SheafOfModules.IsFlatOnSite (R := R) (P.X i)`, `hf : QuasiIso f`.
  There is no epimorphism condition on f, no K-flatness condition on M, and no
  completeness or boundedness condition on either complex.

Conclusions, in the order they occur in Lean:

1. `b` is a family of maps between the actual quotient ring sheaves, with
   `h : quotient R s (n+1) ≫ b n = quotient R s n`. This characterizes quotient
   reduction, because the quotient projections are epic. `scalarTower` uses
   `ordinaryStep p N` and `derivedScalarTower` uses `derivedStep p N`; these are
   the dependency's actual transitions, including their normalization on pure tensors.
2. The strict span consists of the already constructed `koszulSpanLeft R s f` and
   the existential natural transformation `a` to `scalarTower ... P`. Strict tower
   compatibility is part of their natural-transformation types. The ordinary tensor
   functors in `scalarTower` have exactly the objects/maps of sheafified scalar extension,
   followed by the recorded restriction, applied termwise to P.
3. `c.app (op n)` is required to equal the termwise unit of
   `N.ordinaryAdjunction (quotient R s n)`, namely p mapping to 1 tensor p.
   The equation `koszulRepresentativeAugmentation ... ≫ a.app ... = c.app ...`
   pins a on the degree-zero Koszul summand. The subsequent `summand ... ≫ a.f = 0`
   for every Koszul degree `i ≠ 0` pins all other summands. Together these specify
   exactly `epsilon_j tensor id_P` in the shared symmetric model, rather than an
   arbitrary map whose localization happens to be invertible.
4. Both strict arrows are levelwise quasi-isomorphisms in the paired `∀ n, QuasiIso ... ∧
   QuasiIso ...` clause. `e.hom = (localize R).map f` fixes the resolution isomorphism.
5. `beta` is the component localization of the left arrow, as fixed by its hom equation.
   `gamma` is the component isomorphism from the tensor Koszul model to
   `derivedEnd p N (quotient R s n)` evaluated on Q(M), i.e. restricted derived extension.
   `IsIso (epsilon ...)` and the equation `gamma.hom ≫ epsilon = beta.inv ≫ Q(a)`
   require the comparison to be the canonical localized span and canonical K-flat
   counit computation. No freely chosen derived identification is used.
6. The `∀ n m, n ≤ m → ...` equation gives compatibility with every quotient
   transition, including every composite and the identity transition, using the
   actual maps of `derivedScalarTower`.
7. `towerRoos` is exactly `roosF.obj (koszulTowerComplex R T)`; `towerRoosMap` is its
   actual functorial map. `coordinates` is `roosχ` followed by the biproduct braiding,
   so its coordinate order is (v,u) and its differential is (dv,-du-(1-s)v).
8. The coordinate equations on `uM` and `vP` require the product of the specified
   units as first component and zero shifted component. They hold in every degree,
   since q+1 runs over all integers. This specifies the strict augmentations themselves.
9. `left` and `right` are isomorphisms whose homs are Q of the two actual Roos span
   arrows. `sf.hom = left.inv ≫ right.hom` fixes the Roos span comparison.
10. `Q(uM) ≫ sf.hom = e.inv ≫ Q(vP)` is precisely the node's unit identity, with
    Lean's left-to-right categorical composition. The next clause composes this
    exact map with every existing `roosEval` and gives `e.inv ≫ Q(c_n)`.
    The final clause identifies that map with the normalized derived scalar unit
    followed by the canonical `epsilon` computation. Thus these are the actual
    quotient/completion units, not merely maps to isomorphic objects. The recorded
    strict Roos comparison identifies these specified strict augmentations with the
    derived-limit units. The same P, f, e and sf occur in all equations at all levels.

Dependency declarations used, after reading their full definitions/docstrings:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules` and its canonical abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, Q and Qh; no alternative derived category.
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`: `principalKoszulTower`,
  `globalSectionMultiplication`, `koszulTensorTower`, `koszulTowerComplex`,
  `koszulTowerComplexMap`, and `koszulRepresentativeAugmentation`.
- `Mathlib.Algebra.Homology.BifunctorShift`: direct-sum `CochainComplex.mapBifunctor`;
  used through the existing `curriedTensor.map₂CochainComplex` interface.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the recorded generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel` is publicly retained; its ordinary
  functor and universal derived counit are the universal pairs underlying p and N.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `restrictScalars`, used
  in the dependency's `restriction` and the normalized end functors.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosχ`, `roosP`, `roosEval`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatScalarTowerRealization`: `localize`, `ordinaryEnd`,
  `derivedEnd`, `ordinaryStep`, `derivedStep`, `epsilon`;
  `kflat_scalar_tower_realization` is the recorded proof tool for the transition/unit laws.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData`: `Modules`, `Presentation`,
  `Normalization`; its existing existence theorem is in
  `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.Algebra.Homology.KoszulRoosComparisonData`: existing `unitSection`, `B`,
  `quotient`, `summand`. No Models/Normalization assumption from that separate
  Koszul/Roos comparison is imposed; only its already defined tensor notations are reused.
- `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients`:
  `principalPowerRingQuotient`, `principalPowerRingProjection`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- Proof imports required by the item's plan are retained:
  `StrictRoosComparison.strictRoosComparison`,
  `KFlatResolutionIndependentCoefficients.exists_isKFlatResolutionIndependentCoefficients`,
  `FiniteFreeResolutionTensor.finiteFreeResolution_tensor`, and
  `KFlatTensorPreservesQuasiIsoIndependentCoefficients.kFlatTensorPreservesQuasiIsoIndependentCoefficients`.

The added statement-dependency ids are already landed: `def-sp-koszul-roos-comparison-data`,
`def-pe-principal-power-ring-quotients`, `def-weil-pbc-successive-derived-quotient-data`,
`def-pc-flat-sheaf-modules`. The new definition node
`def-sp-kflat-scalar-tower-constructions` records the seven existing scalar-tower
constructions, replacing the realization theorem in `stmt_deps`. The theorem
`lem-pe-kflat-scalar-tower-realization` remains in `proof_deps`. No dependency module
or additional Lean source is delivered.

Edge cases checked before writing:

- The zero complex and the zero coefficient sheaf give the same maps between zero objects.
- An invertible section is regular, gives zero quotient rings and contractible Koszul
  complexes, and hence both completion units are zero with the asserted span.
- The zero section is excluded by regularity except on the zero coefficient sheaf;
  the definitions still make sense there.
- On the one-point site with R=Z, s=2 and M=Z/2 in degree zero, M is not flat;
  a flat-term resolution P computes both H^-1 and H^0 of each derived quotient.
  The statement retains this case, so there is no silent replacement by ordinary
  tensoring M with the quotient.
- For R=Z/4 and s=2 the regularity hypothesis fails, as required: the cone has
  nonzero H^-1 and its quotient augmentation would not be a quasi-isomorphism.
- Unbounded P and M remain allowed. n=0 means power one, and n=m in the transition
  equation means the empty composite, so no positive level or identity case is lost.
- An empty site is allowed by EssentiallySmall, and all constructions reduce to the
  unique sheaf data. No Nonempty hypothesis was added.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "A single K-flat resolution compares principal Koszul and
  quotient tensor towers preserving strict Roos completion units"`: eight hits,
  all ordinary module-flatness criteria; none concerns the strict span and units.
- `msearch.py ... loogle '"Koszul", "QuasiIso"'`: zero hits.
- `msearch.py ... grep 'Koszul|KFlat|k_flat' Algebra/Homology`: one hit,
  Mathlib/Algebra/Homology/LocalCohomology.lean (ordinary Koszul homology commentary).
- `msearch.py ... leansearch "A single K-flat resolution compares strict Koszul and
  quotient towers with their completion units"`: eight hits (flatness, adic completion,
  and generic projective resolutions), no exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `koszulTensorTower|reductionTensorTower`: no upstream attachment; found the shared
  principal towers and earlier completion/reconstruction results. Those cover the
  comparison on a K-flat input or an abstract completion unit, but do not state
  this simultaneous span on an arbitrary M and a specified f:P→M, with the exact
  quotient units at all levels. Read `RegularQuotientCompletionUnit`,
  `DerivedCompleteKoszulReconstruction`, `PrincipalKoszulRoosPresentationComparison`,
  `KoszulRoosComparisonData`, and `KFlatScalarTowerRealization` to reuse their interfaces.
- `rg` for the proposed public names in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: no collision.

No statement dispute or source correction was needed. The module compiles cleanly with
`scompile.py` against the published live server build; both its sandbox and final module
checks passed. Final delivery preflight is run through `deliver2.py` as prescribed.


## Returned delivery repair

The independent review of immutable head `73aad002b2ef` returned one point, H2:
plain definitions used in the statement need a definition-node dependency, whereas
`lem-pe-kflat-scalar-tower-realization` states their properties. Repaired by adding
`def-sp-kflat-scalar-tower-constructions` with `existing: true` on all seven existing
definitions in `Sheaf.Algebra.Homology.KFlatScalarTowerRealization`, replacing the
theorem in the bridge's `stmt_deps` and retaining it in `proof_deps`. There is no
`.choose` of the theorem. The bridge Lean source, signature, statement, proof and
proof dependencies are unchanged. Compared with current main: its original
statement dependencies are all retained, and the reviewed added definition interfaces
are preserved. The wrapper rebases the delivery onto current main.

## New nodes

`def-sp-kflat-scalar-tower-constructions` records `ordinaryEnd`, `derivedEnd`,
`localize`, `ordinaryStep`, `derivedStep`, `computation`, and `epsilon`, all in
`SheafOfModules.KFlatScalarTower`. It attaches existing definitions rather than
constructing new objects. Its first clause is exactly the two extension/restriction
composites and the homotopy-quotient localization. Its second clause renders the
ordinary and derived unit/compositor composites in `ordinaryStep` and `derivedStep`.
Its third clause renders the counit, restriction-factorization and homotopy-composition
composite in `computation`, followed by transport using `e.inv` in `epsilon`.
Sources: Stacks 06YY and 0D6D and the current blueprint's reduction/completeness
paragraph. The data use `SuccessiveDerivedQuotient.Presentation` and `Normalization`
from `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData`, `ringedSiteModules`
from `Sheaf.CategoryTheory.RingedSiteModules`, and Mathlib's existing derived category.
No K-flatness condition is required to define these maps, and no isomorphism assertion
is added. Arbitrary coefficient maps, unbounded or zero complexes, an empty site,
and identity coefficient maps remain valid; these are composites of existing functors
and natural transformations on these cases.

New-node searches: LeanSearch for canonical scalar-extension/restriction endofunctors
and K-flat computation found eight ordinary scalar/restriction declarations;
LeanFinder for scalar transitions and counit computation found eight ordinary counit
or truncation declarations; neither supplies these sheaf-derived composites. Mathlib
grep for `KFlatScalarTower|ordinaryEnd|derivedEnd|ordinaryStep|derivedStep` in `Algebra`
returned zero hits. Project `rg` found the exact seven definitions in
`KFlatScalarTowerRealization.lean`, no counterpart in `WeilConjectures`; DAG declaration
search found only the theorem node's auxiliary declaration list, with no definition
node for this construction. `blueprint_refs.py search "scalar tower"` returned zero
nodes. Full search results are recorded in the new node's `mathlib_searches`.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

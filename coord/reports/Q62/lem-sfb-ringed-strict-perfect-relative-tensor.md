## Worker report

Module `Sheaf.Algebra.Homology.RingedSiteStrictPerfectRelativeTensor` states
`SheafOfModules.ringedSite_strictPerfect_relativeTensor`. Its only postponed proof is
that named theorem. Transparent helpers expose existing constructions: the module
category, restriction of scalars, the signed tensor total, and slice
smallness from `CostructuredArrow.essentiallySmall`, termwise restriction via
`overFunctor.mapHomologicalComplex`, and the recorded canonical-representative derived
restriction, with an explicit coefficient-category instance conversion. All helper
data are written in full; none selects data from an unspecified existence theorem.
The node statement and its accepted nine-step proof remain unchanged.

Hypotheses and their Lean counterparts:

- The site has independent object and morphism universes `u`, `v`; coefficients and
  modules have universe `r`. `[EssentiallySmall.{r} C]` is exactly smallness in the
  module universe. `J : GrothendieckTopology C` presents the given site, using the
  recorded site convention. No category-wide pullback assumption is introduced.
- `R A : Sheaf J CommRingCat.{r}` and `φ : R ⟶ A` are the given ring sheaves and map.
  `strictPerfectModules R`/`strictPerfectModules A` are the existing `ringedSiteModules` abbreviations.
- The four `HasDerivedCategory` instances supply the unbounded categories globally
  and on the one slice in question; their localization universes `wA`, `wR`, `wAU`,
  `wRU` are independent. No equality of site or localization universes is imposed.
- `I : Type i` and `points : I → GeometricMorphism (Type r) (Sheaf J (Type r))`
  specify a set-indexed family of points. The adjunction makes inverse image preserve
  all small colimits, and `leftExact` gives finite limits. `hpoints` is joint
  reflection of isomorphisms on sheaves of sets. There is no `Nonempty I`.
- `stalks j : RingedSitePoint R (points j)` is the already recorded normalized ring
  and module inverse image, including all operation equations. Such presentations
  exist for every point (`RingedSitePoint.nonempty`); supplying one neither changes
  the point nor strengthens the hypothesis. All presentations are allowed.
- `M`, `P`, `U`, `L` have exactly the specified global complex, derived object, slice
  object and slice complex types. Cochains use the recorded `CochainComplex ... ℤ`.
- `a b c d : ℤ`, `hab`, `hcd`, `hM`, `hL` express the ordered intervals and zero terms
  outside them. `IsZero` is zero in the module-sheaf category, not a chosen equality.
- `hflat` is ordinary `Module.Flat` over `(stalks j).ring` of the stalk of the scalar
  restriction of each `M.X q`. The action is fixed by `RingedSitePoint.moduleSMul`
  and the given ring-sheaf map; no unrelated module structure is supplied.
- `hfree` gives a rank `k` and split inclusion/retraction into
  `SheafOfModules.free (ULift.{r} (Fin k))`, with `ι ≫ π = 𝟙`. This includes rank zero
  and every finite free summand. `ULift` places the finite index in the module universe.
- `eL : strictPerfectDerivedSlice A U P ≅ DerivedCategory.Q.obj L` is the prescribed
  local derived isomorphism. The helper is the recorded derived restriction, not an
  independently chosen local lift. The zero-preservation proof used to restrict
  complexes is the existing `CategoryTheory.module_overFunctor_preservesZero`.

Conclusion clauses:

1. `∃ T, T = strictPerfectTotalTensor (A.over U) L (strictPerfectSliceComplex ... M)`
   fixes the actual signed direct-sum total tensor. The helper applies the recorded
   `CochainComplex.mapBifunctor` to the canonical `curriedTensor`, with
   differential `d_L tensor 1 + (-1)^p 1 tensor d_M`.
2. The first `Nonempty (... ≅ Q.obj T)` is the isomorphism in `D(A|U)` from the
   restriction of `siteDerivedTensorIndependentCoefficients J A` applied to `(P,QM)`.
3. For each degree, the existential `k,q,s,N` and `T.X n ≅ ∐ N` give a finite direct
   sum of summands. Each `N j` has a split inclusion/retraction into the finite
   coproduct indexed by `Fin (s j)` of `(M.X (q j)).over U`. This is the full
   finite-sum-of-direct-summands assertion, not merely finite generation.
4. `n < a+c ∨ b+d < n → IsZero (T.X n)` is the exact support interval.
5. `IsFlatOnSite (J := J.over U) (R := R.over U)` applied to the actual scalar
   restriction is termwise relative flatness. The next conjunct is
   `IsKFlatIndependentCoefficients` of the termwise scalar restriction of T.
6. The following `Nonempty` is the scalar-restricted local derived isomorphism
   in `D(R|U)`, with RHS `Q` of the same scalar-restricted T. Restriction of the ring
   map is exactly `(J.overPullback CommRingCat U).map φ`.
7. For every `F : strictPerfectModules R`, the last derived isomorphism identifies the slice
   restriction of `Res(H) tensor_R^L Q(F[0])` with `Q(T_R tensor_{R|U} F|U[0])`.
   Degree-zero complexes are `HomologicalComplex.single _ (.up ℤ) 0` (integer
   cochains, not the natural-number `single₀`). The same clause asserts `IsZero`
   of `DerivedCategory.homologyFunctor ... n` on that left side outside `[a+c,b+d]`.
8. No coherence, Noetherian, compactness, geometric map between sites, proper-support,
   or flatness of R→A assumption appears. Geometric morphisms here are exactly the
   specified *points* of the statement, not an added map hypothesis.

Dependency declarations used (all read at their actual definitions/docstrings):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; the
  Grothendieck-topology presentation has the same sheaves. The size convention has
  no declaration and is rendered by explicit universes.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; `DerivedCategory.HomologySequence`: `homologyFunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`, using the
  actual sheafified tensor functor and exactness.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, applied
  to `CategoryTheory.MonoidalCategory.curriedTensor` with
  `SheafOfModules.monoidalCategory` in `strictPerfectTotalTensor`. This is the
  construction owned by `def-pc-tensor-complex-sheaves`. The category helper
  `strictPerfectModules` uses `ringedSiteModules`, owned by
  `def-weil-sheaf-of-modules-category`. No fixed-tensor theorem is a statement dependency.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `overFunctor`,
  `over`; `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `restrictScalars`,
  through the transparent item helper `strictPerfectRestrictScalars`, owned by
  `def-pc-sheaf-restrict-scalars`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `siteDerivedTensorIndependentCoefficients`, the published derived tensor.
- `Sheaf.CategoryTheory.Sites.RingedSitePoint`: `CategoryTheory.RingedSitePoint`.
  This landed node is added to statement dependencies for the stalk hypothesis.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `ringedSiteDerivedRestrictionOfUniverses`, added to statement dependencies.
- `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` is a plain proof
  import only: its finite-limit and finite-colimit preservation instances apply
  definitionally to `strictPerfectRestrictScalars`. The additive instance is
  Mathlib's for `SheafOfModules.restrictScalars`. It is not a statement dependency.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: `free`; finite coproducts and
  split arrows express the notions directly rather than adding private predicates.

All recorded proof dependency modules are imported with plain `import` when they
are not already public statement imports: `SliceRestrictionFlat`,
`BoundedAboveFlatSheafKFlat`, `SiteOneSidedTensorNormalization`,
`RingedSiteRestrictionKFlat`, `LocalizedSiteTensorRestriction`, and
`RestrictedKFlatTensorIdentification`. The sheaf tensor
interface `CochainTensorUniverses` is public. The proof dependency
`lem-sfb-ringed-site-conservative-flatness` currently has no recorded Lean declaration;
there is therefore no module to import for it. It is used only by the future proof,
not assumed in place of the stalk-flatness hypothesis and not restated in this delivery.

Edge cases checked before writing: M=0, L=0, rank-zero free summands; a=b and c=d
(the bound is then the sum degree); arbitrary negative endpoints; degrees just outside
both ends; R=A and identity scalars; R=Z, A=Z/2 (the relative flatness condition must
exclude a nonzero Z/2 term, so no A-flatness can accidentally replace it); A=0;
empty slice; empty conservative point family on a degenerate topos. Empty finite
coproducts and zero stalk modules remain allowed. Infinite site or point index sets
are not replaced by finite ones. A stalk presentation is normalized for every operation,
not a noncanonical scalar action. No mathematical statement correction is needed.

Searches:

- `msearch.py ... leanfinder "A bounded finite projective complex tensor a bounded
  relatively flat complex on a ringed site computes derived tensor with summed Tor
  amplitude"`: eight hits, chiefly `HomologicalComplex.HasGoodTensor₁₂/₂₃` and
  `CategoryTheory.Tor`; no ringed-site statement.
- `msearch.py ... loogle "CochainComplex.mapBifunctor, Module.Flat"`: zero hits.
- `msearch.py ... grep "KFlat|StrictlyPerfect|strictlyPerfect"`: zero hits.
- Additional `msearch` LeanSearch/LeanFinder searches for variable-ring module stalks
  found topological stalks and `PresheafOfModules.colimitFunctor`, not this theorem.
  A DAG-wide definition census then found the usable existing `def-sfb-ringed-site-point`;
  the draft filtered-colimit helper was removed, and no new node is delivered.
- `msearch ... grep "sitePointModuleFiber|colimitFunctor|Point.*SheafOfModules"
  Algebra/Category/ModuleCat`: five hits, colimitFunctor and free sheaf documentation.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for strict-perfect relative tensor
  found scheme-only `StrictPerfectRelativeTensorModel`, `StrictPerfectTensorRelativeTorBound`
  and related scheme specializations. None allows an arbitrary ringed site and R→A.
- Exact node-id search in `lean/WeilConjectures` found no existing declaration.
  `rg` for the delivered full names in both library roots and `dag/lean_names_upstream.json`
  found none. `blueprint_refs.py search "point module fiber"` found zero blueprint nodes.

Sources read locally: Stacks sites-cohomology.tex 06YQ, 06YU, 0E8K and 0DEN;
sites-modules.tex 05VC; spaces-perfect.tex 0DKJ, especially the finite local tensor
calculation. Also read the current latest blueprint unit and direct-image proof of
`sk-thm-sf-ctf-stability`. The generic node does not impose the unrelated finiteness
hypotheses of the proper-direct-image theorem in 0DKJ.

## Second reading by Q62

The dispatcher requests direct delivery and forbids starting another agent; the
maintainer provides the independent review. This section records my own clause-by-clause
rereading, not an independent-agent claim. It found and repaired three interface
mistakes during compilation: natural-number `single₀` was replaced by the integer
single complex; scalar-map slice restriction uses the actual `overPullback.map`;
and commutative-ring forgetting and slice localization instances now use explicit
coefficient universes. The final statement retains all hypotheses and seven
conclusion groups above. The only sorry is the named main theorem. No new definition
nodes, dependency-node changes or statement correction are delivered.


## Returned delivery repair (H2)

The return on immutable head `692466c22615` requested removal of two theorem
statement dependencies whose modules supplied only ordinary definitions. Removed
`lem-weil-pbc-kflat-fixed-tensor-triangulated` and
`lem-pe-restricted-kflat-tensor-identification` from `stmt_deps`.
The module no longer imports the fixed-tensor theorem module or opens its namespace.
It uses `strictPerfectModules`, `strictPerfectTotalTensor` and
`strictPerfectRestrictScalars`, transparent item-module abbreviations of exactly
`ringedSiteModules`, `CochainComplex.mapBifunctor` of canonical `curriedTensor`, and
`SheafOfModules.restrictScalars (sheafCompose.map φ)`. Their docstrings cite the
three owning definition nodes, which were already statement dependencies. Two
instance aliases apply the existing finite-limit and finite-colimit preservation
proofs to the new scalar-restriction notation; their bodies are the recorded proofs,
not new postponed assertions. They introduce no construction or hypothesis.
`RestrictedKFlatTensorIdentification` is retained as a plain proof import for its
exactness instances, as authorized in the return. The legitimate derived tensor
from `lem-weil-pbc-site-derived-tensor-descent` is retained.

Compared the retained sandbox node with the current main checkout: the mathematical
statement, proof, proof dependencies and all other non-Lean fields agree, except for
the authorized additional statement dependencies for points and derived restriction.
No dependency record is modified. Reread all hypotheses and conclusions after the
replacement: only definitionally identical notation changed; all bounds, arbitrary
universes, rank-zero cases, point hypotheses, scalar and slice restrictions and the
universal test-module clause remain. No statement correction is needed.

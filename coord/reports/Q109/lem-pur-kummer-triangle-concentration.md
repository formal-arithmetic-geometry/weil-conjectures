## Worker report

The module `Sheaf.Paper.PurityKummerTriangleConcentration` states
`WeilConjectures.PurityFiniteSetting.kummer_triangle_concentration`, with one postponed
proof and no postponed data. The auxiliary declarations name the existing module-sheaf category, the two actual
derived images, their restriction and boundary maps, canonical unit comparisons,
the associated-module realization, and the recorded constructibility/Tor predicates.
The generic `orientationTensorUnitIso` constructs the induced tensor isomorphism;
`OrientationTensorUnitConclusions` transparently spells out its existence and exact
normalization for a specified family of test objects. They introduce no alternative geometric or
coefficient construction. The natural-language statement and accepted split are unchanged.

Hypotheses, in order:

- `P : PurityFiniteSetting.{u}` is the recorded finite-field and coefficient datum:
  algebraic closure k of the finite field, prime ell different from its characteristic,
  finite coefficient extension E and A=O_E/(varpi_E^n), with `P.level_pos` giving n>=1.
  `P.Coefficient` is precisely the prescribed universe lift of that quotient.
- `h : P.ramificationIndex ∣ P.level` is e(E/Q_ell) dividing n.
- `Y`, its structure map `a : Y ⟶ Spec (CommRingCat.of P.field.k)`, and the classes
  `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]` mean separated finite type
  over k. No nonemptiness, smoothness, connectedness or flatness is imposed.
- `P.kummerImage h Y false` is P=Rp_*A_X(1)[0]; the value at `true` is
  Q=Rpi_*A_U(1)[0], with X, U, p, j, pi from the recorded affine-line datum.
- Arbitrary `B`, `b`, `δ` and `hT` give exactly the distinguished unrotated triangle
  B -> P -> Q -> B[1]. Its second arrow is fixed to `P.kummerRestriction h Y`:
  Rp_* of the canonical open unit, followed by the inverse of the recorded canonical
  `finiteDirectImageComposition`. Thus no arbitrary restriction is substituted.

Conclusions, in order:

- `IsIso (P.relativeUnit h (lineProjection Y) true)` is the specified unit isomorphism.
- `IsIso ((DerivedCategory.homologyFunctor ... 0).map (P.kummerRestriction h Y))`
  is precisely invertibility of H0(r).
- The two quantified `IsZero` clauses say P has no cohomology outside zero and Q
  has none outside zero and one. Their index is all integers, including negative ones.
- `IsIso (P.kummerGenerator h Y a)` is invertibility of gamma. That recorded map takes
  1 to the edge of the actual coordinate Kummer class, not an unspecified generator.
- `IsIso (DerivedCategory.HomologySequence.δ (Triangle.mk ...) 1 2)` asserts
  invertibility of the connecting map of this very triangle, with no rotation or sign
  change: H1(Q) -> H2(B).
- `∀ m, m ≠ 2 → IsZero ...` is the complete B concentration assertion.
- `hC` is concentration of C=B[2] in degree zero. The existential `θ` is an actual
  derived isomorphism A_Y[0] -> C, not merely separate homology isomorphisms.
- The first equality after `θ` says the good-truncation epsilon induces identity on H0,
  using the canonical single-complex comparison.
- The next equality fixes `θ.hom` to single(gamma followed by delta followed by the
  inverse H0(B[2])=H2(B) shift comparison) followed by epsilon inverse.
- The following H0 equality explicitly states H0(theta)=delta gamma under both the
  degree-zero single comparison and H0(B[2])=H2(B). This retains the actual boundary
  normalization, even for a triangle with different outer arrows.
- `Nonempty (P.constant Y ≅ H0(C))`, together with hC, is the stated globally constant
  lisse rank-one cohomology and absence of other cohomology: the constant value is
  exactly the free rank-one coefficient module, not only a fibre-rank assertion.
- `Scheme.intrinsicFiniteTorsionConstructible ...` on the canonical associated-module
  realization of C states the recorded intrinsic bounded constructibility condition.
  The realization is the existing additive exact equivalence for the same constant ring
  sheaf and the same quotient coefficient ring.
- `ProEtale.DerivedCategory.constructibleFiniteTor ... C` gives D^b_ctf membership in the
  native fixed-ModuleCat presentation, as exposed by the recorded FiniteTorAmplitudeSites.
- `ProEtale.DerivedCategory.torAmplitudeIn ... 0 0 C` is exactly the Tor interval [0,0].
- `OrientationTensorUnitConclusions (singleFunctor ... 0).obj θ
  (P.kummerDerivedUnit h Y)` unfolds to: for every module sheaf M,
  `∃ e : C ⊗ M[0] ≅ M[0], e = orientationTensorUnitIso θ η M[0]`.
  This states the requested derived tensor isomorphism. Its map is theta inverse
  tensored with M[0], the canonical constant-to-derived-unit identification tensored
  with M[0], then the left unitor. The helper is fully defined in the same module;
  no mathematical assertion is hidden or postponed in it.
  The global derived monoidal tensor is definitionally `ProEtale.derivedTensor`.
  No flatness condition on M is added.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its field and coefficient data,
  `Ring`, `Coefficient`, `constant`, `twist`, `derivedSheaf`.
- `Sheaf.Paper.PurityAffineLineDatum`: `Line`, `Punctured`, `openImmersion`,
  `lineProjection`, `puncturedProjection`, `coordinateKummer`.
- `Sheaf.Paper.PurityRelativeKummer`: `relativeUnit`, `kummerGenerator`, `relative_kummer`.
  The generator definition is H0 of the derived adjunct of coordinateKummer followed by
  the canonical shift comparison.
- `Sheaf.Paper.FiniteDirectImageComposition`: `ProEtale.finiteDirectImageComposition`,
  the actual unbounded direct-image compositor with the recorded unit normalization.
- `Sheaf.Paper.SfDerivedDirectImage`: the finite right-derived-image convention
  (`sfFiniteDerivedDirectImage` in the integral tower); here the entire unbounded finite
  image is the canonical `ProEtale.lowerStar ... .rightDerivedFunctor` also exposed by
  the compositor module. There is no integral tower in this item's statement.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules` and its
  fixed-coefficient realization; `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicRealization` and its exact equivalence. Fixed-ModuleCat
  sheaves are the existing presentation of the same ordinary constant-ring modules.
- Mathlib `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`,
  `HomologySequence.δ` and `exact₁/₂/₃`, `singleFunctor`,
  `singleFunctorCompHomologyFunctorIso`, and `homologyFunctor.shiftIso`;
  `Pretriangulated.Triangle.mk`, `distTriang`, `DerivedCategory.TStructure.t`.
- `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization`:
  `DerivedCategory.goodTruncationNormalization`, its roof formula and normalization.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the exposed native fixed-ModuleCat
  `ProEtale.DerivedCategory.constructibleFiniteTor` and `torAmplitudeIn`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `ProEtale.derivedTensor`; `WeilConjectures.SixFunctors.ProEtale.Comparison`:
  `comparisonUpperStarUnitIso`; `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `singleFunctorObjUnitIso` and the ordinary monoidal left unitor.
- Proof-only imports include the recorded independent-coefficient K-flat and sheaf tensor
  interfaces, ring-sheaf Grothendieck property and direct-image left exactness. The
  recorded negative-derived-vanishing and total-complex interfaces are already imported
  through the published relative-Kummer and tensor modules. No proof dependency import
  is omitted for a cycle.

Edge cases checked: the empty scheme is allowed (no rank or nonemptiness hypothesis);
n=1 and every positive n divisible by e are included; ell=2 is included when prime to the
base characteristic. Vanishing includes negative indices, the exceptional index m=2 for
B, and m=0,1 for Q. The test sheaf M ranges over all modules, including zero and nonflat
residue modules when n>1. The normalization uses the actual unrotated connecting arrow,
so a changed identification of B changes theta accordingly. Site objects remain in
u+1, morphisms in u, with coefficient modules in u+1; no extra universe equality is added.

Searches: the item's sandbox searches.jsonl records LeanSearch queries about the relative
Kummer restriction triangle and degree-two concentration (no matching theorem), Loogle
queries `"DerivedCategory", "singleFunctor"` (the generic single-complex interfaces),
and LeanFinder queries about affine/punctured-line concentration and the tensor unit
(generic complexes and Ext lemmas only). The additional Loogle query
`DerivedCategory.singleFunctor, IsIso, Triangle` returned no hits because IsIso was not
recognized by that service; the earlier successful singleFunctor query is retained.
Mathlib grep for `kummer.*[Tt]riangle|[Tt]riangle.*[Kk]ummer|[Cc]oncentration` in
Algebra/Homology returned zero hits. Searches of both `lean/WeilConjectures` and
`lean/Sheaf` for those patterns and this node id found no existing declaration of this
statement: only a consumer's proof docstring mentions KummerTriangleConcentration.
The recorded relative-Kummer statement computes P and Q but does not state the arbitrary
restriction triangle, boundary-normalized theta, or tensor-unit conclusion.

No new nodes, dependency repairs, statement corrections or disputed statements are needed.
Every theorem proof in this delivery is `sorry`, as required for stage 2.

Validation: scompile.py compiled the complete delivered module and its sandbox form
cleanly (9.7 s and 10.0 s respectively), with no errors or warnings. Earlier drafts
spent excessive kernel reduction on a specialized tensor normalization. Writing that
same normalization as the transparent generic OrientationTensorUnitConclusions
removes repeated expansion while preserving exactly the degree-zero test family.
The complete theorem, rather than a reduced probe, was compiled.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

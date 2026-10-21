## Worker report

The module `Sheaf.Paper.ClosedIdentityOpenHomNormalization` states
`AlgebraicGeometry.ProEtale.closedIdentityOpenHomNormalization`, with `sorry`.
It defines two canonical identity-open compact-support identifications and a
transparent predicate containing the complete conclusion. No other theorem or
axiom is introduced. All definitions contain actual data; no data is selected
from a mere existence assertion. The item's node changes only in `lean`.

Hypotheses, in order:

- The fixed global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`;
  the base field is literally `D.k`, including its fixed algebraic closure structure.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. The positive level is `n`, `hn : 1 ≤ n`.
  Inside the predicate, `A` is `ULift.{u+1,u} (Padic.coefficientExtensionRing l E n)`.
  This is the existing quotient by the existing chosen uniformizer power. The
  lift only puts the scalar ring in the universe of module values on the sites;
  it does not substitute a different coefficient theory. Its finiteness is supplied
  by `Padic.finite_coefficientExtensionRing`, rather than an extra hypothesis.
- The separated finite-type k-schemes have structure maps `aZ`, `aP` to `Spec (.of D.k)`.
  Each has `[LocallyOfFiniteType]`, `[QuasiCompact]`, `[IsSeparated]`.
  The closed immersion is `i : Z ⟶ P`, `[IsClosedImmersion i]`, and its k-linearity
  is `_hi : i ≫ aP = aZ`. No properness, dimension bound or quasi-compactness of
  either underlying space is additionally assumed.
- Ordinary derived module categories are `DerivedCategory (Sheaf ... C)` with
  `C := ModuleCat.{u+1} A`; the sites are `T.smallEtaleTopology` and
  `Scheme.ProEt.topology T`. This is the existing fixed-scalar presentation of
  the ordinary constant coefficient categories, not completed/adic coefficients.
- In the predicate, `F` and `Q` are the actual ordinary etale and pro-etale
  `lowerStar` right derived functors. `I := F.rightAdjoint` is the closed-ambient
  right adjoint and `β := Adjunction.ofIsLeftAdjoint F` its specified adjunction.
  `SZ`, `SP` are exact `comparisonUpperStar.mapDerivedCategory`, `UP` is
  `comparisonLowerStar.rightDerivedFunctor`, and `η` is the unit of the existing
  `derivedComparisonAdjunction`. `J := UP ⋙ I ⋙ SZ` is exactly S_Z I U_P.
- `c := Compactification.ofIsProper i` is exactly (id_Z,i). `e` and `q` remove
  its identity etale and pro-etale extension by zero via `leftAdjointIdIso`,
  termwise descent, and `Functor.leftUnitor`. They are not free isomorphism inputs.
  The right-adjoint comparison `r := (adjc.ofNatIsoLeft e).rightAdjointUniq β`
  is the counit-compatible adjunction comparison stipulated in the node.
- `H : DerivedCategory.Plus ...` and `hIH : t.plus (I.obj H.obj)` are precisely
  the two bounded-below assumptions. There is no assumption that I preserves
  boundedness on other objects, and no ambient pro-etale exceptional adjunction.

Clauses, in order in `closedIdentityOpenHomNormalizationProperty`:

1. `t.plus (I.obj (UP.obj (SP.obj H.obj)))` states boundedness of IU_PS_PH.
2. `IsIso (SZ.map (I.map (η.app H.obj)))` states invertibility of the actual alpha_H,
   not existence of an unrelated isomorphism.
3. The existential `hJ` states boundedness of JS_PH. The retained
   `Scheme.FixedEtaleOriginWitness` has `W.complex = ⟨I.obj H.obj,hIH⟩` and
   `HEq W.iso.hom (SZ.map (I.map (η.app H.obj)))`. The heterogeneous equality is
   only needed because the witness's source is indexed by its retained complex;
   together these equations specify exactly (IH,alpha_H), not just some origin.
4. For every `L : DerivedCategory.Plus ...`,
   `q.inv.app (SZ.obj L.obj) ≫ (compactSupportSiteComparison A c).hom.app L ≫
   SP.map (e.hom.app L.obj) = (fixedDirectImageComparisonIso A i).inv.app L`
   identifies the canonical compact-support comparison with delta_L inverse after
   the canonical identity-open identifications. `fixedDirectImageComparisonIso`
   is explicitly the named `fixedComparisonDirectImageMatePlus` transported by
   the specified D+ inclusion compatibility isomorphisms (read its definition).
5. For every `g : Q.obj (SZ.obj L.obj) ⟶ SP.obj H.obj`, the left side evaluates
   the actual `specifiedExceptionalHomEquiv` at the literal identity witness
   `⟨L,Iso.refl _⟩`. It precomposes g with `q.hom` to put it in the compact-support
   source, then postcomposes the output with `SZ.map (r.hom.app _)` to make the
   stipulated etale right-adjoint identification. Its equality with
   `SZ.map ((β.homEquiv _ _) (η.app (F.obj L.obj) ≫
   UP.map ((fixedDirectImageComparisonIso A i).hom.app L ≫ g)))`
   retains all four requested factors: delta precomposition; the actual comparison
   unit formula; beta; and exact SZ on morphisms. Equality for every g specifies
   the bijection as a function, rather than only asserting its existence.
   The `specifiedExceptionalHomEquiv` value already has an Equiv type, so
   bijectivity is retained. Both S_ZL and S_PH are passed using the existing
   `siteComparisonDerivedPullbackPlus`, retaining their D+ typing.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, `coefficientExtensionIdeal`, and the chosen
  `coefficientExtensionUniformizer`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
  The scheme-properties dependency is a convention collecting these Mathlib notions.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient import:
  ordinary derived categories, `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the continuous-function coefficient
  sheaf and the existing fixed-scalar realization. The categories used here are
  the fixed ModuleCat presentation used by all the named comparison/adjunction APIs.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`,
  reusing `comparisonAdjunction`, `comparisonUpperStar` and `comparisonLowerStar`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`: the specified invertible unit;
  its upstream `FiniteCoefficient.Derived.Comparison` supplies
  `derivedComparisonAdjunction` and `isIso_derivedComparisonAdjunction_unit_app`.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- The exceptional-inverse-image dependency's recorded coefficient module reexports
  `sfFiniteExceptionalAt`; its owning `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`
  is imported directly, and the specified class-Hom module imports it as well.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`:
  `specifiedExceptionalHomEquiv`, with `specifiedExceptionalEtale_boundedBelow`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: `Scheme.FixedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison` (also the construction node's existing declaration).
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus` and its named counit normalization;
  `FiniteComparisonClassAdjunction.fixedDirectImageComparisonIso` transports this
  exact map to the ambient categories. No duplicate comparison is defined here.
- Proof-only imports include `BoundaryExceptionalComparisonData.homTransport`,
  `ProEtaleExtensionZeroComparison.openImmersionLowerShriekComparison_coherence`,
  `exists_topologicalKrullDim_le`, `proper_basic`, and the ordinary etale direct image.

Edge cases checked before writing: H=0, L=0, the empty source or empty target,
identity i, and the smallest level n=1. The fixed finite quotient includes residue
coefficients; no nonzero object or positive-dimension hypothesis is added. For an
empty source the finite dimension bound is taken as 0 in the natural-language proof.
The construction uses no purity coefficient setting, primitive root of unity,
constructibility, finite Tor amplitude, or uniform bound for I as an extra premise.
Universes are all explicitly bound, `autoImplicit` is false, and the site universes
are not forced equal. All conclusions are in the ordinary derived category.

Searches (2026-10-21 UTC):

- `msearch.py ... leanfinder`: "The relative exceptional Hom bijection for a closed
  immersion normalized at the identity open equals the canonical site comparison
  mate followed by the comparison adjunction and exceptional adjunction".
  Eight generic sheaf adjunction and scheme closed-immersion hits; no match.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Adjunction.rightAdjointUniq`. One hit,
  `CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` in
  `Mathlib.CategoryTheory.Adjunction.Unique`; useful generic normalization,
  not the geometric statement.
- `msearch.py ... grep`: `homEquiv_normalized|compactSupportSiteComparison|
  specifiedExceptionalHomEquiv` in `CategoryTheory`: zero hits.
- `msearch.py ... leansearch`: "The specified relative exceptional Hom equivalence
  for a closed immersion is the direct image comparison mate then comparison
  adjunction then exceptional adjunction then exact pullback".
  Eight generic closed-immersion, restriction and exponential-comparison hits;
  none states this result.
- `rg` in the exact live `lean/WeilConjectures` and `lean/Sheaf` trees for the node id:
  zero hits. `rg` for `closedIdentity|IdentityOpen|identityOpen|closed.*normalization`
  found different base-change identity-open and support comparisons. Reading
  `ClosedSupportExceptionalComparison` showed its `closedSupportCompactIso` requires
  a chosen complementary open and has support-functor endpoints, so it cannot be
  reused for the present ordinary direct-image normalization. Its identity extension
  construction confirms the canonical adjunction convention used here. The existing
  class-Hom definition and mate were reused instead of copied.

Validation: scompile.py compiled both sandbox and library module modes cleanly
(6.9 s / 6.4 s initially). Only the requested theorem is postponed. No node fault,
statement correction, new node, or dependency-record repair is required.

## Second reading by Q04

The dispatcher explicitly forbids starting another agent and assigns independent
review to the maintainer; this section records the worker's own second pass, not a
claim of independent review. I reread the full node, the source's displayed chain,
and the completed file. The input q.hom goes from compact support to Q, whereas
normalizing the comparison uses q.inv; the etale normalization uses e.hom. The
right-adjoint comparison r goes from the specified compactification adjoint to I,
so the Hom output is postcomposed with SZ(r), as required. The comparison unit is
on FL, and the order in Lean is eta_FL followed by UP(delta_L ≫ g), matching the
source's composition convention. The origin witness retains IH and the actual
alpha. No mismatch, added hypothesis or missing clause was found. The final pass
also checked no file-local notation or instance, no data sorry, no extra theorem,
and that the node's statement is unchanged.

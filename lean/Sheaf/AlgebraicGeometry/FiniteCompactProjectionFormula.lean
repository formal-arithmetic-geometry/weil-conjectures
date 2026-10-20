/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.Paper.ExchangeProjection
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Finite-coefficient compact-support projection formula
Source: Weil blueprint, main-20261015, sec-six-functors-basics/sk-thm-sf-pf-finite,
`lem-weil-finite-compact-projection-formula.md`
(blueprint: lem-weil-finite-compact-projection-formula).
Both maps are the published natural transformations of bifunctors, so naturality in
both arguments is retained. The compactification is arbitrary. The pro-etale clause
retains the recorded origin witnesses and evaluates the published fixed-ring map on
their objects through the canonical inverse coefficient-realization equivalence.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Finiteness of the actual positive-level quotient coefficient ring.
Source: blueprint finite coefficient convention; Serre, Local Fields, II, section 2
(blueprint: lem-weil-finite-compact-projection-formula). -/
noncomputable instance finiteCompactProjectionCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- The finite quotient coefficient ring is regarded as discrete.
Source: blueprint finite coefficient convention
(blueprint: lem-weil-finite-compact-projection-formula). -/
instance finiteCompactProjectionCoefficient_topology
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥

/-- Discreteness of the coefficient convention.
Source: blueprint finite coefficient convention
(blueprint: lem-weil-finite-compact-projection-formula). -/
instance finiteCompactProjectionCoefficient_discrete
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := ⟨rfl⟩

-- Prioritize finiteness when checking noetherianity of the quotient coefficients.
attribute [local instance 2000] isNoetherian_of_finite

private theorem finiteCompactProjection_etale
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  rw [projectionMapOfCompactification_app_app]
  infer_instance

private noncomputable def finiteCompactProjection_originIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus T A)
    (w : Scheme.EtaleOriginWitness T A Kp) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj w.L.obj ≅
      (ProEtale.finiteCoefficientRealization T A).mapDerivedCategory.asEquivalence.inverse.obj
        Kp.obj := by
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := ProEtale.finiteCoefficientRealization T A
  let e := R.mapDerivedCategory.asEquivalence
  exact e.unitIso.app _ ≪≫ e.inverse.mapIso
    ((Functor.mapDerivedCategoryCompIso C R).symm.app w.L.obj ≪≫
      _root_.DerivedCategory.Plus.ι.mapIso w.alpha)

private theorem finiteCompactProjection_proEtale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y)
    (hK : _root_.DerivedCategory.TStructure.t.bounded K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L)
    (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X A)
    (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y A)
    (wx : Scheme.EtaleOriginWitness X A Kp)
    (wy : Scheme.EtaleOriginWitness Y A Lp) (hx : wx.L.obj ≅ K) (hy : wy.L.obj ≅ L) :
    IsIso (((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((ProEtale.finiteCoefficientRealization X A).mapDerivedCategory.asEquivalence.inverse.obj
        Kp.obj)).app
      ((ProEtale.finiteCoefficientRealization Y A).mapDerivedCategory.asEquivalence.inverse.obj
        Lp.obj)) := by
  let Cx := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let Cy := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let ex := Cx.mapDerivedCategory.mapIso hx.symm ≪≫
    finiteCompactProjection_originIso A X Kp wx
  let ey := Cy.mapDerivedCategory.mapIso hy.symm ≪≫
    finiteCompactProjection_originIso A Y Lp wy
  obtain ⟨a, b, hLt⟩ := hTor
  have hLt' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y a b L := by
    intro F
    rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2
        (fun q hq ↦ hLt F q (.inl hq)),
      (_root_.DerivedCategory.isLE_iff _ b).2 (fun q hq ↦ hLt F q (.inr hq))⟩
  have hM :=
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hK
  have hML := plus_derivedTensor_leftDerivedUpperStar c.g hM hLt'
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  exact ProEtale.hasProjectionFormulaOfCompactification_of_comparison
    (A := ModuleCat.{u + 1} A) (K₀ := K) (L₀ := L) c ex ey hK hML inferInstance

-- Keep the quotient Ring instance aligned with the generic CommRing helpers.
attribute [local instance 2000] CommRing.toRing

attribute [local irreducible] projectionMapOfCompactification
  ProEtale.projectionMapOfCompactification

/-- The finite-coefficient projection formula on the small etale site and on every
specified pro-etale realization. No Tor-amplitude hypothesis is imposed on `K`, and
neither scheme is required to be separated over the field. The only separatedness
hypothesis is on `f`. The bound `n ≥ 1` supplies finiteness by the recorded theorem.
The witnesses may be arbitrary: their representatives are identified with `K,L` by
`hx,hy`, and the conclusion uses the actual pro-etale projection transformation.
Source: Weil blueprint, main-20261015, sec-six-functors-basics/sk-thm-sf-pf-finite,
`lem-weil-finite-compact-projection-formula.md`
(blueprint: lem-weil-finite-compact-projection-formula).
Proof, following the nine steps of the DAG node:

1. Work first with ordinary constant-$A$ modules on the small etale sites. The coefficient ring is
finite and commutative by [def-weil-l-adic-coefficient-extension]. A field is Noetherian (its only
ideals are zero and the unit ideal). The locally-finite-type assertion in [pqf-def-locnoeth],
applied to the structure maps, makes $X,Y$ locally Noetherian. Their finite-type structure maps
are quasi-compact by [def-weil-finite-type-morphism], so a finite subcover of an affine Noetherian
cover makes them Noetherian. Choose an arbitrary compactification $c=(j,p)$ by
[sk-thm-nagata-sketch-noetherian]. Its proper $p$ is of finite type and quasi-compact by
[def-weil-proper-morphism] and [def-weil-finite-type-morphism]; the same argument over a finite
Noetherian affine cover of $Y$ makes $\overline X$ Noetherian. Its open $j$ is quasi-compact:
$\overline X$ is quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated], and $X$ and
each affine open $V\subset\overline X$ are quasi-compact opens, so their intersection is
quasi-compact by [pqf-lem-qs-intersection-qc]. This intersection is the inverse image $j^{-1}V$.
On $D^+$ the coherent comparisons [lem-amb-etale-compact-comparisons] allow us to compute $Rf_!$
as the candidate $Rp_*j_!$ of [def-amb-etale-compact-support]. Define the etale compact projection
map using this computation as $Rp_*(\gamma)\circ\pi_{p;j_!K,L}$, where $\pi$ is precisely the
counit-tensor-identity mate of [def-kun-projection-formula-map] and
$\gamma:j_!K\otimes^Lp^{-1}L\to j_!(K\otimes^Lf^{-1}L)$ is the open tensor comparison constructed
in step 3. We prove invertibility for every choice $c$; thus computing the compact-support
transformation using any chosen compactification, or transporting its source and target along the
coherent functor comparisons, gives the asserted invertibility. No equality of transformations for
different compactifications is being assumed from mere independence of the functors.

2. Check all bounded-below domains before base change. Choose integers $u\leq v$ outside which the
cohomology of $K$ vanishes, and a representative $C$. First form $C_{\leq v}$ by replacing $C^v$
by $\ker(d_C^v)$ and deleting degrees $>v$; its inclusion into $C$ is a quasi-isomorphism. Then
form $E$ by quotienting its degree $u$ by the incoming boundaries and deleting degrees $<u$. The
quotient map $C_{\leq v}\to E$ is a quasi-isomorphism, since it leaves cohomology in degrees $\geq
u$ unchanged and the deleted cohomology vanishes. Thus $C\leftarrow C_{\leq v}\to E$ is an
explicit quasi-isomorphism zigzag and $E$ is supported in $[u,v]$. When $u=v$, the sole term is
$E^u=\ker(d_C^u)/\operatorname{im}(d_C^{u-1})$; the zero object may be represented by the zero
complex. By the explicitly etale clause of [lem-sf-flat-model], choose a bounded flat
representative $H$ of $L$, supported in some $[a,b]$. The hypothesis $\ell\ne p$ makes $\ell$
invertible on these $k$-schemes, as required there. By [lem-kun-kflat-criteria](1), $H$ is K-flat.
Constant-coefficient inverse image is exact by [prop-weil-pbc-inverse-image-modules-exact];
moreover [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] says pullback of this K-flat
flat-term model is again K-flat with flat terms. Thus $K\otimes^Lf^{-1}L$ is represented by the
total tensor $E\otimes f^{-1}H$, supported in $[u+a,v+b]$. There are only finitely many summands
in each total degree. Extension by zero is exact by [lem-weil-pbc-extension-by-zero-exact], so
$j_!E$ is still bounded. The module-coefficient derived direct image of
[def-weil-pbc-direct-image] carries $D^+$ to $D^+$; hence $Rf_!K$, $Rf_!(K\otimes^Lf^{-1}L)$, and
also $Rf_!K\otimes^LL$ are bounded below. For the last assertion tensor a bounded-below
representative of $Rf_!K$ with the same bounded flat $H$. No Tor-amplitude assumption on $K$ is
used.

3. Here is the open comparison, including its normalization. For etale module sheaves $F$ on $X$
and $B$ on $\overline X$, use [lem-weil-pbc-extension-by-zero-adjunction] to form
$\kappa:j_!(F\otimes j^{-1}B)\to(j_!F)\otimes B$, the transpose of the unit $F\to j^{-1}j_!F$
tensored with $j^{-1}B$. On germs inside $X$ it sends $s\otimes t$ to $s\otimes t$; outside $X$
both sides are zero by [lem-weil-pbc-extension-by-zero-stalks] and the ordinary stalk-tensor
isomorphism [lem-pod-etale-stalk-tensor-scalar](1). Thus
[lemma-weil-pbc-geometric-stalk-conservative] shows $\kappa$ is an isomorphism of sheaves (the
inverse of a bijective linear map is linear). Apply this in each bidegree to $E$ and $p^{-1}H$.
All maps are natural, hence commute with both differentials and their total-complex signs.
Exactness of $j_!$ [lem-weil-pbc-extension-by-zero-exact] and the K-flat pullback assertion of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] identify this total-complex isomorphism with
the corresponding derived one. Its inverse is $\gamma$. This proves the required etale open
projection isomorphism, rather than importing the pro-etale-only version. The construction also
works on every base-changed compactification, with the pulled-back bounded flat model.

4. Fix any geometric point $g:\operatorname{Spec}\Omega\to Y$; write
$f_g:X_g\to\operatorname{Spec}\Omega$ and $c_g=(j_g,p_g)$ for the base-changed morphism and
compactification. Set $E_g=g'^{-1}K$ and $P=g^{-1}L$. The stalk-as-pullback identification
[lem-kun-stalk-as-pullback] and the first assertion of [lem-kun-0ezp] let us regard $P$ as an
object of $D(A)$: an etale object over $\Omega$ is a disjoint union of points, so the sheaf axiom
determines a module sheaf by its value on that point, with products on disjoint unions. This
equivalence and its inverse preserve the tensor unit, tensor products and complexes. By
[lem-kun-inverse-image-monoidal] and [thm-cbc-finite-torsion], applied to both $K$ and
$K\otimes^Lf^{-1}L$ (step 2), the source and target of the pulled-back compact projection map
identify respectively with $$R\Gamma_c(X_g,E_g)\otimes_A^LP,\qquad
R\Gamma_c(X_g,E_g\otimes_A^L\underline P),$$ where $\underline P=f_g^{-1}P$. The base-change
theorem permits arbitrary $g$: neither finite type of $g$ nor constructibility on the fiber is an
extra hypothesis. The source complexes lie in $D^+$, $A$ is finite, $j$ is quasi-compact and $p$
is proper, exactly as that theorem requires.

5. The identifications in step 4 carry the actual map to the compact projection map for $f_g$, not
just its objects. Indeed [def-cbc-exchange-map] factors the compact exchange as the proper mate
followed by the open base-change comparison. For the proper square,
[lem-weil-pbc-ringed-exchange-tensor-coherence], with $E=j_!K$ and $Q=L$, asserts exactly the
equality between exchanging after projection and projecting after exchange, with the specified
tensor comparisons. For the open square, the comparison of [lem-cbc-extension-zero-base-change] is
the inverse of the mate of the open-adjunction unit. Its compatibility with $\kappa$ from step 3
can be checked by transposing to $j_g^{-1}$: both composites are the pulled-back unit tensored
with the pulled-back second factor; on a local elementary tensor $s\otimes t$ each sends it to the
pair of pulled-back sections. Bilinearity gives equality on tensors, sheafification gives equality
of sheaf maps, and naturality gives equality in every total-complex degree. The derived open
base-change is precisely this termwise map by [cor-cbc-derived-extension-zero-base-change].
Inverting the two $\kappa$ maps gives the equality for $\gamma$. Combining the proper equality and
this open equality proves that the stalk map is exactly
$$\alpha_P:R\Gamma_c(X_g,E_g)\otimes_A^LP\longrightarrow R\Gamma_c(X_g,E_g\otimes_A^L\underline
P).$$

6. By the explicitly etale assertion of [fix-lem-finite-tor-perfect], $P=L_{\bar y}$ is
represented by a bounded finite-free complex $F^\bullet$ over $A$. It suffices to prove the proper
projection map for $p_g$ with fixed first input $j_{g!}E_g$ and variable second input $P$ on
$\operatorname{Spec}\Omega$. The open projection is already an isomorphism by step 3. By
[lem-weil-pbc-ringed-projection-mate-exact], both proper-map functors are exact, the
transformation is natural and commutes with shifts and the connecting arrows of triangles, and at
$P=A$ it is the identity. Naturality with the inclusions and projections of finite direct sums
therefore identifies its component at $A^r$ with the direct sum of $r$ identity components. Shift
compatibility gives the assertion for $A^r[-i]$. To build $F^\bullet$, remove its lowest nonzero
degree $i$: the subcomplex of degrees $>i$ and the quotient $F^i[-i]$ form a degreewise split
short exact sequence. The associated triangle is distinguished by
[lem-weil-pbc-degreewise-split-derived-triangle]. Induct on the number of nonzero terms, starting
with the zero complex and the one-term case; [lem-sf-triangle-morphism-iso] applied to the
morphism of triangles makes the remaining vertical map an isomorphism. Naturality transports this
conclusion across the quasi-isomorphism $F^\bullet\simeq P$. Thus the proper component and hence
$\alpha_P$ are isomorphisms. This uses the pointwise finite-free representative, not a claim that
$L$ is locally perfect as a sheaf complex. Retracts, although also stable under naturality and
splitting, are not needed because the stalk model is finite free.

7. Steps 4-6 show that every geometric pullback of the etale compact projection map is an
isomorphism. Apply [lem-kun-stalk-faithful-derived] to its underlying abelian-sheaf complex map:
forgetting $A$-module structure preserves the kernels, images and cokernels that compute
cohomology, and a vanishing underlying cohomology sheaf is a vanishing module sheaf. Hence its
cone is acyclic as a module complex and the etale map is an isomorphism. Its naturality in $K,L$
follows from the natural counit and tensor maps of [def-kun-projection-formula-map] and the
natural open-adjunction construction in step 3. This proves the etale assertion for the arbitrary
compactification selected in step 1.

8. For the pro-etale assertion put $C_T=\nu_T^*$. This is the exact termwise derived comparison of
[lem-sf-comparison-pullback-exact] and [def-sf-comparison-derived-pullback]. The ring
identification in the former and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] give its
canonical derived tensor comparison. Pullback comparison is [lem-weil-pbc-comparison-pullback].
Let $c_j:C_{\overline X}j_!^{et}\simeq j_!^{pro}C_X$ be
[lem-cbc-proetale-extension-zero-comparison], extended termwise; exactness on the pro-etale
localized site is [lem-pur-site-restriction-module-adjunction-exact], using the open-site
identification of [lem-weil-proetale-weakly-etale-localization]. For proper $p$, quasi-compactness
follows from its finite-type definition and quasi-separatedness from
[lem-pc-separated-quasi-separated]. Thus [lem-weil-pbc-comparison-direct-image-canonical-mate]
supplies the named isomorphism $b_p:C_YRp_*^{et}\simeq Rp_*^{pro}C_{\overline X}$, with its stated
counit normalization, for every bounded-below input. Compose it with $Rp_*^{pro}(c_j)$ to obtain
$$B_H:C_YRf_!^{et}H\xrightarrow{\sim}Rf_!^{pro}C_XH.$$ This is the compact-support comparison on
etale-origin inputs; its invertibility and naturality are also stated in
[lem-sf-class-compact-support-comparison]. We need it for $H=K$ and $H=K\otimes^Lf^{-1}L$, which
are bounded below by step 2. Exactness of $C$ keeps their realizations bounded below. All rings
here are ordinary constant finite rings, with no completed or rational tensor products.

9. Check compatibility with projection before transporting invertibility. For the proper factor
use [lem-weil-pbc-ringed-exchange-tensor-coherence] on the commutative ringed-topos square formed
by $p_{et},p_{pro},\nu_{\overline X},\nu_Y$. That lemma explicitly does not require a cartesian
square. Its exchange map is exactly $b_p$ of
[lem-weil-pbc-comparison-direct-image-canonical-mate], since both are adjunct to $C_{\overline
X}(\varepsilon^{et})$ after the inverse of the specified pullback comparison; its equality
therefore compares the actual counit-defined proper projection maps. For the open factor one can
check the canonical $c_j$ of [lem-cbc-proetale-extension-zero-comparison] on adjunctions, rather
than invoking pro-etale stalk conservativity. By [def-weil-pbc-site-comparison-morphism], $\nu_*$
is restriction on etale test objects. Hence $j_{et}^{-1}\nu_{\overline
X,*}=\nu_{X,*}j_{pro}^{-1}$: both evaluate a sheaf on the very same etale test scheme with the
same restrictions and scalar actions. The extension adjunctions
[lem-weil-pbc-extension-by-zero-adjunction], [lem-weil-extension-by-zero-adjunction], and the
comparison adjunction in that definition give natural bijections $$\operatorname{Hom}(C_{\overline
X}j_!^{et}F,M)\simeq\operatorname{Hom}(F,j_{et}^{-1}\nu_*M) =
\operatorname{Hom}(F,\nu_*j_{pro}^{-1}M)\simeq\operatorname{Hom}(j_!^{pro}C_XF,M).$$
The canonical $c_j$ is the isomorphism represented by these bijections (construct its two arrows
by the images of the two identity maps; naturality makes their composites identities). In
particular it identifies the open units. Transpose the proposed compatibility of $C(\kappa)$ and
$\kappa^{pro}$ under $j_!^{pro}\dashv j_{pro}^{-1}$; after the pullback and tensor comparisons
both transposes are that same unit tensored with the identity. The Hom bijection is injective, so
the maps agree. This calculation is on sheaves and is natural in both arguments; apply it to the
bounded flat model from step 2. The comparison pullback carries this model to a K-flat flat-term
model by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]; the exact derived comparisons
therefore give the same equality for derived tensors. Inverting $\kappa$ identifies the
transported $\gamma$ with the canonical pro-etale open projection isomorphism
[lem-cbc-extension-zero-projection-formula]. Combining proper and open equalities identifies
$C_Y(\mathrm{PF}^{et})$ with precisely the pro-etale composite specified in
[def-exchange-projection], under $B_K,B_{K\otimes^Lf^{-1}L}$ and the tensor/pullback comparisons.
Thus $\mathrm{PF}^{pro}$ for $(C_XK,C_YL)$ is an isomorphism by step 7. Finally for arbitrary
realizations with the witnesses of [def-weil-pbc-etale-origin-witness], conjugate this equality by
the supplied two witness isomorphisms. Naturality of the same projection construction gives the
stated map on those realizations and its naturality in $K,L$.
-/
theorem isIso_finiteCompactProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) X K)
    (_hL : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) Y L)
    (_hTor : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app K).app L) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X (Padic.coefficientExtensionRing l E n))
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y (Padic.coefficientExtensionRing l E n))
      (wx : Scheme.EtaleOriginWitness X (Padic.coefficientExtensionRing l E n) Kp)
      (wy : Scheme.EtaleOriginWitness Y (Padic.coefficientExtensionRing l E n) Lp)
      (_hx : wx.L.obj ≅ K) (_hy : wy.L.obj ≅ L),
      IsIso (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app
        (((ProEtale.finiteCoefficientRealization X
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Kp.obj)).app
        (((ProEtale.finiteCoefficientRealization Y
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Lp.obj)) := by
  constructor
  · exact finiteCompactProjection_etale (Padic.coefficientExtensionRing l E n) c K L
  · intro Kp Lp wx wy hx hy
    have hKb : _root_.DerivedCategory.TStructure.t.bounded K := by
      obtain ⟨a, b, _, h⟩ := _hK.2
      exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
        (fun q hq ↦ h q (.inl hq))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff K b).2 (fun q hq ↦ h q (.inr hq))⟩⟩
    exact finiteCompactProjection_proEtale (Padic.coefficientExtensionRing l E n)
      c K L hKb _hTor Kp Lp wx wy hx hy

end AlgebraicGeometry.Etale

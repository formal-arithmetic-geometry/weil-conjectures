/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Sheaf.Paper.PulledReductionStrictTowerComparison
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.IntegralPullbackStrictRoosData
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralRoosChainRepresentatives
import Sheaf.Paper.IntegralRoosResolvingCounits
import Sheaf.Paper.IntegralRoosAugmentationLocalization
import Sheaf.Paper.IntegralLambdaQuotientAugmentation
import Sheaf.Paper.IntegralRoosScalarLocalization

/-! Strict Roos normalization, assembled from the strict and derived comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] roosF roosχ roosConeFunctor
attribute [local irreducible] HasDerivedCategory.standard
  pbcIntegralDatum completedAdicChangeData
namespace WeilConjectures.IntegralPullbackStrictRoos
attribute [local irreducible] IsLambdaNormalized IsAugmentationNormalized IsENormalized
  IsUnitNormalized IsLocalized IsConstantUnitNormalized bV

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Strict Roos normalization of integral pullback and constant scalar restriction.

Source: main-20261015, det-lem-int-tensor-pullback, first paragraph and Comparison with the
Stacks Project; Stacks proetale.tex Tags 099M, 099N and algebraization.tex Tag 099I.
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization).

Proof plan (the ten steps of this DAG node):

1. Identify $R_T$ with $\varprojlim_n A_{n,T}$ by [det-prop-sfb-qlbar-colimit-x-integral-limit],
using its canonical finite projections. The coefficient datum makes $A$ a discrete valuation
ring, hence a principal ideal domain; every ideal is finitely generated, so $A$ is Noetherian.
Apply [lem-weil-pbc-constant-completion-equivalence] on each small pro-étale site with
$I=(\pi)$. Its flatness and quotient assertions give $R_T$ flat over $C_T$ and
$R_T/\pi^nR_T\cong A_{n,T}$ for every $n\geq1$, compatibly with the quotient projections. These
assertions concern the entire module categories and require no completeness of $[P]$.

2. Write $a_C:g^{-1}C_Y\cong C_X$ and $a_R:g^{-1}R_Y\cong R_X$. The constant identification
comes from inverse image of constant sheaves; the completed identification and exactness of
module inverse image are [sk-prop-sfb-cartesian-coefficients]. If $i_T:C_T\to R_T$ is the
constant-function map, naturality of the comparison $g^{-1}p_Y^*\cong p_X^*$ at the map from
discrete $A$ to continuous $A$ gives $a_R\,g^{-1}i_Y=i_Xa_C$
[sk-def-sfb-pullback-from-point-comp, sk-def-sfb-coefficient-morphisms]. By
[sk-def-sfb-module-pushforward-pullback], $g^*H=R_X\otimes_{g^{-1}R_Y}g^{-1}H$. Its
identification with $g^{-1}H$ sends $r\otimes h$ to $a_R^{-1}(r)h$, with inverse
$h\mapsto1\otimes h$. The analogous formula using $a_C$ identifies $g_C^*\operatorname{Res}_YH$
with the same abelian sheaf. The displayed coefficient-square equation makes these two
$C_X$-actions identical. Define $d_H$ by the identity on that sheaf. It therefore sends each
scalar-extension generator to its specified constant-coefficient generator, is invertible, and
is natural in $H$. Both module inverse images therefore have the same exact underlying abelian
inverse-image functor. Applying the construction in every degree gives a chain isomorphism for
every complex $H$, in particular $d=d_P$.

3. Apply [lem-weil-pbc-flat-scalar-restriction-kflat] to $C_Y\to R_Y$, flat by step 1. Since $P$
is K-flat with flat terms, $Q=\operatorname{Res}_YP$ is K-flat with flat terms over $C_Y$. Apply
the flat-term K-flat pullback assertion of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]
to the ringed-topos morphisms with coefficients $R_Y,R_X$ and $C_Y,C_X$, respectively. It gives
flat terms and K-flatness for $g^*P$ and $g_C^*Q$. These applications impose neither boundedness
nor a condition on the cohomology of $P$.

4. For any $R_T$-module $H$, construct the underived comparison
$$\beta_{T,n,H}:\operatorname{Res}_TH\otimes_{C_T}A_{n,T}\longrightarrow
\operatorname{Res}_T(H\otimes_{R_T}A_{n,T}),\qquad
h\otimes\bar a\longmapsto h\otimes\bar a.$$
Both sides are the cokernel of multiplication by $\pi^n$ on the same underlying sheaf $H$: on
the left use $A_{n,T}=C_T/(\pi^n)$, and on the right use $A_{n,T}=R_T/(\pi^n)$ from
[lem-weil-pbc-constant-completion-equivalence]. The two identifications send $h\otimes1$ to the
class of $h$, so $\beta$ is invertible. This also proves the inverse formula, including
balancing by arbitrary local $R_T$-sections, without assuming that those sections are constant.
Applying it degreewise gives a natural chain isomorphism. On each tensor generator both orders
of reduction from $n+1$ to $n$ send $h\otimes\bar a$ to $h\otimes(\bar a\bmod\pi^n)$, and
$\beta$ sends the quotient augmentation $h\mapsto h\otimes1$ to the same augmentation. Thus all
these compatibilities are strict.

5. Use the ordinary balanced tensor comparison of [def-sfb-condensed-pullback-tensor-comparison]
with $H=P^q$ and the coefficient module $A_{n,Y}$, and identify $g^*A_{n,Y}=A_{n,X}$ by
[sk-prop-sfb-cartesian-coefficients]. Degreewise this gives $\lambda_n:T_n\cong U_n$. The same
balanced calculation over $C$ gives
$g_C^*(Q\otimes_{C_Y}A_{n,Y})\cong(g_C^*Q)\otimes_{C_X}A_{n,X}$. Under inverse-coefficient
transport its formula is the balanced map sending the inverse-image tensor $h\otimes\bar a$ to
the tensor of the two inverse images; it commutes with differentials by naturality in $P^q$.
Define
$$\theta_n=g_C^*(\beta_{Y,n,P}^{-1})\circ
d_{P\otimes_{R_Y}A_{n,Y}}:\operatorname{Res}_XT_n\xrightarrow{\sim}V_n.$$
Here step 2 constructs $d$ for all complexes, so it applies even though the finite tensor need
not be K-flat. The formulas for $\beta$ and $d$ show that $\theta_n$ also sends an inverse-image
tensor $h\otimes\bar a$ to the same tensor. For either $\lambda$ or $\theta$, composing in
either order with the transition sends this generator to $h\otimes(\bar a\bmod\pi^n)$. Composing
with the augmentation sends $h$ to $h\otimes1$; on the source of $\theta$ this uses $d_P(h)=h$.
These generator equations prove equality of sheaf maps, hence of chain maps. Thus $\lambda$ and
$\theta$ are isomorphisms of strict towers, preserving their specified augmentations.

6. Restriction of scalars is the identity on underlying abelian sheaves
[def-pc-sheaf-restrict-scalars]. Kernels and local lifts of sections through epimorphisms are
therefore unchanged, so it is exact. Products of module sheaves exist and are computed
sectionwise by [lem-weil-proetale-countable-products-exact]. Consequently the canonical map
$\operatorname{Res}_X(\prod_nT_n)\to\prod_n\operatorname{Res}_XT_n$ is an isomorphism: over
every site object it sends a tuple to that same tuple, and both $C_X$-actions are componentwise.
It commutes with projections, differentials and $s$. Finite direct sums and their maps are
unchanged as well. This fixes the product and cone identifications used for $E_P$.

7. For $W$ put $B_W=\prod_nW_n$ and $F_W=1-s_W$. In the coordinate order fixed in the statement,
$$\mathsf R(W)^q=B_W^{q-1}\oplus B_W^q,\qquad D_W(y,x)=(-d_Wy-F_Wx,d_Wx).$$
Let $a=\prod_n\lambda_n$ and let $e=\prod_n\theta_n$, using step 6 for the source of $e$. Strict
transition compatibility from step 5 gives $aF_T=F_Ua$ and $eF_{\operatorname{Res}T}=F_Ve$.
Define $L_P(y,x)=(ay,ax)$ and $E_P(y,x)=(ey,ex)$. For example,
$$D_U(ay,ax)=(-a\,d_Ty-aF_Tx,a\,d_Tx)=L_P D_T(y,x).$$
The identical computation with $e$ proves the chain equation for $E_P$. Their inverses are
diagonal products of the levelwise inverses and satisfy the same equations. Naturality in $P$
follows from the natural level maps and the componentwise product formulas. Thus these are
precisely the asserted cochain isomorphisms, with no cone-map choice.

8. For a compatible augmentation $b:L\to W$, set $b^\Pi=(b_n)_n$. Compatibility says
$F_Wb^\Pi=0$. Hence
$$D_W(0,b^\Pi z)=(0,b^\Pi d_Lz),$$
so the specified $\alpha_W(z)=(0,b^\Pi z)$ is a chain map with exactly the given cone signs.
Step 5 gives $a b_T^\Pi=b_U^\Pi$ and $e\operatorname{Res}_X(b_T^\Pi)=b_V^\Pi d$. Evaluating the
diagonal maps of step 7 now gives
$$L_P\alpha_T(z)=(0,b_U^\Pi z)=\alpha_U(z),\qquad
E_P\operatorname{Res}_X(\alpha_T)(z)=(0,b_V^\Pi d(z))=\alpha_Vd(z).$$
These are equalities of actual chain maps, rather than equalities inferred only from their
finite projections.

9. It remains to identify these actual cone maps with the total derived strict-tower
comparisons. By [lem-weil-proetale-countable-products-exact], products are exact for each
coefficient sheaf here. Thus [lem-pe-roos-cone-calculus] applies: its reordered cone is exactly
$\mathsf R(W)$ with coordinates $(x,y)$, and its action on strict maps is the diagonal product
map of step 7. For a K-injective tower resolution $W\to I$, as used in
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], this gives a quasi-isomorphism $\mathsf
R(W)\to\mathsf R(I)$. By [lem-weil-derived-limit-roos-complex] the natural map $\varprojlim
I_n\to\mathsf R(I)$ is a quasi-isomorphism, explicitly $z\mapsto(0,(z_n)_n)$. The remaining
hypothesis of the K-injective Roos lemma holds: the module category on a small pro-étale
skeleton is Grothendieck by [lem-pur-ringed-site-grothendieck-abelian] and hence has enough
injectives by [lem-sp-grothendieck-enough-injectives]. The strict tower resolution is supplied
by the ringed strict-tower theorem. The resulting zigzag identifies $Q\mathsf R(W)$ with the
total right derived inverse limit. For an augmented tower, both composites from $L$ to $\mathsf
R(I)$ are $(0,(L\to W_n\to I_n)_n)$, so this zigzag identifies the augmentation with the
strict-derived-tower unit. Where the unit is defined as in [def-weil-pbc-completed-pullback],
through a resolution $\Delta L\to I'$ and $R\lim$ of $\Delta L\to W$, choose a lift $I'\to I$;
by K-injectivity of $I$ its composite with $\Delta L\to I'$ is homotopic to $\Delta L\to W\to
I$, and the diagonal product of that homotopy is a homotopy on $\mathsf R(I)$, so both
descriptions give the same map in the derived category. It is natural in strict maps; hence the
localizations of $L_P,E_P$ are the claimed canonical comparisons, not arbitrary isomorphisms of
Roos triangles.

10. By step 3, $P$, $g^*P$, $Q$ and $g_C^*Q$ are valid flat-term K-flat representatives for
their respective derived tensor calculations
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus $U$ computes the finite derived
reductions of $g^*[P]$, and $V$ computes those of $g_C^*[Q]$ (constant-coefficient inverse image
commutes with reduction by the same balanced calculation of step 5). The quotient-tower units
are the derived-completion units by [lem-weil-pbc-constant-completion-equivalence], including
for inputs which are not complete. In the notation of [def-weil-pbc-completed-pullback], use the
identification of step 1 [det-prop-sfb-qlbar-colimit-x-integral-limit] of its
$A_T=\varprojlim_n(A_n)_T$ with $R_T$. Its structure map $c_g$ is then $a_R$ of step 2:
naturality of $g^{-1}p_Y^*\cong p_X^*$ at $\mathcal O_E\to\mathcal O_E/\pi^n$
[sk-def-sfb-pullback-from-point-comp, sk-def-sfb-coefficient-morphisms] gives the $n$-th
projection of $a_R$ as the constant-sheaf comparison $g^{-1}(A_n)_Y\cong(A_n)_X$, which, like
the $n$-th component of $c_g$, sends each constant section to itself; maps into the limit agree
when their projections do. So module pullback along $c_g$ is the item's $g^*$. Applying derived
pullback to the augmented strict reduction tower gives the tower represented here by $T$:
inverse image on $R$-modules is exact by [sk-prop-sfb-cartesian-coefficients], so it computes
this operation on any representative of the tower. Step 9 identifies its chosen total derived
inverse limit and unit with $Q\mathsf R(T)$ and $Q\alpha_T$. Therefore step 8 proves both
required normalized derived identities. On derived-complete input the constant formula is
precisely Stacks completed pullback (099N(2),(5)); on arbitrary input it is the same ordinary
pullback followed by completion and its unit. This argument never identifies the two ambient
coefficient categories, or asserts that an arbitrary $[P]$ is complete.
-/
theorem integralPullbackStrictRoosNormalization
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    ∃ (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
      (a : T l E g ≅ U l E g)
      (e : T l E g ⋙ towerRes l E X ≅ V l E g)
      (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
      (ε : EType l E g) (κR : kappaType X (R l E X))
      (jR : inclusionType X (R l E X)) (κC : kappaType X (C l E X))
      (jC : inclusionType X (C l E X)),
      IsComparison l E g d a e αT αU αV ε κR jR κC jC := by
  obtain ⟨⟨d, a, e, αT, αU, αV, ε, κR, jR, κC, jC⟩,
    hd, ha, he, hα, hε, hαε, hκR, hκC⟩ :=
      integralRoosChainRepresentatives l E g k
  obtain ⟨hU, hT, hC⟩ := integralRoosAugmentationLocalization l E g k
    d a e αT αU αV ε κR jR κC jC hd ha he hα hε hαε hκR hκC
  refine ⟨d, a, e, αT, αU, αV, ε, κR, jR, κC, jC,
    hd, ha, he, ?_, hα, hε, ?_, hαε, hκR, hκC, ?_, hC, ?_⟩
  · intro P hP
    exact (integralRoosResolvingCounits l E g k P hP).1
  · intro P
    have hprod : Limits.Pi.lift (bT l E g P) ≫
        roosPmap ((lamComplex l E g a).hom.app P) =
        Limits.Pi.lift (bU l E g P) := by
      apply roosProduct_augmentation
      intro n q
      rw [bT_f, bU_f, lamComplex_hom_component]
      exact integralLambdaQuotientAugmentation l E g a ha (P.X q) n
    rw [Lmap_hom]
    exact roosMap_augmentation ((lamComplex l E g a).hom.app P)
      (αT P) (αU P) (Limits.Pi.lift (bT l E g P)) (Limits.Pi.lift (bU l E g P))
      (IsAugmentationNormalized.t l E g hα P)
      (IsAugmentationNormalized.u l E g hα P) hprod
  · unfold IsLocalized
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro P
      rw [Lmap_hom]
      exact κR.hom.naturality ((lamComplex l E g a).hom.app P)
    · exact integralRoosScalarLocalization l E g e ε κR jR κC jC hε hκR hκC
    · exact hU
    · exact hT
  · intro P hP
    exact (integralRoosResolvingCounits l E g k P hP).2

end WeilConjectures.IntegralPullbackStrictRoos

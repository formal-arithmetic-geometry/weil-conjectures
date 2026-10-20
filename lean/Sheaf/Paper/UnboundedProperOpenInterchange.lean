/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility
import Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear

/-!
# Unbounded proper/open interchange and its canonical normalizations

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B (case (b)), 0F7C, 0F7D
and 0F7F (blueprint: lem-amb-unbounded-proper-open-interchange).

The sheaf isomorphism is specified by equality of its two maps into the common direct
image. This is precisely equality of the proper-support subsheaves, and fixes the map.
The derived isomorphism is specified on every K-injective representative and every
K-injective resolution of its open extension. All composition equations include the
canonical composition isomorphisms. No boundedness of the input is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Unbounded proper/open interchange, including its representative, adjunction, pasting,
identity and arbitrary base-change normalizations.
Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F
(blueprint: lem-amb-unbounded-proper-open-interchange).

Proof:

1. Write $\theta_Q:i_!r_*\cong p_*k_!$ for the sheaf identification in the statement. Indeed,
properness includes separatedness and finite type, so the proper-support composition theorem
applies to both paths $ir=pk$; its proper and open specializations identify both sides with the
same subsheaf of $(ir)_*$. For an open immersion, the diagonal is an isomorphism, so it is
separated; on an affine target, principal affine opens contained in the image cover the source and
their coordinate rings are one-element localizations, hence finitely generated algebras. Thus the
open edges are locally of finite type as required. Its naturality makes $\theta_Q$ an isomorphism
of complexes on applying it termwise. Choose a K-injective representative $J$ of $K$ and a quasi-
isomorphism $\rho:k_!J\to I$ with $I$ K-injective. Define $\Gamma_{Q,K}$ to be the class of
$p_*\rho\circ\theta_{Q,J}$. The source is $Di_!Rr_*K$ and the target is $Rp_*Dk_!K$, by
K-injective computation and exactness of extension by zero. This is independent of the resolutions
and natural in $K$: a morphism of derived inputs has a unique homotopy-class representative
$f:J\to J'$; the derived map induced by $k_!f$ has a unique representative $g:I\to I'$ with
$g\rho=\rho'k_!f$ up to homotopy. Naturality of $\theta_Q$ gives the required commuting square
after $p_*$. Additive functors preserve a homotopy $dh+hd$ termwise, so these equalities hold in
the derived category. For a change of resolutions, $f$ and $g$ are homotopy equivalences, giving
the same map under the canonical identifications.
Uses: lem-cbc-proper-support-sheaf-composition, def-weil-proper-morphism, def-weil-open-immersion,
def-weil-finite-type-morphism, prop-weil-pbc-kinjective-resolutions-exist, lem-weil-pbc-
kinjective-total-derived, lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-extension-by-zero-
exact.

2. There is a finite cohomological-dimension bound for $p_*$ on all constant-$A$ module sheaves.
The assumed finite affine cover of $Z$ is a finite cover by quasi-compact spaces, so $Z$ is quasi-
compact. Since $p$ is of finite type, the fibre-dimension-bound theorem gives an integer $d\geq0$
bounding the dimensions of all fibres of $p$. Choose $N\geq1$ with $N1_A=0$ (the additive order of
$1_A$, and $N=1$ for the zero ring). Every $A$-module sheaf has torsion underlying abelian sheaf,
since $Nm=(N1_A)m=0$. The proper torsion bound gives $R^qp_*U(M)=0$ for $q>2d$. The bounded-below
module/abelian direct-image comparison, applied to the single sheaf $M$ and then to degree-$q$
cohomology, identifies this with the underlying abelian sheaf of $R^qp_*M$; hence $R^qp_*M=0$ for
$q>2d$. This use of the bounded-below comparison is only for sheaves in degree zero, not for
unbounded complexes. Module sheaf categories are Grothendieck abelian and $p_*$ is additive and
left exact, so the finite-cd acyclic-complex theorem applies with bound $2d$.
Uses: lem-weil-pbc-affine-scheme-qcqs, def-weil-proper-morphism, lem-fin-finite-type-fibre-
dimension-bound, lem-kun-proper-torsion-cd-bound, lem-weil-pbc-module-abelian-derived-direct-
image-comparison, lem-weil-pbc-module-sheaves-grothendieck-abelian, def-weil-pbc-direct-image,
lem-kun-finite-cd-acyclic-complex.

3. Choose $J$ in Step 1 to be K-injective with every term injective, using the injective-term
K-injective resolution theorem in the Grothendieck category of module sheaves. For every degree
$n$, the open-extended-injective acyclicity lemma applied to precisely $(p,r,i,k)$ gives
$R^qp_*(k_!J^n)=0$ for $q>0$; it requires neither a cartesian square nor a dimension bound. Thus
$k_!J$ is an unbounded complex of $p_*$-acyclic objects. The finite-cd theorem from Step 2 says
that its canonical map to its total derived image is an isomorphism, and this map is represented
by $p_*\rho:p_*k_!J\to p_*I$. Therefore $\Gamma_{Q,K}$ is an isomorphism. An arbitrary K-injective
representative is homotopy equivalent to the chosen injective-term one; $r_*$, $i_!$ and $k_!$
preserve this homotopy equivalence termwise. Resolution independence from Step 1 then gives the
asserted formula and isomorphism for every K-injective representative. No boundedness of $K$ has
been used.
Uses: lem-weil-pbc-module-sheaves-grothendieck-abelian, lem-pur-kinjective-degreewise-existence,
lem-cbc-open-extended-injective-proper-acyclic, lem-kun-finite-cd-acyclic-complex, lem-weil-pbc-
kinjective-total-derived, lem-weil-pbc-kinjective-hom-derived.

4. For cartesian $Q$ verify the open-adjunction normalization, including its direction. The sheaf
adjunction $i_!\dashv i^*$ descends termwise to the homotopy categories and then to derived
categories, since both functors are exact; the triangle identities descend with the units and
counits. The open unit $1\to i^*Di_!$ is an isomorphism: on any etale object over the open, the
extension-by-zero presheaf and all its covering restrictions are just the original sheaf. Open
inverse image is restriction, compatibly with modules. Also $k^*$ takes K-injectives to
K-injectives, being right adjoint to the exact functor $k_!$. On $k_!J\xrightarrow{\rho}I$, let
$\eta_k:J\xrightarrow{\sim}k^*k_!J$ be the open unit and put $v=k^*\rho\circ\eta_k:J\to k^*I$.
This is a quasi-isomorphism between K-injectives, hence $r_*v$ is a homotopy equivalence. In the
formula for $\lambda_Q$, the exchange evaluated on $I$ is represented by
$\operatorname{Ex}^0_{p,i,I}:i^*p_*I\to r_*k^*I$, and $\lambda_Q$ is
$(r_*v)^{-1}\operatorname{Ex}^0_{p,i,I}$. This follows directly by taking the mate of the termwise
counit in the definition of the unbounded exchange (the same calculation is written in Step 8). By
restriction of sections and the definition of $\theta_Q$ as equality of underlying sections,
$\operatorname{Ex}^0_{p,i,k_!J}\circ i^*\theta_{Q,J}\circ\eta_i=r_*\eta_k$. Naturality with
respect to $\rho$ therefore gives $\operatorname{Ex}^0_{p,i,I}\circ
i^*\Gamma_{Q,K}\circ\eta_i=r_*v$. Hence $\lambda_Q\circ i^*\Gamma_{Q,K}\circ\eta_i=1$. Since
$\Gamma_Q$ and $\eta_i$ are isomorphisms, this says exactly that the adjunct of $\Gamma_Q$ is
$\lambda_Q^{-1}$, and the inverse adjunction formula gives $\Gamma_Q=\varepsilon_i\circ
Di_!(\lambda_Q^{-1})$.
Uses: lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-extension-by-zero-exact, prop-weil-
pbc-inverse-image-modules-exact, lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-
localization-universal-property, def-weil-pbc-extension-by-zero, lem-weil-pbc-etale-inverse-image-
restriction, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-hom-derived,
def-kun-unbounded-exchange, def-weil-pbc-underived-exchange, lem-cbc-proper-support-sheaf-
composition.

5. The composites of the proper edges are proper by proper-composition stability. For vertical
pasting choose $J$ K-injective on the top left, and $\rho:k_{1!}J\to I$ with $I$ K-injective on
the top right. Direct images preserve K-injectives: they are right adjoints to exact constant-
coefficient inverse images. Thus $r_{1,*}J$ and $p_{1,*}I$ compute the iterated derived direct
images without another replacement. The map $a=p_{1,*}\rho\circ\theta_{Q_1,J}:i_{1!}r_{1,*}J\to
p_{1,*}I$ is a quasi-isomorphism by Step 3, so it can itself be used as the K-injective resolution
for computing $\Gamma_{Q_2}$ at $r_{1,*}J$. The resulting map is
$p_{2,*}a\circ\theta_{Q_2,r_{1,*}J}$. For clarity, under the resolution $a$ the object
$Rp_{2,*}(i_{1!}r_{1,*}J)$ is represented by $p_{2,*}p_{1,*}I$. The map $Rp_{2,*}\Gamma_{Q_1}$ is
then represented by the identity of $p_{2,*}p_{1,*}I$: the square comparing $a$ with the identity
resolution of $p_{1,*}I$ has top map $a$ and bottom map $1$. Consequently the claimed two-factor
composite is precisely $p_{2,*}a\circ\theta_{Q_2,r_{1,*}J}$. Expanding $a$ gives
$p_{2,*}p_{1,*}\rho\circ p_{2,*}\theta_{Q_1,J}\circ\theta_{Q_2,r_{1,*}J}$. The last two factors
identify the same underlying sections in the common subsheaf of $(i_2r_2r_1)_*J$; associativity of
sheaf composition therefore makes them $\theta_{Q_2Q_1,J}$. The remaining factor is precisely the
representative for the outer rectangle. The derived direct-image composition isomorphisms have
this resolution normalization, so inserting them gives the stated vertical equation.
Uses: lem-weil-pbc-proper-composition, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-
right-adjoint-preserves-kinjective, lem-cbc-proper-support-sheaf-composition, lem-weil-pbc-ringed-
topoi-derived-pushforward-composition.

6. For horizontal pasting take $J$ K-injective on $U$, $\rho:k_!J\to I$ K-injective on the middle
top scheme, and $\sigma:l_!I\to H$ K-injective on the right top scheme. Since $l_!$ is exact,
$u=\sigma\circ l_!\rho:l_!k_!J\to H$ is a quasi-isomorphism. The two consecutive interchange maps
are represented by $j_!(p_*\rho\circ\theta_{Q_1,J})$ followed by $q_*\sigma\circ\theta_{Q_2,I}$.
Naturality of $\theta_{Q_2}$ moves $\rho$ through this expression, giving $q_*\sigma\circ
q_*l_!\rho\circ\theta_{Q_2,k_!J}\circ j_!\theta_{Q_1,J}$. The two $\theta$ factors identify
sections in the same proper-support subsheaf of the common composite direct image, so their
product is $\theta_{Q_2Q_1,J}$. Thus the composite is $q_*u\circ\theta_{Q_2Q_1,J}$, the outer
comparison computed with the resolution $u$. The canonical open-extension composition maps
identify $j_!i_!$ with $(ji)_!$ and $l_!k_!$ with $(lk)_!$, yielding exactly the horizontal
equation in the statement.
Uses: prop-weil-pbc-kinjective-resolutions-exist, lem-weil-pbc-extension-by-zero-exact, lem-cbc-
proper-support-sheaf-composition, lem-cbc-extension-zero-composition.

7. If the proper edges are identities, commutativity identifies the two open edges. The
representative of Step 1 is then just the resolution $i_!J\to I$, hence gives the identity of
$Di_!K$ under its derived identification. If the open edges are identities, the proper edges
agree; choose $I=J$ and $\rho=1_J$, so the representative is the identity on $p_*J$. These give
the asserted identity comparisons with the same normalization as the composition maps.
Uses: lem-cbc-proper-support-sheaf-composition, lem-weil-pbc-kinjective-total-derived, lem-cbc-
extension-zero-composition.

8. Record explicitly the complex model for the exchange used in the final diagram. For a cartesian
square with proper or arbitrary vertical map $h$, base map $b$, top projection $a$ and new
vertical map $h_1$, let $L$ be K-injective and let $t:a^*L\to L_1$ be a K-injective resolution.
Then the unbounded exchange of the statement is represented by
$h_{1,*}t\circ\operatorname{Ex}^0_{h,b,L}:b^*h_*L\to h_{1,*}L_1$. To check this, the derived
adjunction $h^*\dashv Rh_*$ computed with $L$ has counit represented by the ordinary termwise
counit $h^*h_*L\to L$: this follows from the termwise Hom adjunction and the bijection from
homotopy maps into a K-injective to derived maps. The defining mate of the unbounded exchange is
therefore represented by $h_1^*b^*h_*L\cong a^*h^*h_*L\to a^*L\xrightarrow{t}L_1$. Applying the
termwise adjunction $h_1^*\dashv h_{1,*}$ to this map gives exactly
$h_{1,*}t\circ\operatorname{Ex}^0_{h,b,L}$. Localization preserves these unit, counit and
naturality equations. All calculations are $A$-linear: the module inverse-image adjunction has the
same underlying maps as the abelian adjunction. This proves the formula for arbitrary unbounded
$L$ without invoking the bounded-below-only termwise-exchange lemma.
Uses: def-kun-unbounded-exchange, def-weil-pbc-underived-exchange, prop-weil-pbc-inverse-image-
modules-exact, lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-localization-universal-property.

9. Finally consider arbitrary base change by $b:Z_1\to Z$. Properness and openness are preserved
under base change. The new schemes remain Noetherian: $W_1$ is open in $Z_1$, $V_1$ is proper and
hence finite type over $Z_1$, and $U_1$ is proper and finite type over $W_1$. Choose $J,I,\rho$ as
in Step 1, a K-injective resolution $j:d^*J\to J_1$, and a K-injective resolution $t:a^*I\to I_1$.
Put $s=k_{1!}j:k_{1!}d^*J\to k_{1!}J_1$ and $w=t\circ a^*\rho\circ e_{k,J}^{-1}:k_{1!}d^*J\to
I_1$. Both $s,w$ are quasi-isomorphisms, by exact pullback and exact extension by zero. The
K-injective Hom bijection gives a chain map $v:k_{1!}J_1\to I_1$ with $vs\simeq w$, unique up to
homotopy; two-out-of-three says $v$ is a quasi-isomorphism. Compute $\Gamma_{Q_1}$ with this $v$.
Before resolutions the following equality of maps of complexes holds:
$$p_{1,*}e_{k,J}\circ\operatorname{Ex}^0_{p,b,k_!J}\circ b^*\theta_{Q,J}=\theta_{Q_1,d^*J}\circ
i_{1!}\operatorname{Ex}^0_{r,c,J}\circ e_{i,r_*J}.$$ Indeed the proper-support identifications are
equalities of subsheaves of the common composite direct image and commute with pullback. On their
ambient direct images both paths restrict the same section along the projection for the base
change of $pk=ir$; this is also the two pasting formulas for adjunction mates. Now apply
$p_{1,*}v\circ p_{1,*}k_{1!}j$ to the displayed equality. Naturality of $\theta_{Q_1}$ moves $j$
to $i_{1!}r_{1,*}j$ on its right-hand side. On its left-hand side, the equation $v\circ
k_{1!}j\simeq t\circ a^*\rho\circ e_k^{-1}$ and naturality of the underived exchange replace the
resulting path by $p_{1,*}t\circ\operatorname{Ex}^0_{p,b,I}\circ b^*(p_*\rho\circ\theta_{Q,J})$.
Step 8 identifies this as $(Rp_{1,*}e_k)\circ(\operatorname{Ex}_{p,b}Dk_!)\circ(b^*\Gamma_Q)$
after identifying $I_1$ as a representative of $Dk_{1!}d^*K$ via $v$. On the right, Step 8
identifies $r_{1,*}j\circ\operatorname{Ex}^0_{r,c,J}$ as $\operatorname{Ex}_{r,c}$, and
$p_{1,*}v\circ\theta_{Q_1,J_1}$ as $\Gamma_{Q_1}$. This is precisely the required base-change
equation. Homotopies are preserved by all the termwise functors, so the equation holds in the
derived category. To identify the specified degreewise maps, let $j$ be either open edge and write
$b,c,j_1$ for its base-change diagram. Take the adjunct of the defining conjugate comparison
$\beta:j_{1!}c^*\to b^*j_!$ under $j_{1!}\dashv j_1^*$. Substitution of the underived exchange
formula and of the composite unit from the definition cancels the inverse-image/direct-image
counit against its unit by the triangle identity; the resulting map is $c^*\eta_j:c^*\to
c^*j^*j_!\cong j_1^*b^*j_!$. This is precisely the mate whose inverse is $e_j$ in the extension-
zero base-change lemma. Thus $e_i,e_k$ are the inverses of the degreewise maps specified in the
statement, including their normalization. This argument uses no invertibility, constructibility or
bound on the dimensions of the schemes; the fibre bound in Step 2 was deduced from properness over
the given quasi-compact base.
Uses: lem-weil-pbc-proper-base-change, lem-weil-pbc-open-immersion-base-change, def-weil-proper-
morphism, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-
noetherian, prop-weil-pbc-kinjective-resolutions-exist, prop-weil-pbc-inverse-image-modules-exact,
lem-weil-pbc-extension-by-zero-exact, lem-cbc-extension-zero-base-change, lem-weil-pbc-kinjective-
hom-derived, lem-cbc-proper-support-sheaf-composition, def-weil-pbc-underived-exchange, lem-weil-
pbc-mate-pasting, def-weil-pbc-etale-shriek-base-change-map.
-/
theorem unboundedProperOpenInterchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
      (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])),
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : IsPullback k r p i),
        ∃ lam : D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
            D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]),
          (∀ K : DerivedCategoryModule A U,
            lam.hom.app K =
              (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
                R((r)_*[ModuleCat.{u + 1} A]).map
                  (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                    (ModuleCat.{u + 1} A) k).unit.app K))) ∧
          ∀ K : DerivedCategoryModule A U,
            (Γ k r p i sq.toCommSq).hom.app K =
              D((i)_!open[ModuleCat.{u + 1} A]).map (lam.inv.app K) ≫
                (derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) i).counit.app
                    (R((p)_*[ModuleCat.{u + 1} A]).obj
                      (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U V W Z S T : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian S] [IsNoetherian T]
        (k : U ⟶ V) (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (i₁ : W ⟶ Z)
        (r₂ : W ⟶ S) (p₂ : Z ⟶ T) (i₂ : S ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
        [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
        (sq₁ : CommSq k r₁ p₁ i₁) (sq₂ : CommSq i₁ r₂ p₂ i₂)
        (K : DerivedCategoryModule A U),
        (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom.app K =
          D((i₂)_!open[ModuleCat.{u + 1} A]).map
              ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂).inv.app K) ≫
            (Γ i₁ r₂ p₂ i₂ sq₂).hom.app (R((r₁)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₂)_*[ModuleCat.{u + 1} A]).map ((Γ k r₁ p₁ i₁ sq₁).hom.app K) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂).hom.app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K)) ∧
      (∀ {U V T W Z S : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian T] [IsNoetherian W]
        [IsNoetherian Z] [IsNoetherian S]
        (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
        (i : W ⟶ Z) (j : Z ⟶ S)
        [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
        [IsProper r] [IsProper p] [IsProper q]
        (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
        (K : DerivedCategoryModule A U),
        (Γ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂)).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map ((Γ k r p i sq₁).hom.app K) ≫
            (Γ l p q j sq₂).hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
                Functor.mapDerivedCategoryCompIso _ _).inv.app K)) ∧
      (∀ {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
        (k : U ⟶ V) [IsOpenImmersion k] (K : DerivedCategoryModule A U),
        (Γ k (𝟙 U) (𝟙 V) k ⟨by simp⟩).hom.app K =
          D((k)_!open[ModuleCat.{u + 1} A]).map
              ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
                Functor.mapDerivedCategoryIdIso _).hom.app K) ≫
            ((((𝟙 V)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) V) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U W : Scheme.{u}} [IsNoetherian U] [IsNoetherian W]
        (r : U ⟶ W) [IsProper r] (K : DerivedCategoryModule A U),
        (Γ (𝟙 U) r r (𝟙 W) ⟨by simp⟩).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (Adjunction.leftAdjointIdIso
                (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
                (upperStarId (ModuleCat.{u + 1} A) W)) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((r)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (Adjunction.leftAdjointIdIso
                    (openImmersionLowerShriekUpperStarAdjunction
                      (ModuleCat.{u + 1} A) (𝟙 U))
                    (upperStarId (ModuleCat.{u + 1} A) U)) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app K)) ∧
      (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K)) := by
  sorry

end AlgebraicGeometry.Etale

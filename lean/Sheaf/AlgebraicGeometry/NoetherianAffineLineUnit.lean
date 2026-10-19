/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.Paper.FiniteDirectImageComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.EtaleClosedSheafInternalAdjunction

/-!
# The ordinary finite-coefficient affine-line unit over a Noetherian base

Source: ILO, Travaux de Gabber, Expose XVI, Proposition 1.5, proof on printed page 227
(blueprint: lem-per-noetherian-affine-line-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical ordinary small-etale derived unit for the affine line, followed by the
canonical identification of the inverse image of the constant coefficient complex.
Source: ILO, Travaux de Gabber, Expose XVI, Proposition 1.5, proof on printed page 227
(blueprint: lem-per-noetherian-affine-line-unit).

The coefficient ring is lifted only to match the existing small-etale universe convention.
No regularity, separatedness, or morphism to a field is required.

Proof plan:

1. Put $m=\ell^n$ and $P=\mathbf P(\{0,1\};B)$, with projection $q$. The standard charts
   [lem-weil-pbc-projective-space-standard-charts] are $D(x_0)=\operatorname{Spec}R[t]$ and
   $D(x_1)=\operatorname{Spec}R[s]$ over each $\operatorname{Spec}R\subset B$, with $s=t^{-1}$ on
   the intersection. The closed locus $x_0=0$ is empty in the first chart and is $s=0$ in the
   second; these equations agree on the overlap and identify this closed subscheme with $B$. Write
   $i:B\hookrightarrow P$ for it. Its complementary open $j:U\hookrightarrow P$ is $D(x_0)=\mathbf
   A^1_B$, with $qj=p$ and $qi=\operatorname{id}_B$. By
   [lemma-nagata-projective-space-base-change-proper], $q$ is proper, hence of finite type;
   [lem-weil-pbc-finite-type-over-noetherian] makes $P$ Noetherian. Thus all Noetherian hypotheses
   of the proper projection formula below hold, without requiring $B$ to be regular or over a
   field.

2. Use [lem-asd-etale-finite-twist-pullback] with $A=\Lambda$ and $m=\ell^n$. Set
   $T_B=\Lambda_B(1)[2]$, $T_P=\Lambda_P(1)[2]=q^{-1}T_B$, and $K=\Lambda_B(-1)[-2]$. Evaluation
   gives $K\otimes^L T_B\cong\Lambda_B$ and $q^{-1}K\otimes^L T_P\cong\Lambda_P$: the finite Tate
   line is locally free of rank one, so its dual evaluations are isomorphisms, and the shifts
   cancel. Write $F=Rq_*$ and $G(L)=q^{-1}L\otimes^L T_P$. The entire ordinary-etale adjunction
   $F\dashv G$ and the decomposition $b:T_B\oplus\Lambda_B\xrightarrow{\sim}FT_P$ are
   [lem-asd-ordinary-finite-p1-adjunction]. Its trace is $t=\operatorname{pr}_2b^{-1}$ and its
   actual counit at $L$ is $(1_L\otimes t)\pi_{L,T_P}^{-1}$. Here $\pi$ is the canonical proper
   projection isomorphism [lem-amb-proper-coproducts-projection]. In particular
   $GK\cong\Lambda_P$.

3. Tensor $b$ with $K$ and use the same canonical projection isomorphism to obtain
   $$d:\Lambda_B\oplus K=(K\otimes^L T_B)\oplus K\xrightarrow{1_K\otimes b}K\otimes^L
   FT_P\xrightarrow{\pi_{K,T_P}}F\Lambda_P.$$ Its first component is the ordinary $q^{-1}\dashv F$
   unit $\eta_q:\Lambda_B\to F\Lambda_P$. Indeed the first component of $b$ is the unit at $T_B$.
   The map $\pi$ of [lem-amb-proper-coproducts-projection] is
   $Rq_*(\sigma)\,\mathrm{PF}_q\,\sigma$, where $\mathrm{PF}_q$ is by definition the morphism
   adjoint to $(\varepsilon^{\mathrm{ord}}\otimes1)$ composed with the inverse-image tensor
   comparison [def-kun-projection-formula-map] (the same adjoint-of-counit construction as
   [lem-weil-pbc-ringed-projection-mate-exact]); the symmetries $\sigma$ commute with the units by
   naturality. By this adjoint-of-counit description of $\pi$, the transpose of the first
   component of $d$ is $1_{q^{-1}K}$ tensored with
   $\varepsilon^{\mathrm{ord}}_{T_P}\,q^{-1}(\eta_{q,T_B})$, followed by evaluation. This is the
   identity of $\Lambda_P$ by the ordinary triangle identity. The counit
   $\epsilon_K:FGK=F\Lambda_P\to K$ of the different adjunction $F\dashv G$ satisfies
   $\epsilon_Kd=\operatorname{pr}_2$, since its formula in Step 2 cancels $\pi$ and $t
   b=\operatorname{pr}_2$. Thus both the unit and trace have specified coordinates.

4. Let $i^!$ denote the ordinary right adjoint of $i_*$ provided by
   [lem-exc-closed-support-triangle], and write $c:i_*i^!\to\operatorname{id}$ for its counit. The
   termwise $i_*$ is exact [lem-per-etale-closed-sheaf-internal-adjunction], so it computes the
   derived direct image $Ri_*$. Since $qi=\operatorname{id}_B$,
   [lem-weil-derived-direct-image-composition](5) therefore identifies $Fi_*$ canonically with the
   identity. Composing $i_*\dashv i^!$ and $F\dashv G$ gives $Fi_*\dashv i^!G$, whose counit at
   $L$ is $$Fi_*i^!GL\xrightarrow{F(c_{GL})}FGL\xrightarrow{\epsilon_L}L$$ by
   [def-weil-pbc-composite-adjunction]. Compare this with the identity adjunction by
   [det-sp-unique-right-adjoint]. It follows that this displayed counit, regarded as $i^!GL\to L$,
   is an isomorphism. Let $\theta:K\xrightarrow{\sim}i^!GK$ be its inverse at $K$. After
   $GK=\Lambda_P$, the map $f=F(c_{\Lambda_P})\,\theta:K\to F\Lambda_P$ therefore satisfies
   $\epsilon_K f=1_K$. This obtains the needed closed-support value from the two adjunctions,
   without an absolute-purity assertion about $B$.

5. Apply [lem-exc-closed-support-triangle] to $\Lambda_P$ and apply $F=Rq_*$. This preserves
   distinguished triangles by [lem-pc-right-derived-functor-triangulated]. The direct-image
   composition comparison [lem-weil-derived-direct-image-composition](5) identifies the third term
   with $R(qj)_*\Lambda_U=Rp_*\Lambda_U$. Identify the first term with $K$ using
   $Fi_*=\operatorname{id}$ and $\theta$, and identify the middle term using $d$. We get a
   distinguished triangle $$K\xrightarrow{u}\Lambda_B\oplus
   K\xrightarrow{v}C\xrightarrow{\partial}K[1],\qquad C=Rp_*\Lambda_U.$$ The second arrow before
   these identifications is $F$ of the ordinary open adjunction unit. By Steps 3 and 4,
   $\operatorname{pr}_2u=\epsilon_Kf=1_K$. Hence $u=(a,1_K)$, where
   $a=\operatorname{pr}_1d^{-1}f$. No identification of $a$ with a Chern class is needed.

6. Here is the split-triangle calculation with all arrows retained. By
   [lem-weil-pbc-hom-into-triangle-exact](i), also on rotated triangles, $vu=0$ and
   $u[1]\partial=0$. Applying the left inverse $\operatorname{pr}_2[1]$ gives $\partial=0$. Put
   $z=\operatorname{pr}_1-a\operatorname{pr}_2:\Lambda_B\oplus K\to\Lambda_B$. Since $zu=0$,
   [lem-weil-pbc-hom-out-of-triangle-exact](i) gives $w:C\to\Lambda_B$ with $wv=z$. Therefore
   $w(v\operatorname{in}_1)=1$. Also
   $$((v\operatorname{in}_1)w-1_C)v=v(\operatorname{in}_1z-1)=-vu\operatorname{pr}_2=0.$$ Part
   (ii) of the same Hom-out exactness says this difference factors through $\partial$, so it is
   zero. Thus $v\operatorname{in}_1:\Lambda_B\to C$ is an isomorphism with inverse $w$.

7. It remains to identify the isomorphism, rather than just its endpoints. Step 3 identifies
   $d\operatorname{in}_1$ with $\eta_q$. Step 5 therefore identifies $v\operatorname{in}_1$ with
   $\Lambda_B\xrightarrow{\eta_q}Rq_*\Lambda_P\xrightarrow{Rq_*(\eta_j)}Rq_*Rj_*\Lambda_U$. Under
   the canonical composition comparison this is the unit for $p=qj$. More explicitly the ordinary
   inverse images are exact by [prop-weil-pbc-inverse-image-modules-exact], and the small-etale
   module-sheaf categories are Grothendieck abelian
   [lem-weil-pbc-module-sheaves-grothendieck-abelian], so
   [lem-sfb-derived-composition-adjunction-normalization] applies to $q^{-1},j^{-1},p^{-1}$ and
   their specified direct-image right adjoints. Its normalized derived comparison is the
   degreewise direct-image composition on injective representatives, and its unit is exactly
   $Rq_*(\eta_j)\eta_q$ by [def-weil-pbc-composite-adjunction]. Thus Step 6 proves that the
   canonical unit in the statement is invertible. All operations used are on ordinary small-etale
   module derived categories.
-/
theorem isIso_noetherian_affineLine_unit (B : Scheme.{u}) [IsNoetherian B]
    (ell n : ℕ) (hell : ell.Prime) (hn : 0 < n) (hB : IsUnit (ell : Γ(B, ⊤))) :
    IsIso
      ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).unit.app
          (ordinaryFiniteUnit (ULift.{u + 1} (ZMod (ell ^ n))) B) ≫
        (ordinaryFinitePushforward (ULift.{u + 1} (ZMod (ell ^ n)))
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).map
          (ordinaryFiniteUnitPullback (ULift.{u + 1} (ZMod (ell ^ n)))
            (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).hom) := by
  sorry

end AlgebraicGeometry.Etale

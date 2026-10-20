/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.Paper.RingedProjectionTensorComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProperOpenSection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Tensor projection maps and compact-support composition

Source: Stacks Project, `more-etale.tex`, Tags 0F7B and 0F7J, and
`sites-cohomology.tex`, Tag 0E48 (blueprint: lem-amb-shriek-tensor-composition).

The projection map is the existing proper/open compactification construction with both
factors exchanged by the canonical signed derived tensor symmetry. Exact termwise inverse
image is identified with left derived inverse image by its canonical comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The coefficient-first compact-support tensor projection map on a specified compactification.
Source: Stacks Project, Tags 0B56, 0GL1, and 0F7I
(blueprint: lem-amb-shriek-tensor-composition).

The middle map is exactly the proper projection followed by the derived termwise
open-extension tensor comparison. The two symmetries and the exact-pullback comparison
only put its endpoints in the coefficient-first convention of this node.
-/
noncomputable def compactSupportProjectionMapOfCompactification
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M)

/-- The same canonical map on the chosen, compactification-independent compact-support functor.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: lem-amb-shriek-tensor-composition). -/
noncomputable def compactSupportProjectionMap
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) :=
  compactSupportProjectionMapOfCompactification A
    (HasCompactification.compactification f) M K

/-- Tensor projection maps respect the tower-normalized compact-support compositor.
Source: Stacks Project, Tags 0F7B and 0F7J, with the tensor square of Tag 0E48
(blueprint: lem-amb-shriek-tensor-composition).

Proof (the fourteen steps recorded in the DAG):

1. Use right-hand tensor factors until the last step. Write $J_j=Dj_!$, $S_h=Rh_*$,
$\gamma_j:J_jE\otimes N\to J_j(E\otimes j^*N)$ for the canonical derived open tensor isomorphism,
and $\pi_h:S_hE\otimes N\to S_h(E\otimes h^*N)$ for the counit-defined projection map. On
$c=(j,r)$ the projection map is $$t_c=S_r(\gamma_{j;M,r^*N})\circ\pi_{r;J_jM,N}.$$ It first
applies the proper projection and then $S_r$ of the open comparison. The map $P$ in the statement
is $t_c$ conjugated by the canonical signed tensor symmetry. These maps are defined on arbitrary
unbounded inputs; neither $\pi_h$ nor $t_c$ is assumed invertible.
Uses: lem-pur-etale-open-derived-tensor, def-kun-projection-formula-map,
def-amb-etale-compact-support.

2. The derived open tensor map restricts to the identity under $j^*J_j\cong1$: the sheaf map has
this property, and the derived map is induced from it using a K-flat tensor representative. Thus,
for composable opens $j,b$, with the canonical open compositor understood,
$$\gamma_{bj;M,N}=J_b(\gamma_{j;M,b^*N})\circ\gamma_{b;J_jM,N}.$$ Indeed on complexes the two
canonical sheaf tensor comparisons both extend the identity of $M\otimes (bj)^*N$ by zero, with
the same direct-sum tensor differential. Passing to the derived comparisons preserves this
equality. The cited derived tensor lemma already supplies the unbounded comparison; no tensor
product of unresolved complexes is being substituted for derived tensor.
Uses: lem-pur-etale-open-derived-tensor, lem-weil-pbc-ringed-slice-extension-tensor,
lem-cbc-extension-zero-composition.

3. For arbitrary composable proper factors use
$$\pi_{vu;E,N}=S_v(\pi_{u;E,v^*N})\circ\pi_{v;S_uE,N}.$$ This is the second identity of the
generic projection-composition lemma. Its compositor is the canonical derived direct-image
compositor, normalized on K-injective resolutions, so it is the compositor used in compact-support
towers. Constant-coefficient inverse image is exact, hence the derived pullbacks in the generic
statement are precisely the pullbacks used here. This uses no projection isomorphism.
Uses: lem-sfb-ringed-projection-tensor-composition,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
prop-weil-pbc-inverse-image-modules-exact.

4. First prove the mixed square for a CARTESIAN proper/open square $(k:U\to V,r:U\to W,p:V\to
Z,i:W\to Z)$. Put $M_N=M\otimes r^*i^*N$ and $\Gamma:J_iS_r\to S_pJ_k$. The desired equality is
$$S_p(\gamma_k)\pi_p(\Gamma_M\otimes1)=\Gamma_{M_N}J_i(\pi_r)\gamma_i.\tag{*}$$ Both arrows have
source $J_iS_rM\otimes N\cong J_i(S_rM\otimes i^*N)$ and target $S_pJ_kM_N$. Under $J_i\dashv
i^*$, compare their restrictions, then compose with $\lambda_{M_N}:i^*S_pJ_kM_N\to S_rM_N$, the
exchange followed by $k^*J_k\cong1$. The interchange node gives $i^*\Gamma_M=\lambda_M^{-1}$. The
exchange/tensor coherence node gives, for $E=J_kM$, $$\operatorname{Ex}_{E\otimes
p^*N}\,i^*\pi_p=\pi_r(\operatorname{Ex}_E\otimes1).$$ Restriction of $\gamma_k$ and $\gamma_i$ is
the identity by step 2. Consequently the first adjunct becomes
$\pi_r(\lambda_M\lambda_M^{-1}\otimes1)=\pi_r$; the second becomes
$(\lambda_{M_N}\lambda_{M_N}^{-1})\pi_r=\pi_r$. The adjunction bijection proves (*). All
pullback/tensor identifications in this calculation are those of the cited coherence statement.
Uses: lem-amb-unbounded-proper-open-interchange, lem-weil-pbc-ringed-exchange-tensor-coherence,
lem-pur-etale-open-derived-tensor, lem-amb-etale-adjoint-locality.

5. Now let $u:T_1\to T_2$ be a proper refinement with $uj_1=j_2$, for opens $j_a:X\hookrightarrow
T_a$. Put $V=T_1\times_{T_2}X$, $b:V\hookrightarrow T_1$, $q:V\to X$, and
$s=(j_1,1):X\hookrightarrow V$. The proper-open-section lemma says $s$ is clopen, $qs=1$ and
$bs=j_1$; $q$ is proper by the proper-open-p-proper lemma. Factor the refinement square
horizontally as $$(s,1_X,q,1_X)\quad\text{followed by}\quad(b,q,u,j_2).$$ The second square is
cartesian. The first is a clopen-section square, which can be noncartesian. The horizontal pasting
identity for the SPECIFIED support/K-injective comparisons gives $$\Gamma_{\rm ref,M}=\Gamma_{\rm
cart,J_sM}\circ J_{j_2}(\Gamma_{\rm sec,M}).$$ Thus it remains to check the first square, not to
apply the cartesian normalization to it.
Uses: lem-weil-pbc-proper-open-section, lem-weil-pbc-proper-open-p-proper,
lem-amb-unbounded-proper-open-interchange.

6. For the decomposition $V=s(X)\amalg C$, the cited clopen sheaf-product equivalence also
identifies constant-$A$ MODULE sheaves with pairs: an $A$-action and its homomorphisms are
specified componentwise. Here $s^*$ is first projection and $s_!=s_*$ is insertion
$F\mapsto(F,0)$; both are exact, and $s^*\dashv s_*$ has counit the identity. The same formulas
hold for complexes and homotopies. They preserve quasi-isomorphisms, so the localization universal
property descends these functors, their inverse equivalences, and their units/counits to the whole
unbounded derived categories. The exact-functor-derived lemma identifies $S_s$ with $J_s$, with
this normalization. In particular restriction to the two components detects equality of derived
arrows; this is an equivalence of categories, not an inference from equality on cohomology or
stalks.
Uses: lem-weil-pbc-etale-sheaf-clopen-product, lem-weil-pbc-localization-universal-property,
lem-weil-pbc-exact-functor-derived-functor.

7. Let $J$ be a K-injective representative on $X$. By step 6, $J_sJ=s_*J$ is K-injective: it is
the right adjoint of the exact first projection, so the cited K-injective-preservation lemma
applies. In the SPECIFIED construction of $\Gamma_{\rm sec}$ choose the resolution $s_!J\to I$ to
be the identity with $I=s_!J$. Its support identification is $$J=1_!1_*J\longrightarrow
q_*s_!J=(qs)_*J=J,$$ which is the identity on sections (all support lies in the clopen first
component). The derived compositor $c:S_qJ_s\cong S_{qs}=1$ is normalized by these same
K-injective representatives. Hence $\Gamma_{\rm sec}=c^{-1}$ as an actual derived transformation,
with precisely the support/resolution normalization required in the item.
Uses: lem-amb-unbounded-proper-open-interchange, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

8. Under $S_s=J_s$, one has $\pi_s=\gamma_s$. In fact the counit definition of $\pi_s$ restricts
on $s(X)$ to $1\otimes1$, since $s^*s_*=1$ with identity counit, and it is the unique arrow
$0\to0$ on $C$. The canonical $\gamma_s$ has these same two components by step 2. The derived
component equivalence of step 6 therefore identifies the arrows. This computation is valid for
every derived tensor input, including a nonperfect module over $A=\mathbf Z/4$.
Uses: def-kun-projection-formula-map, lem-pur-etale-open-derived-tensor.

9. Apply projection composition, step 3, to $X\xrightarrow{s}V\xrightarrow{q}X$ with $qs=1$. Since
$\pi_s=\gamma_s$ and $\pi_1=1$, it says $$c_{M\otimes N}\,S_q(\gamma_s)\pi_q=c_M\otimes1_N.$$
Compose on the right with $\Gamma_{\rm sec,M}\otimes1_N=c_M^{-1}\otimes1_N$ and on the left with
$c_{M\otimes N}^{-1}$. The result is $$S_q(\gamma_s)\pi_q(\Gamma_{\rm
sec,M}\otimes1_N)=\Gamma_{\rm sec,M\otimes N}.$$ This is exactly (*) for $(s,1,q,1)$: the other
route has $\gamma_1=\pi_1=1$. Thus the noncartesian part of every refinement respects tensor, with
the specified arrow, without any invertibility claim for $\pi_q$.
Uses: lem-sfb-ringed-projection-tensor-composition.

10. Combine the two factors of the refinement in step 5. More explicitly, substitute $\Gamma_{\rm
ref}=\Gamma_{\rm cart}J_s\circ J_{j_2}\Gamma_{\rm sec}$ into the left side of (*), and expand
$\gamma_{j_1}=\gamma_{bs}$ by step 2. Apply the cartesian identity of step 4 with input $J_sM$;
naturality moves $\Gamma_{\rm sec,M}$ through its open tensor map. The remaining interior
composite is $S_q(\gamma_s)\pi_q(\Gamma_{\rm sec,M}\otimes1)$, which step 9 replaces by
$\Gamma_{\rm sec,M\otimes j_2^*N}$. Horizontal pasting then recombines the two factors into
$\Gamma_{\rm ref,M\otimes j_2^*N}$. This proves the fully typed refinement identity
$$S_u(\gamma_{j_1;M,u^*N})\pi_{u;J_{j_1}M,N}(\Gamma_{\rm ref,M}\otimes1) =\Gamma_{\rm ref,M\otimes
j_2^*N}\gamma_{j_2;M,N}.$$ Its source is $J_{j_2}M\otimes N$ and target is $S_uJ_{j_1}(M\otimes
j_2^*N)$, using $j_1^*u^*N=j_2^*N$.
Uses: lem-amb-unbounded-proper-open-interchange.

11. For compactifications $a=r_1j_1=r_2j_2$ with $r_1=r_2u$, the refinement comparison is
$\rho=S_{r_2}\Gamma_{\rm ref}$ followed by the direct-image compositor. Apply step 10 with
$N=r_2^*Q$, then $S_{r_2}$, and precompose with $\pi_{r_2}$. Naturality of $\pi_{r_2}$ moves
$\Gamma_{\rm ref}\otimes1$ past it, and step 3 combines $\pi_{r_2}$ and $\pi_u$ into $\pi_{r_1}$.
By the definition in step 1 the resulting equality is
$$t_{c_1;M,Q}(\rho_M\otimes1_Q)=\rho_{M\otimes a^*Q}\,t_{c_2;M,Q}.$$ The compact-support
comparison lemma fixes $\rho$ as exactly this proper/open refinement arrow. Since $\rho$ is
invertible, its inverse also respects these tensor maps, by cancellation. Composing such equations
proves the same for comparisons through a common refinement.
Uses: lem-amb-unbounded-compact-support-comparisons, lem-sfb-ringed-projection-tensor-composition,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

12. Now choose the compatible tower supplied in the STATEMENT of the compact-support comparison
lemma: compactify $g$ by $i:Y\hookrightarrow\overline Y$, $s:\overline Y\to Z$, and compactify
$if$ by $a:X\hookrightarrow\overline X$, $p:\overline X\to\overline Y$. Put $V=\overline
X\times_{\overline Y}Y$, with $b:V\hookrightarrow\overline X$, $q:V\to Y$, $j:X\hookrightarrow V$,
so $bj=a$. These give the compactifications $(j,q)$ of $f$ and $(a,sp)$ of $gf$. On these choices
$\alpha$ is $S_s$ of the CARTESIAN interchange $J_iS_q\to S_pJ_b$, followed by the proper and open
compositors. Step 11 has established tensor compatibility of arbitrary refinement comparisons, so
passage to this tower, and back from it, now preserves the projection maps as well as $\alpha$.
Uses: lem-amb-unbounded-compact-support-comparisons, def-amb-etale-compact-support.

13. Expand $t_g$, $S_sJ_i(t_f)$ and $\alpha$ on that tower. Their middle factors are $\gamma_i$,
$J_i(\pi_q)$ and $\Gamma$, so step 4 replaces them by $(\Gamma\otimes1)$, $\pi_p$ and
$S_p(\gamma_b)$ in the reverse route. Step 3 combines the proper projections for $p,s$; step 2
combines the open tensor maps for $j,b$. Naturality lets these substitutions be whiskered by $S_s$
and $J_j$. Thus both expanded routes are equal, with source $(S_sJ_iS_qJ_jM)\otimes K$ and target
$S_{sp}J_a(M\otimes f^*g^*K)$. Returning to tensor factors on the left by the SAME signed symmetry
in each occurrence gives $$\alpha_{g,f,f^*g^*K\otimes M}\,Rg_!(P_{f,g^*K,M})\,P_{g,K,Rf_!M}
=P_{gf,K,M}(1_K\otimes\alpha_{g,f,M}).$$ Step 11 and the refinement compatibility of $\alpha$ in
the comparison lemma give this identity on all compactifications, including noncartesian
refinements. Each equality was of derived transformations, not merely of their stalk or cohomology
maps.
Uses: lem-amb-unbounded-compact-support-comparisons, lem-cbc-extension-zero-composition,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

14. When the maps in the displayed identity are invertible, compose the equality on the
appropriate side with the inverse of each isomorphism and use functoriality of composition. This
gives the equivalent identity for the inverses.
-/
theorem compactSupportProjectionMap_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    (compactSupportProjectionMap A g
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (compactSupportProjectionMap A f M
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).obj M) =
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      compactSupportProjectionMap A (f ≫ g) M K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((unboundedEtaleUpperStarCompIso A f g).hom.app K)).app M)) ∧
    (∀ [IsIso (compactSupportProjectionMap A g
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K)]
        [IsIso (compactSupportProjectionMap A f M
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))]
        [IsIso (compactSupportProjectionMap A (f ≫ g) M K)],
      (unboundedEtaleLowerShriekCompIso A f g).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
              ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          (inv (compactSupportProjectionMap A f M
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))) ≫
        inv (compactSupportProjectionMap A g
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((unboundedEtaleUpperStarCompIso A f g).inv.app K)).app M) ≫
        inv (compactSupportProjectionMap A (f ≫ g) M K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
          ((unboundedEtaleLowerShriekCompIso A f g).inv.app M)) := by
  sorry

/-- The tensor projection maps commute with all compactification comparisons, including
proper refinements whose open square is not cartesian.
Source: Stacks Project, Tags 0F7B, 0F7D, and 0F7I, with Tag 0E48
(blueprint: lem-amb-shriek-tensor-composition).

Proof: factor a proper refinement into a clopen-section square followed by a cartesian
proper/open square. For the section, the clopen product description identifies the specified
support comparison with the inverse direct-image compositor, and the projection with open
tensor extension. Proper projection composition with its retraction proves the tensor square.
For the cartesian factor use the exchange/tensor square after open adjunction. Paste the two
squares, apply the ambient proper pushforward, and combine proper projection composition.
Invertible refinement comparisons can be cancelled, so comparison through any common
refinement has the same compatibility, independently of its choice.
-/
theorem compactSupportProjectionMap_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) ≫
      compactSupportProjectionMapOfCompactification A d M K =
    compactSupportProjectionMapOfCompactification A c M K ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) := by
  let T := derivedTensor (ModuleCat.{u + 1} A) Y
  let U := derivedTensor (ModuleCat.{u + 1} A) X
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let D := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let N := (U.obj M).obj (L.obj K)
  let e := rightDerivedLowerShriekOfCompactificationIso A c d
  let pc : (T.obj (F.obj M)).obj K ⟶ F.obj N :=
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K
  let pd : (T.obj (G.obj M)).obj K ⟶ G.obj N :=
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app M).app K
  have hp : (T.map (e.hom.app M)).app K ≫ pd = pc ≫ e.hom.app N :=
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A c d M K).symm
  let S := derivedTensorSymmetry (ModuleCat.{u + 1} A) Y
  let l := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let q := ((U.obj M).map (l.hom.app K)) ≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app (D.obj K)).app M
  have hc : compactSupportProjectionMapOfCompactification A c M K =
      (S.hom.app K).app (F.obj M) ≫ pc ≫ F.map q := by
    dsimp only [compactSupportProjectionMapOfCompactification, q]
    rw [Functor.map_comp]
  have hd : compactSupportProjectionMapOfCompactification A d M K =
      (S.hom.app K).app (G.obj M) ≫ pd ≫ G.map q := by
    dsimp only [compactSupportProjectionMapOfCompactification, q]
    rw [Functor.map_comp]
  rw [hc, hd]
  have hs : (T.obj K).map (e.hom.app M) ≫ (S.hom.app K).app (G.obj M) =
      (S.hom.app K).app (F.obj M) ≫ (T.map (e.hom.app M)).app K :=
    (S.hom.app K).naturality (e.hom.app M)
  have hn : e.hom.app N ≫ G.map q = F.map q ≫ e.hom.app _ :=
    (e.hom.naturality q).symm
  calc
    _ = (S.hom.app K).app (F.obj M) ≫
        ((T.map (e.hom.app M)).app K ≫ pd) ≫ G.map q := by
      rw [← Category.assoc, hs]
      simp only [Category.assoc]
    _ = (S.hom.app K).app (F.obj M) ≫
        (pc ≫ e.hom.app N) ≫ G.map q := by rw [hp]
    _ = _ := by
      rw [Category.assoc, Category.assoc, hn]
      simp only [Category.assoc]
      rfl

end AlgebraicGeometry.Etale

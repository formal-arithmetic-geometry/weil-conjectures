/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusSite
public import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

import WeilConjectures.CategoryTheory.BraidedSheafTensorGenerators

/-!
# Frobenius trivialization over condensed coefficients

Source: latest blueprint, sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum,
scheme-Frobenius comparison underlying kappa; Stacks Tag 0F6W
(blueprint: lem-pur-condensed-frobenius-linear-trivialization).

The sheaf and module trivializations, the forward coefficient comparison, scalar extension,
and total left derivation are the existing canonical constructions. The theorem records their
compatibility, exact termwise descent, and normalization at exponent zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical absolute-Frobenius trivialization is monoidal and coefficient-linear,
its module component factors the sheaf map through scalar extension, and its total left
derivation is its termwise descent on the ordinary unbounded derived category.

Source: latest blueprint, sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum,
scheme-Frobenius comparison underlying kappa; Stacks Tag 0F6W
(blueprint: lem-pur-condensed-frobenius-linear-trivialization).

Proof plan:

1. Put $F=H^*_{\mathrm{Ab}}$, $G=H_*^{\mathrm{Ab}}$, $R=\Lambda_X$, and write $c:FG\to\mathrm{id}$
for the adjunction counit. Define $d:\mathrm{id}\to G$ by $d_{A,V}=A(r_V^{-1}):A(V)\to
A(V\times_{X,H}X)$. The $r_V$ are the isomorphisms in the item hypotheses. Their naturality makes
$d$ natural in $A,V$, and $A(r_V)$ gives its inverse. The mate formula gives $t_A=c_A\circ
F(d_A)$: it is the stipulated trivialization, rather than an arbitrarily chosen inverse-image
equivalence.

2. Check that $d$ is monoidal for the actual lax structure of $G$. Write $j_{A,B}:UA\otimes_p
UB\to U(A\otimes B)$ and $j_0:\underline{\mathbf Z}\to U\mathbf1$ for the sheafification maps. The
generator formulas of [lem-sfb-pushforward-comp-monoidal] describe that lax structure. Precompose
the equation $d_{A\otimes B}=\mu^G_{A,B}(d_A\otimes d_B)$ with $j_{A,B}$. At $V$, its two sides
are $(A\otimes B)(r_V^{-1})j_{A,B,V}$ and $j_{A,B,V\times_{X,H}X}(A(r_V^{-1})\otimes
B(r_V^{-1}))$. They agree by naturality of $j$. The unit equation, precomposed with $j_0$, is
naturality of $j_0$ along $r_V^{-1}$; restriction of the constant presheaf is identity. These
precompositions detect equality by [lem-sfb-braided-sheaf-tensor-generators]. All sites may be
replaced by small skeletons and the coefficient category is $\mathrm{Ab}$.

3. The counit $c$ is monoidal by [lem-sfb-finite-monoidal-adjunction]. For sheaves $A,B$,
naturality of the strong tensorator $\mu^F$ and Step 2 give $F(d_{A\otimes
B})\mu^F_{A,B}=F(\mu^G_{A,B})\mu^F_{GA,GB}(F(d_A)\otimes F(d_B))$. Compose with $c_{A\otimes B}$
and use its monoidal equation. The result is $t_{A\otimes B}\mu^F_{A,B}=t_A\otimes t_B$. The same
substitution with the two unit maps gives $t_{\mathbf1}\varepsilon^F=\mathrm{id}_{\mathbf1}$. Thus
$t$ is monoidal.

4. For a profinite set $S$ put $W=X[S]=\operatorname{Spec}LC(S,\mathbf
Z)\times_{\operatorname{Spec}\mathbf Z}X$, with projections $q$ and $v$. It is a weakly etale test
object by [det-def-sfb-pullback-from-point]. It has characteristic $p$: pulling the equation $p=0$
on $X$ through the unital structure-sheaf map for $v$ gives that equation on $W$. Let
$e:W\times_{X,H}X\to W$ be the canonical map having projections $q\operatorname{pr}_W$ and
$\operatorname{pr}_X$. It is defined because both maps to $\operatorname{Spec}\mathbf Z$ are the
structure map. Its composite with $r_W$ has projections $qF_W^b=q$, by [lem-pur-frobenius-locally-
constant-spectrum], and $v$. The fibre-product universal property therefore gives $e
r_W=\mathrm{id}_W$. Since $r_W$ is invertible, $e=r_W^{-1}$.

5. The right adjoint of $p_X^*$ evaluates $A$ at $X[S]$. Whiskering $d$ by this right adjoint
gives, at $(A,S)$, the restriction $A(r_{X[S]}^{-1})$. On the other hand the inverse pullback
compositor defining $H^*p_X^*\to p_X^*$ is the conjugate of the pushforward compositor: on $(A,S)$
the latter is restriction $A(e)$, by the iterated-fibre-product formula for pushforward
composition. Step 4 identifies these restrictions for every $A,S$. The mate bijection [def-weil-
pbc-adjunction-mate] therefore identifies the left transformations. Hence $t_{p_X^*B}$ is the
canonical point-comparison for every condensed abelian group $B$. Taking the underlying group of
$\Lambda$ yields $t_R=\alpha_H$, by the definition of the coefficient morphism. This does not
assume that $\Lambda$ is a discrete ring.

6. For the action $a_M:R\otimes M\to M$, naturality of $t$ gives $t_M F(a_M)=a_M t_{R\otimes M}$.
Compose with $\mu^F_{R,M}$ and substitute Steps 3 and 5 to obtain exactly $t_M
F(a_M)\mu^F_{R,M}=a_M(\alpha_H\otimes t_M)$. By [def-sfb-modobj-transport] and scalar restriction,
this says that $t_M$ is an $FR$-linear map
$\operatorname{mapMod}(F)M\to\operatorname{Res}_{\alpha_H}M$. Its inverse is linear too: multiply
the same equation by the inverse maps. Naturality for module maps is the naturality of $t$.

7. Transpose the isomorphism of Step 6 across
$\operatorname{Ext}_{\alpha_H}\dashv\operatorname{Res}_{\alpha_H}$. This gives the required
scalar-extension factor $\widetilde
t_M:\operatorname{Ext}_{\alpha_H}(\operatorname{mapMod}(F)M)\to M$, uniquely characterized by
$\operatorname{Res}_{\alpha_H}(\widetilde t_M)\eta_M=t_M$. Since $\alpha_H$ is an isomorphism,
[det-def-sfb-change-of-scalars], clause 5, says restriction is an equivalence and extension is its
quasi-inverse. Equivalently $\widetilde t_M=\epsilon_M\circ\operatorname{Ext}_{\alpha_H}(t_M)$.
Extension is an equivalence by clause 5, so its adjunction counit $\epsilon$ is invertible by
[lem-coef-adjunction-equivalence-counit-iso]. Both factors are therefore invertible. The
adjunction bijection and its uniqueness give naturality. Its source is exactly the defined module
pullback, with scalar extension retained.

8. For an arbitrary integer-indexed complex $K$, the maps $\widetilde t_{K^n}$ commute with
differentials by naturality, so form a chain isomorphism $H^*_{\Lambda}K\to K$. This is natural
for every chain map. Pullback is additive and exact by [det-prop-sfb-module-pullback-exact-main];
alternatively this chain isomorphism directly shows it preserves quasi-isomorphisms. The exact-
functor factorization [lem-weil-pbc-exact-functor-derived-factorization] supplies its termwise
functor on the ordinary unbounded derived category. The localization universal property descends
the chain isomorphism too: its naturality on an inverted quasi-isomorphism remains valid for the
inverse, hence for every localized morphism. This descended functor is its total left derived
functor: its comparison with the termwise functor is invertible, so it satisfies the derived
universal property directly. If computed using resolutions as in [det-def-sfb-derived-categories],
every resolution augmentation remains a quasi-isomorphism under pullback, giving the same functor
and comparison. Thus the descended isomorphism is $D(\widetilde t_H):LH^*_{\Lambda}\to\mathrm{id}$
on all of $D(\operatorname{Mod}_R)$; no boundedness or coefficient condition was used.

9. When $b=0$, $H=\mathrm{id}_X$ and $r_V=(\mathrm{id}_V,v)$ is inverse to the identity-base-
change projection $V\times_{X,\mathrm{id}}X\to V$. Thus $d$ is precisely the inverse identity-
pushforward comparison. Its adjunct $t$ is the canonical identity-inverse-image unitor, by the
mate formula. The coefficient component is the identity coefficient comparison by Step 5. The
scalar-extension adjunction then says that its unique linear factor is the canonical identity-
module-pullback unitor; both have the same adjunct $t_M$. The equality holds termwise on every
complex and hence after localization. This proves the asserted normalization, including at the
zero ring, zero module and zero complex.
-/
theorem condensed_frobenius_linear_trivialization
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : X.IsCharacteristic p) (b : ℕ) :
    NatTrans.IsMonoidal
        (ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b).hom ∧
      (ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b).hom.app
          (condensedRingObj Λ X) =
        condensedPullbackHom Λ (X.iterateFrobenius hp (hX.2 ⊤) b) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ X),
        Functor.LaxMonoidal.μ
            (ProEtale.upperStar AddCommGrpCat.{u + 1} (X.iterateFrobenius hp (hX.2 ⊤) b))
            (condensedRingObj Λ X) M.X ≫
          (ProEtale.upperStar AddCommGrpCat.{u + 1} (X.iterateFrobenius hp (hX.2 ⊤) b)).map
            (ModObj.smul (M := condensedRingObj Λ X) (X := M.X)) ≫
          (ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b).hom.app
            M.X =
        (condensedPullbackHom Λ (X.iterateFrobenius hp (hX.2 ⊤) b) ⊗ₘ
          (ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b).hom.app
            M.X) ≫ ModObj.smul (M := condensedRingObj Λ X) (X := M.X)) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ X),
        Mod.extendUnitHom (condensedPullbackHom Λ (X.iterateFrobenius hp (hX.2 ⊤) b))
            (((ProEtale.upperStar AddCommGrpCat.{u + 1}
              (X.iterateFrobenius hp (hX.2 ⊤) b)).mapMod (condensedRingObj Λ X)).obj M) ≫
          ((upperStarIterateFrobeniusIso Λ hp (hX.2 ⊤) b).hom.app M).hom =
        (ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b).hom.app
          M.X) ∧
      Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp (hX.2 ⊤) b) =
        leftDerivedUpperStarIsoMapDerivedCategory Λ (X.iterateFrobenius hp (hX.2 ⊤) b) ≪≫
          Functor.mapDerivedCategoryNatIso (upperStarIterateFrobeniusIso Λ hp (hX.2 ⊤) b) ≪≫
          Functor.mapDerivedCategoryIdIso
            (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
              (condensedRingObj Λ X)) ∧
      (b = 0 → ∃ w : X.iterateFrobenius hp (hX.2 ⊤) b = 𝟙 X,
        ProEtale.upperStarIterateFrobeniusIso AddCommGrpCat.{u + 1} hp (hX.2 ⊤) b =
          eqToIso (congrArg (ProEtale.upperStar AddCommGrpCat.{u + 1}) w) ≪≫
            ProEtale.upperStarId AddCommGrpCat.{u + 1} X ∧
        upperStarIterateFrobeniusIso Λ hp (hX.2 ⊤) b =
          eqToIso (congrArg (upperStar Λ) w) ≪≫ upperStarId Λ X ∧
        Functor.leftDerivedFunctorIdIso (upperStarIterateFrobeniusIso Λ hp (hX.2 ⊤) b) =
          eqToIso (congrArg (fun f : X ⟶ X ↦ (upperStar Λ f).leftDerivedFunctor) w) ≪≫
            Functor.leftDerivedFunctorIdIso (upperStarId Λ X)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

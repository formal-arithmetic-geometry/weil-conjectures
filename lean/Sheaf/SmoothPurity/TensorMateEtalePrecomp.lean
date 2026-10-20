/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# Canonical tensor mates under etale precomposition

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-asd-smooth-tensor.proof.md, paragraph 3
(blueprint: lem-asd-tensor-mate-etale-precomp).

The locality isomorphism uses the graph-normalized compact-support comparison and the
termwise sum/evaluation adjunction. The theorem states both the actual tensor-mate equality
and the sum-counit normalization on the whole ordinary unbounded derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The canonical etale locality comparison `u^* f^× ≅ (fu)^×`.
Source: the blueprint thm-asd-smooth-tensor proof, paragraph 3
(blueprint: lem-asd-tensor-mate-etale-precomp).

Conjugate the specified proper/open tower comparison against the composite of the
sum-extension/evaluation adjunction and the exceptional adjunction. The normalization `N`
includes the graph-section characterization, so this construction uses no arbitrary
isomorphism or arbitrary adjunction for the etale map. Its existence is supplied by
`nonempty_etaleCompactSupportNormalization`; the theorem below holds for every such `N`.
-/
noncomputable def tensorMateEtalePrecompLocalityIso
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{v}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification f] [HasCompactification (u ≫ f)] :
    R(f)^![ModuleCat A] ⋙ (u)^*[ModuleCat A].mapDerivedCategory ≅
      R(u ≫ f)^![ModuleCat A] :=
  ((conjugateIsoEquiv
    (rightDerivedUpperShriekAdjunction (ModuleCat A) (u ≫ f))
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
          inferInstance).mapDerivedCategoryAdjunction).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat A) f)))
    (etaleAmbientLeftComparison A N u f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (u ≫ f)))).symm

/-- Canonical tensor mates commute with separated finite-type etale precomposition, with
its specified sum/evaluation counit. Source: the blueprint thm-asd-smooth-tensor proof,
paragraph 3 (blueprint: lem-asd-tensor-mate-etale-precomp).

The two `homEquiv` terms below are exactly alpha_f and alpha_h: inverse projection,
tensor of the exceptional counit at the coefficient unit, then the right unitor.
The signed symmetries put the upstream projection in coefficient-first order, and
`leftDerivedUpperStarIsoMapDerivedCategory` identifies left derived with exact inverse image.
The first clause inserts the canonical tensor and pullback-composition comparisons.
The second clause explicitly uses the sum-extension fold counit, not the counit of a
chosen exceptional adjunction for u. No boundedness or smoothness is assumed.

Proof (the seven steps of the DAG node):
1. Write $F=Rf_!$, $E=Du_!$, $V=u^*$, $G=f^\times$ and $H=Rh_!$. Throughout, $\otimes$ means
$\otimes_A^L$ and composition is right to left. Write $q_a(K,M):Ra_!(a^*K\otimes M)\to K\otimes
Ra_!M$ for the inverse-directed projection denoted $P_a$ in the question. It is a natural
isomorphism: choose a compactification $a=rj$, apply the open tensor isomorphism of
[lem-pur-etale-open-derived-tensor], and then the proper projection isomorphism of
[lem-amb-proper-coproducts-projection], using the tensor symmetry [lem-kun-tensor-sym] to put $K$
first. The compactification ambient scheme is Noetherian by
[lem-weil-pbc-finite-type-over-noetherian], since $r$ is proper, hence finite type, over the
Noetherian target. These are precisely the factors of the projection used in
[lem-amb-shriek-tensor-composition], whose statement includes the refinement compatibility. All
these maps exist on the entire unbounded categories.

2. By [lem-amb-etale-adjoint-locality] and [thm-amb-etale-exceptional-adjoint], $E\dashv V$ and
$F\dashv G$ are adjunctions on the unbounded categories. Since $U$ and $X$ are Noetherian, hence
quasi-compact and quasi-separated, and $u$ is separated of finite type, $u$ has a compactification
by [thm-nagata-compactification]. Use [lem-asd-etale-compact-support-normalization] and
[lem-amb-unbounded-compact-support-comparisons] to fix $c:FE\xrightarrow{\sim}H$: first identify
$E$ with compact-support direct image of $u$, then apply the proper/open tower composition. Put
$e_C=\epsilon_{u,C}:EVC\to C$. The composite Hom bijection of [def-weil-pbc-composite-adjunction]
sends $b:M\to VGB$ to $\epsilon_{f,B}\circ F(e_{GB})\circ FE(b)$. On the other hand the specified
comparison $\lambda_B$ sends it to $\lambda_B\circ b$, whose $H\dashv h^\times$-transpose,
precomposed with $c_M$, is $\epsilon_{h,B}\circ H(\lambda_B\circ b)\circ c_M$. Taking $M=VGB$ and
$b=1$ proves
$$\epsilon_{h,B}\circ H(\lambda_B)\circ c_{VGB}=\epsilon_{f,B}\circ F(e_{GB}).$$
This is exactly the claimed composite-counit identity after identifying the right adjoints; it is
not a choice of counit on isomorphic functors. Naturality of $c$ then gives the same identity
after precomposition by $FE(b)$ for every $b$.

3. Let $Q(B,M):E(VB\otimes M)\xrightarrow{\sim}B\otimes EM$ be the sum-extension tensor map of
[lem-asd-etale-sum-extension-tensor]. Clause (2) of [lem-pur-etale-support-map-compatibility] says
that the compactification projection for $u$ becomes the sum-extension projection under its
canonical proper-support comparison. Its specified component sends $(s,m)\otimes b$ to
$(s,m\otimes s^*b)$; after the tensor symmetries and inversion this is $Q(B,M)$. The
proper-support comparison is the same one as [lem-asd-etale-compact-support-normalization]: both
send a proper-support section to its sheet components, with inverse given by its graph sections.
Thus the inverse-projection identity in [lem-amb-shriek-tensor-composition], for the pair $(u,f)$
(both compactifiable: $f$ by hypothesis, $u$ by [thm-nagata-compactification] as in step 2) and
this normalization, gives, for every $M\in D(U_{\mathrm{et}},A)$,
$$q_h(K,M)\circ c_{h^*K\otimes M}=(1_K\otimes c_M)\circ q_f(K,EM)\circ F(Q(f^*K,M)).$$
Here $h^*K=Vf^*K$ by the canonical pullback-composition identification. This equation specifies
all occurrences of $c$ below; it is an identity of actual transformations, not just the existence
of isomorphic objects.

4. Put $W=GA_S=\omega_f$, $B=f^*K$, $N=B\otimes W$, and $D=VB\otimes VW$. Let
$\theta:D\xrightarrow{\sim}VN$ be the inverse-image tensor comparison; its naturality is part of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Apply the counit identity in
[lem-asd-etale-sum-extension-tensor] to $(B,W)$. With $Q=Q(B,VW)$ it says exactly
$$e_N\circ E(\theta)=(1_B\otimes e_W)\circ Q:E(D)\longrightarrow N.$$
In particular this is the fold/evaluation counit, rather than the counit of $u^*\dashv Ru_*$. The
coefficient objects $B,W$ are arbitrary complexes, as required by that cited statement.

5. Abbreviate $\alpha_{f,K}$ by $a:N\to GK$. By its defining transpose,
$$\epsilon_{f,K}\circ F(a)=(1_K\otimes\epsilon_{f,A_S})\circ q_f(K,W).$$
Using step 2 and naturality of $c$, the $H\dashv h^\times$-transpose of $\lambda_K\circ
V(a)\circ\theta:D\to h^\times K$, precomposed with $c_D$, is
$$\epsilon_{f,K}\circ F(e_{GK})\circ FE(V(a))\circ FE(\theta).$$
Naturality of $e$ at $a:N\to GK$ rewrites $e_{GK}\circ EV(a)=a\circ e_N$. Substitute step 4 into
this expression. The resulting transpose is
$$\epsilon_{f,K}\circ F(a)\circ F(1_B\otimes e_W)\circ F(Q).$$
These are simply the formula for the Hom bijection, functoriality, and the naturality square for
its counit, with all domains fixed in step 4.

6. Insert the defining equation for $a$ from step 5. Naturality of the inverse projection $q_f$ at
$e_W:EVW\to W$ gives
$$q_f(K,W)\circ F(1_B\otimes e_W)=(1_K\otimes F(e_W))\circ q_f(K,EVW).$$
Bifunctoriality of tensor therefore makes the transpose computed in step 5 equal to
$$(1_K\otimes[\epsilon_{f,A_S}\circ F(e_W)])\circ q_f(K,EVW)\circ F(Q).$$
Finally apply step 3 with $M=VW$ to rewrite this as
$$T=(1_K\otimes[\epsilon_{f,A_S}\circ F(e_W)])\circ(1_K\otimes c_{VW}^{-1})\circ q_h(K,VW)\circ
c_D:FE(D)\to K.$$
The projection naturality used here is the naturality of the maps in
[lem-amb-shriek-tensor-composition] and of their inverses, not an additional projection formula.

7. The other map is $\alpha_{h,K}\circ(1_{h^*K}\otimes\lambda_{A_S}):D\to h^\times K$. Its
transpose, by the definition of $\alpha_{h,K}$ and naturality of $q_h$ in the coefficient object,
is
$$(1_K\otimes[\epsilon_{h,A_S}\circ H(\lambda_{A_S})])\circ q_h(K,VW).$$
Precompose with $c_D$ and use the counit equation of step 2 at $B=A_S$, namely
$$\epsilon_{h,A_S}\circ H(\lambda_{A_S})=[\epsilon_{f,A_S}\circ F(e_W)]\circ c_{VW}^{-1}.$$
This gives exactly $T$ from step 6. Since $c_D$ is invertible, the two transposes are equal; since
the adjunction in [thm-amb-etale-exceptional-adjoint] is a Hom bijection, the two original maps
are equal. Removing $\theta$ by the canonical source identification gives the equality in the
statement. Every projection, comparison and adjunction used above was stated on entire ordinary
unbounded derived categories over finite $A$, so the calculation applies to every unbounded $K$
without any smoothness, invertibility-of-exponent, constructibility or Tor-amplitude assumption.
-/
theorem tensorMateEtalePrecomp
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{v}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (u ≫ f)] [LocallyOfFiniteType (u ≫ f)] [QuasiCompact (u ≫ f)]
    [HasCompactification f] [HasCompactification (u ≫ f)] :
    (∀ K : DerivedCategoryModule A S,
      (etaleSumExtensionTensorPullbackIso A u
        ((f)^*[ModuleCat A].mapDerivedCategory.obj K)
        (R(f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))).hom ≫
        (u)^*[ModuleCat A].mapDerivedCategory.map
          ((rightDerivedUpperShriekAdjunction (ModuleCat A) (f)).homEquiv _ K
            (R(f)_![ModuleCat A].map
                (((derivedTensor (ModuleCat A) X).map
                  ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) (f)).inv.app K)).app
                    (R(f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              R(f)_![ModuleCat A].map
                (((derivedTensorSymmetry (ModuleCat A) X).hom.app
                  ((f)^*[ModuleCat A].leftDerivedFunctor.obj K)).app
                    (R(f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              ((@inv _ _ _ _ (projectionMap (ModuleCat A) (f))
                (isIso_projectionMap_of_finite A (f))).app
                  (R(f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))).app K ≫
              ((derivedTensorSymmetry (ModuleCat A) S).hom.app
                (R(f)_![ModuleCat A].obj (R(f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A
                  S))))).app K ≫
              ((derivedTensor (ModuleCat A) S).obj K).map
                ((rightDerivedUpperShriekAdjunction (ModuleCat A) (f)).counit.app
                  (𝟙_ (DerivedCategoryModule A S))) ≫
              (derivedTensorRightUnitor (ModuleCat A) S K).hom)) ≫
        (tensorMateEtalePrecompLocalityIso A N u f).hom.app K =
      ((derivedTensor (ModuleCat A) U).map
        ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app
          ((u)^*[ModuleCat A].mapDerivedCategory.obj (R(f)^![ModuleCat A].obj (𝟙_
            (DerivedCategoryModule A S)))) ≫
        ((derivedTensor (ModuleCat A) U).obj
          ((u ≫ f)^*[ModuleCat A].mapDerivedCategory.obj K)).map
            ((tensorMateEtalePrecompLocalityIso A N u f).hom.app
              (𝟙_ (DerivedCategoryModule A S))) ≫
        ((rightDerivedUpperShriekAdjunction (ModuleCat A) (u ≫ f)).homEquiv _ K
            (R(u ≫ f)_![ModuleCat A].map
                (((derivedTensor (ModuleCat A) U).map
                  ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) (u ≫ f)).inv.app K)).app
                    (R(u ≫ f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              R(u ≫ f)_![ModuleCat A].map
                (((derivedTensorSymmetry (ModuleCat A) U).hom.app
                  ((u ≫ f)^*[ModuleCat A].leftDerivedFunctor.obj K)).app
                    (R(u ≫ f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              ((@inv _ _ _ _ (projectionMap (ModuleCat A) (u ≫ f))
                (isIso_projectionMap_of_finite A (u ≫ f))).app
                  (R(u ≫ f)^![ModuleCat A].obj (𝟙_ (DerivedCategoryModule A S)))).app K ≫
              ((derivedTensorSymmetry (ModuleCat A) S).hom.app
                (R(u ≫ f)_![ModuleCat A].obj (R(u ≫ f)^![ModuleCat A].obj (𝟙_
                  (DerivedCategoryModule A
                          S))))).app K ≫
              ((derivedTensor (ModuleCat A) S).obj K).map
                ((rightDerivedUpperShriekAdjunction (ModuleCat A) (u ≫ f)).counit.app
                  (𝟙_ (DerivedCategoryModule A S))) ≫
              (derivedTensorRightUnitor (ModuleCat A) S K).hom))) ∧
    (∀ B : DerivedCategoryModule A S,
      (etaleAmbientLeftComparison A N u f
        (HasCompactification.compactification f)
        (HasCompactification.compactification (u ≫ f))).hom.app
          ((u)^*[ModuleCat A].mapDerivedCategory.obj (R(f)^![ModuleCat A].obj B)) ≫
        R(u ≫ f)_![ModuleCat A].map
          ((tensorMateEtalePrecompLocalityIso A N u f).hom.app B) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) (u ≫ f)).counit.app B =
      R(f)_![ModuleCat A].map
        (((etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
          inferInstance).mapDerivedCategoryAdjunction).counit.app
          (R(f)^![ModuleCat A].obj B)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app B) := by
  sorry

end AlgebraicGeometry.Etale

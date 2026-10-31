/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSumExtensionTensor
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import WeilConjectures.SmoothPurity.EtalePrecompProjection

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

private theorem conjugate_composite_counit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {V : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    {H : C ⥤ E} {J : E ⥤ C}
    (adjL : L ⊣ V) (adjF : F ⊣ G) (adjH : H ⊣ J)
    (c : L ⋙ F ≅ H) (B : E) :
    c.hom.app (V.obj (G.obj B)) ≫
        H.map (((conjugateIsoEquiv adjH (adjL.comp adjF) c).symm).hom.app B) ≫
        adjH.counit.app B =
      F.map (adjL.counit.app (G.obj B)) ≫ adjF.counit.app B := by
  change c.hom.app _ ≫
    H.map ((conjugateEquiv (adjL.comp adjF) adjH c.inv).app B) ≫ _ = _
  rw [conjugateEquiv_counit, Iso.hom_inv_id_app_assoc]
  exact Adjunction.comp_counit_app adjL adjF B

private theorem tensor_mate_calculation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (V : D ⥤ C) (F : D ⥤ E) (G : E ⥤ D)
    (H : C ⥤ E) (J : E ⥤ C)
    (adjL : L ⊣ V) (adjF : F ⊣ G) (adjH : H ⊣ J)
    (c : L ⋙ F ≅ H) (locality : G ⋙ V ⟶ J)
    (hc : ∀ B, c.hom.app (V.obj (G.obj B)) ≫
      H.map (locality.app B) ≫ adjH.counit.app B =
      F.map (adjL.counit.app (G.obj B)) ≫ adjF.counit.app B)
    (T : D ⥤ D) (U W : C ⥤ C) (S : E ⥤ E)
    (qF : T ⋙ F ⟶ F ⋙ S) (qH : W ⋙ H ⟶ H ⋙ S)
    (Q : ∀ M, L.obj (U.obj M) ⟶ T.obj (L.obj M))
    (t : U ⟶ W)
    (hprojection : ∀ M, F.map (Q M) ≫ qF.app (L.obj M) ≫ S.map (c.hom.app M) =
      c.hom.app (U.obj M) ≫ H.map (t.app M) ≫ qH.app M)
    (B K : E) (r : S.obj B ⟶ K)
    (theta : U.obj (V.obj (G.obj B)) ⟶ V.obj (T.obj (G.obj B)))
    (hfold : L.map theta ≫ adjL.counit.app (T.obj (G.obj B)) =
      Q (V.obj (G.obj B)) ≫ T.map (adjL.counit.app (G.obj B))) :
    theta ≫ V.map (adjF.homEquiv _ K
        (qF.app (G.obj B) ≫ S.map (adjF.counit.app B) ≫ r)) ≫ locality.app K =
      t.app (V.obj (G.obj B)) ≫ W.map (locality.app B) ≫
        adjH.homEquiv _ K (qH.app (J.obj B) ≫ S.map (adjH.counit.app B) ≫ r) := by
  let a := adjF.homEquiv _ K
    (qF.app (G.obj B) ≫ S.map (adjF.counit.app B) ≫ r)
  have ha : F.map a ≫ adjF.counit.app K =
      qF.app (G.obj B) ≫ S.map (adjF.counit.app B) ≫ r :=
    (adjF.homEquiv _ K).symm_apply_apply _
  apply (adjH.homEquiv _ K).symm.injective
  apply (cancel_epi (c.hom.app (U.obj (V.obj (G.obj B))))).1
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hcn := c.hom.naturality (theta ≫ V.map a)
  change F.map (L.map (theta ≫ V.map a)) ≫ c.hom.app _ =
    c.hom.app _ ≫ H.map (theta ≫ V.map a) at hcn
  have hen := adjL.counit.naturality a
  change L.map (V.map a) ≫ adjL.counit.app _ =
    adjL.counit.app _ ≫ a at hen
  have hnF := qF.naturality (adjL.counit.app (G.obj B))
  change F.map (T.map (adjL.counit.app (G.obj B))) ≫ qF.app _ =
    qF.app _ ≫ S.map (F.map (adjL.counit.app (G.obj B))) at hnF
  have hnH := qH.naturality (locality.app B)
  change H.map (W.map (locality.app B)) ≫ qH.app _ =
    qH.app _ ≫ S.map (H.map (locality.app B)) at hnH
  have hleft :
      c.hom.app (U.obj (V.obj (G.obj B))) ≫ H.map theta ≫
        H.map (V.map a) ≫ H.map (locality.app K) ≫ adjH.counit.app K =
      F.map (Q (V.obj (G.obj B))) ≫ qF.app (L.obj (V.obj (G.obj B))) ≫
        S.map (F.map (adjL.counit.app (G.obj B))) ≫
        S.map (adjF.counit.app B) ≫ r := by
    rw [← H.map_comp_assoc, ← reassoc_of% hcn, hc K]
    simp only [Functor.map_comp, Category.assoc]
    have hfhen := congrArg F.map hen
    simp only [Functor.map_comp] at hfhen
    rw [reassoc_of% hfhen, ha]
    have hffold := congrArg F.map hfold
    simp only [Functor.map_comp] at hffold
    rw [reassoc_of% hffold, reassoc_of% hnF]
  have hb : H.map (adjH.homEquiv _ K
        (qH.app (J.obj B) ≫ S.map (adjH.counit.app B) ≫ r)) ≫
      adjH.counit.app K = qH.app (J.obj B) ≫ S.map (adjH.counit.app B) ≫ r :=
    (adjH.homEquiv _ K).symm_apply_apply _
  rw [hleft, hb, reassoc_of% hnH]
  rw [← S.map_comp_assoc, ← hc B, S.map_comp, S.map_comp]
  rw [← reassoc_of% hprojection]
  simp only [Category.assoc]

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
    R(f)^![A] ⋙ (u)^*[ModuleCat A].mapDerivedCategory ≅
      R(u ≫ f)^![A] :=
  ((conjugateIsoEquiv
    (rightDerivedUpperShriekAdjunction A (u ≫ f))
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
          inferInstance).mapDerivedCategoryAdjunction).comp
      (rightDerivedUpperShriekAdjunction A f)))
    (etaleAmbientLeftComparison A N u f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (u ≫ f)))).symm

set_option maxRecDepth 4096 in
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
        (R(f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))).hom ≫
        (u)^*[ModuleCat A].mapDerivedCategory.map
          ((rightDerivedUpperShriekAdjunction A (f)).homEquiv _ K
            (R(f)_![ModuleCat A].map
                (((derivedTensor (ModuleCat A) X).map
                  ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) (f)).inv.app K)).app
                    (R(f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              R(f)_![ModuleCat A].map
                (((derivedTensorSymmetry (ModuleCat A) X).hom.app
                  ((f)^*[ModuleCat A].leftDerivedFunctor.obj K)).app
                    (R(f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              ((@inv _ _ _ _ (projectionMap (ModuleCat A) (f))
                (isIso_projectionMap_of_finite A (f))).app
                  (R(f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))).app K ≫
              ((derivedTensorSymmetry (ModuleCat A) S).hom.app
                (R(f)_![ModuleCat A].obj (R(f)^![A].obj (𝟙_ (DerivedCategoryModule A
                  S))))).app K ≫
              ((derivedTensor (ModuleCat A) S).obj K).map
                ((rightDerivedUpperShriekAdjunction A (f)).counit.app
                  (𝟙_ (DerivedCategoryModule A S))) ≫
              (derivedTensorRightUnitor (ModuleCat A) S K).hom)) ≫
        (tensorMateEtalePrecompLocalityIso A N u f).hom.app K =
      ((derivedTensor (ModuleCat A) U).map
        ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app
          ((u)^*[ModuleCat A].mapDerivedCategory.obj (R(f)^![A].obj (𝟙_
            (DerivedCategoryModule A S)))) ≫
        ((derivedTensor (ModuleCat A) U).obj
          ((u ≫ f)^*[ModuleCat A].mapDerivedCategory.obj K)).map
            ((tensorMateEtalePrecompLocalityIso A N u f).hom.app
              (𝟙_ (DerivedCategoryModule A S))) ≫
        ((rightDerivedUpperShriekAdjunction A (u ≫ f)).homEquiv _ K
            (R(u ≫ f)_![ModuleCat A].map
                (((derivedTensor (ModuleCat A) U).map
                  ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) (u ≫ f)).inv.app K)).app
                    (R(u ≫ f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              R(u ≫ f)_![ModuleCat A].map
                (((derivedTensorSymmetry (ModuleCat A) U).hom.app
                  ((u ≫ f)^*[ModuleCat A].leftDerivedFunctor.obj K)).app
                    (R(u ≫ f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))) ≫
              ((@inv _ _ _ _ (projectionMap (ModuleCat A) (u ≫ f))
                (isIso_projectionMap_of_finite A (u ≫ f))).app
                  (R(u ≫ f)^![A].obj (𝟙_ (DerivedCategoryModule A S)))).app K ≫
              ((derivedTensorSymmetry (ModuleCat A) S).hom.app
                (R(u ≫ f)_![ModuleCat A].obj (R(u ≫ f)^![A].obj (𝟙_
                  (DerivedCategoryModule A
                          S))))).app K ≫
              ((derivedTensor (ModuleCat A) S).obj K).map
                ((rightDerivedUpperShriekAdjunction A (u ≫ f)).counit.app
                  (𝟙_ (DerivedCategoryModule A S))) ≫
              (derivedTensorRightUnitor (ModuleCat A) S K).hom))) ∧
    (∀ B : DerivedCategoryModule A S,
      (etaleAmbientLeftComparison A N u f
        (HasCompactification.compactification f)
        (HasCompactification.compactification (u ≫ f))).hom.app
          ((u)^*[ModuleCat A].mapDerivedCategory.obj (R(f)^![A].obj B)) ≫
        R(u ≫ f)_![ModuleCat A].map
          ((tensorMateEtalePrecompLocalityIso A N u f).hom.app B) ≫
        (rightDerivedUpperShriekAdjunction A (u ≫ f)).counit.app B =
      R(f)_![ModuleCat A].map
        (((etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
          inferInstance).mapDerivedCategoryAdjunction).counit.app
          (R(f)^![A].obj B)) ≫
        (rightDerivedUpperShriekAdjunction A f).counit.app B) := by
  let L := (etaleLowerShriek (ModuleCat A) u inferInstance).mapDerivedCategory
  let V := (u)^*[ModuleCat A].mapDerivedCategory
  let F := R(f)_![ModuleCat A]
  let G := R(f)^![A]
  let H := R(u ≫ f)_![ModuleCat A]
  let J := R(u ≫ f)^![A]
  let adjL : L ⊣ V := (etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
    inferInstance).mapDerivedCategoryAdjunction
  let adjF : F ⊣ G := rightDerivedUpperShriekAdjunction A f
  let adjH : H ⊣ J := rightDerivedUpperShriekAdjunction A (u ≫ f)
  let c : L ⋙ F ≅ H := etaleAmbientLeftComparison A N u f
    (HasCompactification.compactification f)
    (HasCompactification.compactification (u ≫ f))
  let locality : G ⋙ V ⟶ J := (tensorMateEtalePrecompLocalityIso A N u f).hom
  have hc (B : DerivedCategoryModule A S) :
      c.hom.app (V.obj (G.obj B)) ≫ H.map (locality.app B) ≫ adjH.counit.app B =
        F.map (adjL.counit.app (G.obj B)) ≫ adjF.counit.app B :=
    conjugate_composite_counit adjL adjF adjH c B
  refine ⟨?_, hc⟩
  intro K
  let B := (f)^*[ModuleCat A].mapDerivedCategory.obj K
  let T := (derivedTensor (ModuleCat A) X).obj B
  let UP := (derivedTensor (ModuleCat A) U).obj (V.obj B)
  let WP := (derivedTensor (ModuleCat A) U).obj
    ((u ≫ f)^*[ModuleCat A].mapDerivedCategory.obj K)
  let SK := (derivedTensor (ModuleCat A) S).obj K
  let unitS := 𝟙_ (DerivedCategoryModule A S)
  have hfold := ((isIso_etaleSumExtensionTensorComparison A u B
    (V.obj (G.obj unitS))).2 (G.obj unitS)).symm
  have calculation := tensor_mate_calculation L V F G H J adjL adjF adjH c locality hc
    T UP WP SK (tensorMateInverseProjection A f K)
    (tensorMateInverseProjection A (u ≫ f) K)
    (fun M ↦ etaleSumExtensionTensorComparison A u B M)
    ((derivedTensor (ModuleCat A) U).map
      ((unboundedEtaleUpperStarCompIso A u f).inv.app K))
    (fun M ↦ etalePrecompProjection A N u f K M)
    unitS K (derivedTensorRightUnitor (ModuleCat A) S K).hom
    (etaleSumExtensionTensorPullbackIso A u B (G.obj unitS)).hom hfold
  simpa only [tensorMateInverseProjection, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, evaluation_obj_map, flipFunctor_map_app_app,
    Category.assoc] using calculation

end AlgebraicGeometry.Etale

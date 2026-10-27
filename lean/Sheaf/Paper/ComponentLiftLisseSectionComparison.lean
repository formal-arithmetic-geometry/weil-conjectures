/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.ComponentLiftSectionDefs
import Sheaf.Paper.ComponentLiftGeometricComparisons
import Sheaf.Paper.ComponentLiftFiniteFreeDuality
import Sheaf.Paper.ComponentLiftSectionNormalization
import Sheaf.AlgebraicGeometry.LisseModuleInverseImage
import Mathlib.CategoryTheory.HomCongr

/-! # Unit-normalized lisse section comparison for component lifts

Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.1 and Proposition 4.3(3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem parametrization_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} {A B : D} (a : A ≅ F.obj M) (b : F.obj N ≅ B)
    (h : Function.Bijective (fun f : M ⟶ N ↦ F.map f)) :
    Function.Bijective (fun f : M ⟶ N ↦ a.hom ≫ F.map f ≫ b.hom) := by
  exact (Iso.homCongr a.symm b).bijective.comp h

private theorem normalized_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (c : F ⋙ G ≅ H) [NatTrans.IsMonoidal c.hom]
    {N : C} {A : D} (a : F.obj N ≅ A) (b : 𝟙_ C ⟶ N) :
    (Functor.Monoidal.εIso G).hom ≫
        G.map ((Functor.Monoidal.εIso F).hom ≫ F.map b ≫ a.hom) =
      (Functor.Monoidal.εIso H).hom ≫ H.map b ≫
        (c.app N).inv ≫ G.map a.hom := by
  have hu := NatTrans.IsMonoidal.unit (τ := c.inv)
  simp only [Functor.LaxMonoidal.comp_ε] at hu
  simp only [Functor.map_comp, Functor.Monoidal.εIso_hom]
  rw [← Category.assoc, ← hu]
  have hn : c.inv.app (𝟙_ C) ≫ G.map (F.map b) =
      H.map b ≫ (c.app N).inv := (c.inv.naturality b).symm
  simpa only [Category.assoc] using
    congrArg (fun f ↦ Functor.LaxMonoidal.ε H ≫ f ≫ G.map a.hom) hn

private theorem component_hom_identity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (g : V ⟶ U)
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV) (hc : ComponentLiftMonoidal mU mV c) :
    ComponentLiftHomIdentity Λ g dU dV mU mV c := by
  let := mU
  let := mV
  let : (moduleObjectDerivedPullback Λ.X g).Monoidal := monoidal_leftDerivedUpperStar Λ.X g
  let : NatTrans.IsMonoidal c.hom := hc
  intro N _ L _ a b
  exact normalized_naturality _ _ _ c a b

private theorem component_sections_bijective
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (g : V ⟶ U)
    {S : Profinite.{u}} {eU : affineComponentSpace U ≃ₜ S}
    {eV : affineComponentSpace V ≃ₜ S}
    (dU : ComponentLiftCoefficient Λ S U eU) (dV : ComponentLiftCoefficient Λ S V eV)
    (mU : (componentLiftDerived dU).Monoidal) (mV : (componentLiftDerived dV).Monoidal)
    (c : componentLiftDerived dU ⋙ moduleObjectDerivedPullback Λ.X g ≅
      componentLiftDerived dV)
    (hU : ComponentLiftEquivalence dU) (hV : ComponentLiftEquivalence dV)
    (hc : ComponentLiftHomIdentity Λ g dU dV mU mV c)
    (hs : ComponentLiftSectionIdentity Λ g)
    (L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
    (hL : IsLisseCoefficientModule Λ.X L) (hdual : ComponentLiftLisseFacts Λ U L)
    (heU : Function.Bijective (componentLiftHomSection Λ U L))
    (heV : Function.Bijective
      (componentLiftHomSection Λ V ((upperStar Λ.X g).obj L))) :
    Function.Bijective (componentLiftSectionPullback Λ g L) := by
  let := mU
  let := mV
  obtain ⟨P, _, _, _, _, ⟨pair⟩⟩ := hdual
  have hDL : IsDualizable ((DerivedCategory.singleFunctor _ 0).obj L) :=
    ⟨{ rightDual := (DerivedCategory.singleFunctor _ 0).obj P, exact := pair }⟩
  obtain ⟨N, hN, ⟨a⟩⟩ := hU.2.2 _ hDL
  let F := componentLiftDerived dU
  let H := componentLiftDerived dV
  let G := moduleObjectDerivedPullback Λ.X g
  let z := (Functor.singleFunctorCompLeftDerivedFunctorIso (upperStar Λ.X g)).app L
  let bV : H.obj N ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((upperStar Λ.X g).obj L) := (c.app N).symm ≪≫ G.mapIso a ≪≫ z
  let pU := fun b : 𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ.X S)) ⟶ N ↦
    (Functor.Monoidal.εIso F).hom ≫ F.map b ≫ a.hom
  let pV := fun b : 𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over S)
      (profiniteCoefficient Λ.X S)) ⟶ N ↦
    (Functor.Monoidal.εIso H).hom ≫ H.map b ≫ bV.hom
  have hpU : Function.Bijective pU := parametrization_bijective F
    (Functor.Monoidal.εIso F) a (hU.1 _ N isDualizable_unit hN)
  have hpV : Function.Bijective pV := parametrization_bijective H
    (Functor.Monoidal.εIso H) bV (hV.1 _ N isDualizable_unit hN)
  have hcomm : componentLiftSectionPullback Λ g L ∘
      (componentLiftHomSection Λ U L ∘ pU) =
      componentLiftHomSection Λ V ((upperStar Λ.X g).obj L) ∘ pV := by
    funext b
    rw [Function.comp_apply, Function.comp_apply, ← hs L (pU b)]
    apply congrArg (componentLiftHomSection Λ V ((upperStar Λ.X g).obj L))
    dsimp only [pU, pV, bV, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, hc N hN L hL a b]
    simp only [Category.assoc]
    rfl
  apply (Function.Bijective.of_comp_iff _ (heU.comp hpU)).mp
  rw [hcomm]
  exact heV.comp hpV

/-- Unit-normalized component pullback, local finite-free duality, and actual section
comparison, for arbitrary commutative condensed coefficients.

Source: HRS Definition 3.3, Lemma 4.1, Proposition 4.3(3), (4.1)--(4.2);
Stacks 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-component-lift-lisse-section-comparison).

Proof for stage 3 (the seven steps of the node).
1. For a finite clopen subdivision $S_i\to S$, the inverse image of each clopen part of $U$ under
   $g$ is the corresponding part of $V$, because $\pi_0(g)=1_S$. Thus $V\times_U(U\times_S S_i)$
   is the indicated disjoint union of clopen parts of $V$. Pass to the defining affine limits for
   $E=\varprojlim_i S_i$. Explicitly, a map from a scheme $W$ to $V\times_U\varprojlim_i(U\times_S
   S_i)$ is a map $W\to V$ and a compatible family of maps to $U\times_S S_i$ with that composite
   to $U$; this is precisely a compatible family of maps to $V\times_S S_i$. The two universal
   properties give the claimed projection-preserving isomorphism. The same description shows
   naturality in $E$, and for a second morphism $h$ both successive and direct comparisons have
   the same projections, hence agree. The component-site construction therefore gives $\pi_U\circ
   g\cong\pi_V$. Its coefficient maps agree since each is pulled back from the condensed point.
   Apply the ringed-derived monoidal comparisons to this specified 2-isomorphism: it gives
   $c:g^*\pi_U^*\cong\pi_V^*$, preserving the coefficient unit and composition. Uses:
   lem-zl-component-relative-profinite-site, lem-sfb-ringed-derived-monoidal-comparisons.
2. The coefficient isomorphism $\alpha_g$ exists for arbitrary condensed $\Lambda$ by
   [lem-sfb-alpha-iso]. The module pullback formula is
   $\Lambda_V\otimes_{g^{-1}\Lambda_U}g^{-1}(-)$, so along this isomorphism its underlying functor
   is $g^{-1}$, which is exact by [lem-sfb-finite-upper-star-exact]. Consequently the derived
   pullback of a degree-zero module is its ordinary pullback in degree zero. Pull back a
   trivializing pro-etale covering $\{u_i:U_i\to U\}$ for $L$. Base change is the functor defining
   scheme inverse image on these sites, and its base-changed covering $\{v_i:V_i=V\times_UU_i\to
   V\}$ is a covering; let $g_i:V_i\to U_i$ be the projection. By
   [lem-sfb-coefficient-sections-localization], restriction to the slice at $V_i$ (resp. $U_i$) is
   the inverse image $v_i^*$ (resp. $u_i^*$), compatibly with the coefficient isomorphisms. The
   composition isomorphisms of module pullback [sk-def-sfb-module-pushforward-pullback] applied to
   $gv_i=u_ig_i$ give $(g^*L)|_{V_i}\cong g_i^*(L|_{U_i})\cong g_i^*(\Lambda_{U_i}^{r_i})$. The
   latter is $\Lambda_{V_i}^{r_i}$, since $g_i^*$ is additive and sends the regular module to the
   regular module by the tensor formula and the coefficient isomorphism. Hence $g^*L$ satisfies
   the same lisse definition, including varying ranks. Uses: lem-sfb-alpha-iso,
   def-sfb-module-upper-star, lem-sfb-finite-upper-star-exact, def-sfb-finite-upper-star,
   def-sfb-lisse-coefficient-module, lem-sfb-coefficient-sections-localization,
   sk-def-sfb-module-pushforward-pullback.
3. For either $T=U,V$ and the corresponding module $P=L,g^*L$, put $P^\vee=\mathcal
   Hom_{\Lambda_T}(P,\Lambda_T)$. On a trivializing slice the defining sheaf Hom is the finite
   coordinate dual of $\Lambda_T^{r_i}$, hence $P^\vee$ is locally finite free. The finite-free
   tensor-exactness theorem applies to both $P$ and $P^\vee$, with coefficient the commutative
   internal ring $\Lambda_T$. Their tensor functors preserve finite limits, hence kernels. They
   also preserve cokernels: the tensor universal property identifies maps out of the cokernel
   tensor with balanced bilinear maps vanishing on the given image. Thus they are exact, i.e. $P$
   and $P^\vee$ are flat [def-pc-flat-sheaf-modules]. For every acyclic complex $A$, degreewise
   exactness gives $H^n(A\otimes P)=H^n(A)\otimes P=0$, and likewise for $P^\vee$. By the
   definition of total tensor with a degree-zero complex this proves K-flatness of both
   degree-zero complexes. So both degree-zero complexes are K-flat with flat terms, as are their
   finite tensor products and $\Lambda_T[0]$ (locally finite free again), and the K-flat tensor
   comparison therefore computes their derived tensor by the ordinary module tensor. Uses:
   def-pur-sheaf-hom, lem-weil-pbc-condensed-finite-free-tensor-exact,
   def-pur-sheaf-tensor-product, def-pc-kflat-complex, lem-weil-pbc-site-derived-tensor-descent,
   def-pc-flat-sheaf-modules.
4. Evaluation is $\phi\otimes x\mapsto\phi(x)$. On each free slice, with basis $e_1,\ldots,e_r$
   and coordinate dual $e_i^*$, define coevaluation by $1\mapsto\sum_i e_i\otimes e_i^*$. This
   tensor is independent of the trivialization: if $f_j=\sum_i e_i a_{ij}$ and the inverse
   transition has coefficients $b_{ji}$, then $f_j^*=\sum_k b_{jk}e_k^*$ and the coefficient of
   $e_i\otimes e_k^*$ in $\sum_j f_j\otimes f_j^*$ is $\sum_j a_{ij}b_{jk}=\delta_{ik}$. This also
   covers rectangular mutually inverse transition matrices. Therefore these local module maps
   agree on overlaps and glue, since the Hom presheaf is a sheaf. The two triangle composites send
   $x$ to $\sum_i e_i e_i^*(x)=x$ and $\phi$ to $\sum_i\phi(e_i)e_i^*=\phi$. Equality of sheaf
   maps is local, so both identities hold globally. Step 3 computes the derived tensor by these
   degree-zero tensors. Localization thus carries these maps and identities to the ordinary
   derived category, proving dualizability with the displayed locally finite free dual. For $r=0$
   all sums are empty and both identities are identities of the zero object. Uses:
   def-pur-sheaf-hom, def-pur-sheaf-tensor-product, lem-weil-pbc-site-derived-tensor-descent.
5. Write $F_T=\pi_T^*$ on dualizable objects, $e_T:F_T\Lambda_S[0]\xrightarrow{\sim}\Lambda_T[0]$
   for its unit comparison, and fix $a:F_UN\xrightarrow{\sim}L[0]$. By the component equivalence
   and step 4, such an $N,a$ exists. Full faithfulness identifies a morphism $b:\Lambda_S[0]\to N$
   with $aF_U(b)e_U^{-1}$. Use the isomorphism $g^*a$ followed by $c_N^{-1}$ to identify $F_VN$
   with $g^*L[0]$. The actual pullback of $aF_U(b)e_U^{-1}$, precomposed with the inverse
   coefficient-unit comparison for $g^*$, becomes $F_V(b)e_V^{-1}$ under this identification: this
   is exactly $c_N\,g^*F_U(b)=F_V(b)c_{\Lambda_S[0]}$ and the unit equation for the monoidal $c$
   from step 1. Thus it corresponds to the same $b$. This proves the asserted identity on Hom and
   its bijectivity, for every choice of $N,a$. Uses:
   lem-zl-condensed-wcontractible-lisse-evaluation, lem-sfb-ringed-derived-monoidal-comparisons.
6. The fully faithful degree-zero embedding identifies each derived Hom in the statement with
   ordinary module Hom. A module map $t:\Lambda_T\to P$ is determined by $s=t_T(1)$: for any site
   object $W\to T$, it sends $r\in\Lambda_T(W)$ to $r\,s|_W$. Conversely this formula defines a
   module map for every $s\in P(T)$ and commutes with restrictions, so it is inverse to evaluation
   on $1$. For $s\in L(U)$ the adjunction unit sends $s$ to its section pullback $s'$ in
   $g^*L(V)$. Naturality of that unit with respect to $t_s$, and the mate relation for the
   coefficient map, identify the adjoint of $g^*t_s$ with the composite of $t_s$ and this unit;
   evaluating at $1$ gives $s'$. Thus the actual derived Hom map of step 5 is precisely the
   specified section map, not merely an abstract bijection. Its bijectivity follows from step 5.
   Uses: lem-weil-pbc-derived-single-fully-faithful, def-sfb-condensed-module-sections,
   sk-def-sfb-module-pushforward-pullback.
7. All Hom maps above are induced by functors and their specified unit comparisons. For a module
   morphism $L\to L'$, functoriality gives the commutative section square. For $W\xrightarrow
   hV\xrightarrow gU$, the adjunction unit of the composite is the unit for $g$ followed by $g_*$
   of the unit for $h$; the adjunction-compatible derived comparison identifies this with
   successive pullback. Step 1 already proves the same composition identity for the component
   comparison. Consequently the resulting section bijections preserve composition and identities.
   If $S$ is empty then $U,V$ are empty and their section groups are zero; the formulas still
   apply. No step uses discreteness, completeness or t-admissibility of $\Lambda$, connectedness,
   positive rank, or a fixed rank. Uses: lem-sfb-ringed-derived-monoidal-comparisons,
   sk-def-sfb-module-pushforward-pullback, def-sfb-condensed-module-sections. -/
theorem component_lift_lisse_section_comparison
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) [ExtremallyDisconnected S] :
    ∃ d : ∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
        (e : affineComponentSpace T ≃ₜ S), ComponentLiftCoefficient Λ S T e,
      ∃ m : ∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
          (e : affineComponentSpace T ≃ₜ S), (componentLiftDerived (d T e)).Monoidal,
        ∃ c : ∀ (U V : Scheme.{u}) [IsAffine U] [IsAffine V]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (g : V ⟶ U), IsComponentLiftMap eU eV g →
            ((componentLiftDerived (d U eU) ⋙ moduleObjectDerivedPullback Λ.X g) ≅
              componentLiftDerived (d V eV)),
          (∀ (U V : Scheme.{u}) [IsAffine U] [IsAffine V]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (g : V ⟶ U) (hg : IsComponentLiftMap eU eV g),
            (∃ k : componentLiftTests V S eV ≅ componentLiftTests U S eU ⋙
                MorphismProperty.Over.pullback @WeaklyEtale ⊤ g,
              (∀ (E : Over S) (v : ((componentLiftTests V S eV).obj E).left),
                (d U eU).projection E
                  (pullback.fst ((componentLiftTests U S eU).obj E).hom g
                    ((k.app E).hom.left v)) = (d V eV).projection E v) ∧
              ∃ q : componentLiftModules (d U eU) ⋙ upperStar Λ.X g ≅
                  componentLiftModules (d V eV),
                ComponentLiftInducedComparison (d U eU) (d V eV) g k q ∧
                c U V eU eV g hg =
                  componentLiftDerivedComparison (d U eU) (d V eV) g q) ∧
            ComponentLiftMonoidal (m U eU) (m V eV) (c U V eU eV g hg) ∧
            ComponentLiftHomIdentity Λ g (d U eU) (d V eV) (m U eU) (m V eV)
              (c U V eU eV g hg) ∧
            ComponentLiftSectionIdentity Λ g ∧ ComponentLiftSectionNaturality Λ g ∧
            ∀ L : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U),
              IsLisseCoefficientModule Λ.X L →
                IsLisseCoefficientModule Λ.X ((upperStar Λ.X g).obj L) ∧
                ComponentLiftLisseFacts Λ U L ∧
                ComponentLiftLisseFacts Λ V ((upperStar Λ.X g).obj L) ∧
                Function.Bijective (componentLiftSectionPullback Λ g L) ∧
                Function.Bijective (componentLiftHomSection Λ U L) ∧
                Function.Bijective (componentLiftHomSection Λ V ((upperStar Λ.X g).obj L))) ∧
          (∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
            (e : affineComponentSpace T ≃ₜ S), ComponentLiftEquivalence (d T e) ∧
            ∀ (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
              (s : (condensedModuleSections Λ.X T).obj L),
              (condensedModuleSections Λ.X T).map ((upperStarId Λ.X T).hom.app L)
                ((componentLiftSectionPullback Λ (𝟙 T) L) s) = s) ∧
          (∀ (U V W : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine W]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            [IsWContractibleRing Γ(W, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (eW : affineComponentSpace W ≃ₜ S) (g : V ⟶ U) (h : W ⟶ V)
            (hg : IsComponentLiftMap eU eV g) (hh : IsComponentLiftMap eV eW h)
            (hc : IsComponentLiftMap eU eW (h ≫ g))
            (N : Evaluation.D ((coherentTopology Profinite.{u}).over S)
              (profiniteCoefficient Λ.X S)),
            (leftDerivedUpperStarComp Λ.X h g).hom.app ((componentLiftDerived (d U eU)).obj N) ≫
              (moduleObjectDerivedPullback Λ.X h).map ((c U V eU eV g hg).hom.app N) ≫
              (c V W eV eW h hh).hom.app N = (c U W eU eW (h ≫ g) hc).hom.app N ∧
            ComponentLiftSectionComposition Λ g h)
    := by
  obtain ⟨d, m, c, hmaps, hequiv, hcomp⟩ := component_lift_geometric_comparisons Λ S
  obtain ⟨hsections, heval, hid, hseccomp⟩ := component_lift_section_normalization Λ
  refine ⟨d, m, c, ?_, ?_, ?_⟩
  · intro U V _ _ _ _ eU eV g hg
    obtain ⟨htests, hmon⟩ := hmaps U V eU eV g hg
    have hhom := component_hom_identity Λ g (d U eU) (d V eV)
      (m U eU) (m V eV) (c U V eU eV g hg) hmon
    refine ⟨htests, hmon, hhom, (hsections U V g).1, (hsections U V g).2, ?_⟩
    intro L hL
    have hp := isLisseCoefficientModule_upperStar Λ g L hL
    have hdual := component_lift_finite_free_duality Λ U L hL
    exact ⟨hp, hdual,
      component_lift_finite_free_duality Λ V ((upperStar Λ.X g).obj L) hp,
      component_sections_bijective Λ g (d U eU) (d V eV) (m U eU) (m V eV)
        (c U V eU eV g hg) (hequiv U eU) (hequiv V eV) hhom (hsections U V g).1
        L hL hdual (heval U L) (heval V ((upperStar Λ.X g).obj L)),
      heval U L, heval V ((upperStar Λ.X g).obj L)⟩
  · intro T _ _ e
    exact ⟨hequiv T e, hid T⟩
  · intro U V W _ _ _ _ _ _ eU eV eW g h hg hh hc N
    exact ⟨hcomp U V W eU eV eW g h hg hh hc N, hseccomp U V W g h⟩

end AlgebraicGeometry.ProEtale.CondensedRing


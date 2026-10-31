/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.DiagramSiteTopology
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # Constant coefficients and derived adjunctions on strict pro-etale towers

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Derived Categories,
Tags 070H, 070K, 070Y and 0DVC; the strict diagram-site refinement of the blueprint
(blueprint: lem-cbc-tower-adjunction-realization).

All tower categories and operations are the recorded constant-coefficient operations.
The index `n : ℕ` represents positive level `n + 1`. Complexes are unbounded complexes
in the category of strict towers. The small site model retains object universe `u+1`
and transports the original Hom universe `u`, without imposing an equality of them.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

universe w

/-- The vertical coefficient sheaf for a small index and a larger site. -/
private abbrev towerDiagramRing
    (J : Type) (C : Type w) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    Sheaf (verticalDiagramSiteTopology Jᵒᵖ C K) RingCat.{w} where
  obj := (CategoryTheory.Prod.snd Jᵒᵖ C).op ⋙ O.obj
  property := (verticalDiagramSite_isSheaf_iff Jᵒᵖ C K _).2 (fun _ ↦ O.property)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a product module to a vertical component. -/
private noncomputable def towerDiagramModuleComponent
    (J : Type) (C : Type w) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : ringedSiteModules.{w} (towerDiagramRing J C K O)) (j : J) :
    ringedSiteModules.{w} O where
  val := PresheafOfModules.pushforward₀Obj (Prod.sectR (op j) C)
    (towerDiagramRing J C K O).obj F.val
  isSheaf := (verticalDiagramSite_isSheaf_iff Jᵒᵖ C K F.val.presheaf).1 F.isSheaf (op j)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unnecessarySimpa false in
/-- Horizontal structure map on the component modules. -/
private noncomputable def towerDiagramModuleArrow
    {J : Type} {C : Type w} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : ringedSiteModules.{w} (towerDiagramRing J C K O))
    {j k : J} (a : j ⟶ k) :
    towerDiagramModuleComponent J C K O F j ⟶ towerDiagramModuleComponent J C K O F k where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op
          map_add' := map_add _
          map_smul' := by
            intro r x
            have H := F.val.map_smul (Prod.mkHom a.op (𝟙 U.unop)).op r x
            simpa [towerDiagramRing, CategoryTheory.Prod.snd] using H }
      naturality := by
        intro U V f
        ext x
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
        change F.val.map (Prod.mkHom a.op (𝟙 V.unop)).op
          (F.val.map ((Prod.sectR (op j) C).op.map f) x) =
          F.val.map ((Prod.sectR (op k) C).op.map f)
            (F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op x)
        have H : ((Prod.sectR (op j) C).op.map f) ≫
            (Prod.mkHom a.op (𝟙 V.unop)).op =
            (Prod.mkHom a.op (𝟙 U.unop)).op ≫ (Prod.sectR (op k) C).op.map f := by
          apply Quiver.Hom.unop_inj
          ext <;> simp
        have HH := F.val.presheaf.congr_map H
        rw [Functor.map_comp, Functor.map_comp] at HH
        exact ConcreteCategory.congr_hom HH x }

set_option backward.isDefEq.respectTransparency false in
/-- The functor restricting module sheaves to component modules. -/
private noncomputable def towerDiagramModuleCurry
    (J : Type) (C : Type w) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    ringedSiteModules.{w} (towerDiagramRing J C K O) ⥤ J ⥤ ringedSiteModules.{w} O where
  obj F :=
    { obj j := towerDiagramModuleComponent J C K O F j
      map a := towerDiagramModuleArrow K O F a
      map_id j := by
        ext U x
        change F.val.map (𝟙 (op (op j, U.unop))) x = x
        simp
        rfl
      map_comp {j k l} a b := by
        ext U x
        change F.val.map (Prod.mkHom (a ≫ b).op (𝟙 U.unop)).op x =
          F.val.map (Prod.mkHom b.op (𝟙 U.unop)).op
            (F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op x)
        rw [← F.val.map_comp_apply]
        apply F.val.congr_map_apply
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map f :=
    { app j :=
        { val :=
            { app U := f.val.app ((Prod.sectR (op j) C).op.obj U)
              naturality a := f.val.naturality ((Prod.sectR (op j) C).op.map a) } }
      naturality := by
        intro j k a
        ext U x
        exact (PresheafOfModules.naturality_apply f.val (Prod.mkHom a.op (𝟙 U.unop)).op x) }
  map_id F := by ext j U x; rfl
  map_comp f g := by ext j U x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of presheaf modules along the two product coordinates. -/
private noncomputable def towerDiagramModuleUncurryVal
    {J : Type} {C : Type w} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : J ⥤ ringedSiteModules.{w} O) :
    PresheafOfModules.{w} (towerDiagramRing J C K O).obj where
  obj X := (F.obj X.unop.1.unop).val.obj (op X.unop.2)
  map {X Y} f := (F.map f.unop.1.unop).val.app (op X.unop.2) ≫
    (F.obj Y.unop.1.unop).val.map f.unop.2.op
  map_id X := by
    ext x
    simp [towerDiagramRing, CategoryTheory.Prod.snd]
  map_comp {X Y Z} f g := by
    ext x
    change (F.obj Z.unop.1.unop).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map (f.unop.1.unop ≫ g.unop.1.unop)).val.app (op X.unop.2)) x) =
      (F.obj Z.unop.1.unop).val.map g.unop.2.op
        (((F.map g.unop.1.unop).val.app (op Y.unop.2))
          ((F.obj Y.unop.1.unop).val.map f.unop.2.op
            (((F.map f.unop.1.unop).val.app (op X.unop.2)) x)))
    rw [F.map_comp]
    change (F.obj Z.unop.1.unop).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map g.unop.1.unop).val.app (op X.unop.2))
        (((F.map f.unop.1.unop).val.app (op X.unop.2)) x)) = _
    rw [PresheafOfModules.naturality_apply (F.map g.unop.1.unop).val]
    exact (F.obj Z.unop.1.unop).val.map_comp_apply _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of a diagram of module sheaves to a sheaf on the product site. -/
private noncomputable def towerDiagramModuleUncurryObj
    {J : Type} {C : Type w} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w})
    (F : J ⥤ ringedSiteModules.{w} O) :
    ringedSiteModules.{w} (towerDiagramRing J C K O) where
  val := towerDiagramModuleUncurryVal K O F
  isSheaf := by
    apply (verticalDiagramSite_isSheaf_iff Jᵒᵖ C K _).2
    intro j
    let e : (Prod.sectR j C).op ⋙ (towerDiagramModuleUncurryVal K O F).presheaf ≅
        (F.obj j.unop).val.presheaf :=
      NatIso.ofComponents (fun U ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (F.obj j.unop).val.map f
          (((F.map (𝟙 j.unop)).val.app U) x) = (F.obj j.unop).val.map f x
        simp)
    exact (Presheaf.isSheaf_of_iso_iff e).2 (F.obj j.unop).isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- Assembly is functorial on module morphisms. -/
private noncomputable def towerDiagramModuleUncurry
    (J : Type) (C : Type w) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    (J ⥤ ringedSiteModules.{w} O) ⥤ ringedSiteModules.{w} (towerDiagramRing J C K O) where
  obj F := towerDiagramModuleUncurryObj K O F
  map {F G} f :=
    { val :=
        { app X := (f.app X.unop.1.unop).val.app (op X.unop.2)
          naturality := by
            intro X Y a
            ext x
            change ((f.app Y.unop.1.unop).val.app (op Y.unop.2))
              (((F.obj Y.unop.1.unop).val.map a.unop.2.op)
                (((F.map a.unop.1.unop).val.app (op X.unop.2)) x)) =
              ((G.obj Y.unop.1.unop).val.map a.unop.2.op)
                (((G.map a.unop.1.unop).val.app (op X.unop.2))
                  (((f.app X.unop.1.unop).val.app (op X.unop.2)) x))
            rw [PresheafOfModules.naturality_apply (f.app Y.unop.1.unop).val]
            have H := congrArg (fun t ↦ t.val.app (op X.unop.2))
              (f.naturality a.unop.1.unop)
            exact congrArg ((G.obj Y.unop.1.unop).val.map a.unop.2.op)
              (ConcreteCategory.congr_hom H x) } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A module-sheaf isomorphism from an isomorphism of its module presheaves. -/
private def towerDiagramModuleIso {C : Type w} [SmallCategory C] {K : GrothendieckTopology C}
    {O : Sheaf K RingCat.{w}} {F G : ringedSiteModules.{w} O}
    (e : F.val ≅ G.val) : F ≅ G where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence for modules on the vertical product site. -/
private noncomputable def towerDiagramModuleEquivalence
    (J : Type) (C : Type w) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{w}) :
    ringedSiteModules.{w} (towerDiagramRing J C K O) ≌ (J ⥤ ringedSiteModules.{w} O) where
  functor := towerDiagramModuleCurry J C K O
  inverse := towerDiagramModuleUncurry J C K O
  unitIso := NatIso.ofComponents (fun F ↦ towerDiagramModuleIso
    (PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change F.val.map f x = F.val.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
        (F.val.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
      have H : f = (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op := by
        apply Quiver.Hom.unop_inj
        ext <;> simp
      exact (F.val.congr_map_apply H x).trans (F.val.map_comp_apply _ _ x)))) (by
    intro F G f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ towerDiagramModuleIso (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (F.obj j).val.map f (((F.map (𝟙 j)).val.app U) x) =
        (F.obj j).val.map f x
      simp))) (by
      intro j k a
      ext U x
      change (F.obj k).val.map (𝟙 U) (((F.map a).val.app U) x) =
        ((F.map a).val.app U) x
      simp)) (by
    intro F G f
    ext j U x
    rfl)
  functor_unitIso_comp F := by
    ext j U x
    rfl


variable (B : Type (u + 1)) [CommRing B]

/-- The actual termwise adjunction, with the whiskered module unit and counit.
Source: Stacks Project, Tag 03D7, termwise strict-tower construction
(blueprint: lem-cbc-tower-adjunction-realization). -/
noncomputable def termwiseAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    towerPullback B f ⊣ towerDirectImage B f :=
  (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ

/-- Constant-section coefficients, exact termwise adjunctions, diagram-site realization,
K-injective resolutions and preservation, and the normalized unbounded derived and open
adjunctions. There are no finiteness, transition-surjectivity or boundedness assumptions.

Source: Stacks Project, Tags 03DI, 03DJ, 070H, 070K, 070Y and 0DVC; the strict
constant-coefficient diagram-site refinement
(blueprint: lem-cbc-tower-adjunction-realization).

Proof plan (the node's eight steps):
1. Apply [lem-pur-proetale-constant-coefficient-comparison] with $A=B$: its map is precisely the
   adjunct $c_u$ defined in [def-weil-proetale-inverse-image], so it is an isomorphism even for
   infinite $B$. For a ring map $\phi:B\to C$, the maps $\rho_C^u\phi_Y$ and
   $u_*(\phi_X)\rho_B^u$ agree: on a constant presheaf section $b$ each is the constant section
   $\phi(b)$, and the sheafification universal property [def-weil-pbc-constant-sheaf] gives
   equality. Taking adjuncts proves naturality of $c_u$. For $X\xrightarrow uY\xrightarrow vZ$,
   both $c_{vu}$ and $c_u\circ u^{-1}(c_v)$, after the canonical inverse-image compositor, have
   adjunct sending $b$ to the constant section $b$ on $X\times_Y(Y\times_ZW)\cong X\times_ZW$;
   they therefore agree by the same uniqueness. For the identity this calculation sends $b$ to
   $b$, so gives the identity coefficient map. These equalities include compatibility with ring
   homomorphisms and their composites.
2. Apply [lem-weil-pbc-ringed-topoi-module-adjunction] to $R=\underline B_Y$, $S=\underline
   B_X$, and $c=c_u$. Since $c_u$ is invertible, $S\otimes_{u^{-1}R}u^{-1}M\cong u^{-1}M$ with
   action transported by $c_u^{-1}$: the maps are $s\otimes m\mapsto c_u^{-1}(s)m$ and
   $m\mapsto1\otimes m$. The underlying abelian inverse image is exact by [lem-weil-pbc-site-
   pullback-abelian-exact]; kernels and sheafified cokernels have their underlying abelian
   values by [def-weil-sheaf-of-modules-category]. Thus this module inverse image is exact.
   Apply both functors levelwise to towers. A family $a_n:u^*M_n\to N_n$ is a tower map exactly
   when its naturality equations hold for every transition. Naturality of the module adjunction
   sends those equations to the transition equations for its adjuncts $M_n\to u_*N_n$. The
   inverse Hom bijection does the reverse. This proves the tower adjunction, with levelwise unit
   and counit. Kernels and cokernels of tower maps are levelwise: a transition induces the
   unique map of the levelwise kernels or cokernels by their universal properties. Hence
   levelwise inverse image is exact.
3. In [lem-weil-pbc-diagram-site-realization] take $J=\mathbf N_{\geq1}^{op}$, $\mathcal
   C=X_{\mathrm{proet}}$ in its chosen small skeleton, and $\mathcal O=\underline B_X$. This
   gives an additive exact equivalence $\mathcal T_X\simeq\operatorname{Mod}(\mathcal
   O_{\mathcal D})$ for $\mathcal D=J^{op}\times\mathcal C$. Both factors are small in the fixed
   universe, so the product site is small. Apply [prop-pur-kinjective-resolutions-exist] to this
   ringed site. Transfer colimits, their exactness, a generator, and the resulting K-injective
   resolutions across the equivalence. Its termwise extension and inverse preserve acyclicity
   and chain homotopies, so a complex is K-injective on one side exactly when its image is
   K-injective on the other. Thus $\mathcal T_X$ is Grothendieck abelian and every unbounded
   tower complex admits such a resolution.
4. Write $L$ for tower inverse image and $F$ for tower direct image from step 2. If $I$ is a
   K-injective complex over $\mathcal T_X$ and $A$ is an acyclic complex over $\mathcal T_Y$,
   then $LA$ is acyclic by exactness. The degreewise adjunction restricts to chain maps and
   homotopies, giving $\operatorname{Hom}_{K(\mathcal
   T_Y)}(A,FI)\cong\operatorname{Hom}_{K(\mathcal T_X)}(LA,I)=0$. By the definition [def-pur-
   kinjective-complex], applied to the ringed diagram sites of step 3, $FI$ is K-injective. No
   assertion that a levelwise K-injective system is K-injective as a tower is used.
5. The additive functor $F$ induces a functor on homotopy categories, since applying $F$ to
   $a-b=dh+hd$ gives the same identity. It commutes with shifts and cones: its map on
   $C(a)^r=N^r\oplus M^{r+1}$ identifies $F(C(a))$ with $C(F(a))$, including the differential
   matrix and cone arrows. Thus $QF:K(\mathcal T_X)\to D(\mathcal T_Y)$ is triangulated. Step 3
   supplies the resolutions required by [lem-weil-pbc-kinjective-total-derived]; hence its total
   right derived functor exists everywhere and is $R_u(QK)\cong QF(I)$ for a K-injective
   resolution $K\to I$. This is the total derived termwise direct image, not merely an
   independently chosen family of levelwise derived objects. The exact functor $L$ descends to
   $G_u$ by [lem-weil-pbc-exact-functor-derived-factorization], and [lem-weil-pbc-exact-functor-
   derived-functor] identifies that descent with its total left derived functor.
6. Apply [lem-pc-pre-derived-adjoint-functors-general] to $F:\mathcal T_X\to\mathcal T_Y$,
   $L:\mathcal T_Y\to\mathcal T_X$. Its essential-constancy hypotheses hold at every complex.
   Ind side [def-pc-essentially-constant-ind-diagram]: fix a K-injective resolution $s_0:K\to
   I_0$ (step 3). For a quasi-isomorphism $s:K\to I$, [lem-weil-pbc-kinjective-hom-derived]
   gives a chain map $a:I\to I_0$ with $as\simeq s_0$, unique up to homotopy. Take $p_s=Q(F(a))$
   followed by the step-5 isomorphism $QF(I_0)\cong R_u(QK)$, $j_0=s_0$ and $r=$ the inverse of
   that isomorphism. Any two quasi-isomorphisms of K-injectives are homotopy equivalences by the
   same node, so the legs are natural and satisfy the common-stage condition at $k=(s,s_0)$
   followed by a K-injective resolution. Pro side [def-pc-essentially-constant-pro-diagram]: $L$
   is exact, so every leg $QL(P)\to QL(M)$ of a quasi-isomorphism $t:P\to M$ is invertible; take
   $u_t$ the inverse leg composed with $G_u(QM)\cong QL(M)$ and the stage $t=1_M$. This is
   Stacks 070Y. It gives the natural Hom bijection for $G_u\dashv R_u$. Its displayed fraction
   characterization with the left resolution equal to the identity says explicitly that, for
   $K\xrightarrow sI$ K-injective, a map $M\to FI$ is sent to $LM\to I\xrightarrow{(Qs)^{-1}}K$,
   the first map being the ordinary chain-level adjunct. Consequently the unit at $QM$ is $QM\to
   QFLM\to QFI(LM)$, the ordinary unit followed by the direct image of a K-injective resolution
   $LM\to I(LM)$. The counit at $QK$, using $K\xrightarrow sI$, is
   $QLFI\xrightarrow{Q\varepsilon_I}QI\xrightarrow{(Qs)^{-1}}QK$. The natural Hom bijection
   makes these precisely its unit and counit, so the triangle identities and normalization
   follow without a new choice of adjunction.
7. For an open immersion $j:U\hookrightarrow X$, [lem-weil-proetale-weakly-etale-localization]
   identifies $U_{\mathrm{proet}}$ with $X_{\mathrm{proet}}/U$ and $\underline B_U$ with the
   restricted coefficient ring for arbitrary $B$. The equivalence of [lem-weil-pbc-proetale-
   ringed-open-comparison] intertwines the actual module inverse image with slice restriction.
   Apply [lem-pur-site-restriction-module-adjunction-exact] on this localized ringed site:
   restriction is exact and extension by zero is its exact left adjoint. In particular this is
   the adjoint specified in the item. Applying these functors at each index gives an adjunction
   on strict towers by the transition-equation argument of step 2, and both functors are exact
   because kernels and cokernels are computed levelwise.
8. Apply [lem-weil-pbc-exact-functor-derived-factorization] and [lem-weil-pbc-exact-functor-
   derived-functor] to both exact functors of step 7. Their total derived functors are their
   termwise descents $J_j,G_j$. Apply [lem-pc-pre-derived-adjoint-functors-general] with $F=j^*$
   and $G=j_!$ on tower categories. Both functors are exact, so every transition map of its ind-
   and pro-diagrams is invertible, and both diagrams are essentially constant with stage the
   identity resolution [def-pc-essentially-constant-ind-diagram] [def-pc-essentially-constant-
   pro-diagram]. In its fraction formula both resolutions may now be the identity, so its Hom
   bijection on chain maps is the original termwise open adjunction, after localization. Thus
   its unit and counit are the images of the termwise open unit and counit, and it gives
   $J_j\dashv G_j$ with the required normalization. All preceding arguments use only smallness
   of the sites, an arbitrary commutative ring, and exactness; no bound on complex degrees,
   finiteness of $B$, or property of the tower transition maps was invoked.
-/
theorem towerAdjunctionRealization :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of B))) ∧
    (∀ (C : Type (u + 1)) [CommRing C] (φ : B →+* C)
        {X Y : Scheme.{u}} (f : X ⟶ Y),
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom φ)) ≫
        Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of C) =
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B) ≫
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom φ)) ∧
    (∀ X : Scheme.{u},
      Scheme.proEtaleConstantInverseImageMap (𝟙 X) CommRingCat.{u + 1} (CommRingCat.of B) =
        (Adjunction.leftAdjointIdIso
          (Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})
          (Functor.sheafPushforwardContinuousId'
            (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
            (Scheme.ProEt.topology X))).hom.app (coefficients B X)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      constantRingIso B (f ≫ g) = Scheme.proEtaleRingCompositeCoefficients f g
        (coefficients B Z) (coefficients B Y) (coefficients B X)
        (constantRingIso B g) (constantRingIso B f)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      PreservesFiniteLimits (modulePullback B f) ∧
      PreservesFiniteColimits (modulePullback B f) ∧
      PreservesFiniteLimits (towerPullback B f) ∧
      PreservesFiniteColimits (towerPullback B f) ∧
      (∀ (M : Towers B Y) (n : ℕ),
        ((termwiseAdjunction B f).unit.app M).app (op n) =
          (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
            (coefficients B X) (constantRingIso B f)).unit.app (M.obj (op n))) ∧
      (∀ (N : Towers B X) (n : ℕ),
        ((termwiseAdjunction B f).counit.app N).app (op n) =
          (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
            (coefficients B X) (constantRingIso B f)).counit.app (N.obj (op n)))) ∧
    (∀ X : Scheme.{u},
      ∃ (T : GrothendieckTopology ((ℕᵒᵖ)ᵒᵖ × Scheme.proEtaleSiteModel X))
        (R : Sheaf T RingCat.{u + 1})
        (M : ringedSiteModules.{u + 1} R ≌ Towers B X),
        (∀ (n : ℕᵒᵖ) (V : Scheme.proEtaleSiteModel X) (S : Sieve (op n, V)),
          S ∈ T (op n, V) ↔
            S.functorPullback (Prod.sectR (op n) (Scheme.proEtaleSiteModel X)) ∈
              Scheme.proEtaleModelTopology X V) ∧
        R.obj = (CategoryTheory.Prod.snd (ℕᵒᵖ)ᵒᵖ (Scheme.proEtaleSiteModel X)).op ⋙
          (AsSmall.down : Scheme.proEtaleSiteModel X ⥤ X.ProEt).op ⋙
            ((sheafCompose (Scheme.ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)).obj ∧
        M.functor.Additive ∧ PreservesFiniteLimits M.functor ∧
          PreservesFiniteColimits M.functor) ∧
    (∀ X : Scheme.{u}, IsGrothendieckAbelian.{u + 1} (Towers B X)) ∧
    (∀ (X : Scheme.{u}) (K : CochainComplex (Towers B X) ℤ),
      ∃ (I : CochainComplex (Towers B X) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (I : CochainComplex (Towers B X) ℤ),
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((towerDirectImage B f).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (R B f).IsRightDerivedFunctor (towerDirectImage B f).rightDerivedFunctorUnit
        (HomotopyCategory.quasiIso (Towers B X) (.up ℤ)) ∧
      (∀ (I : CochainComplex (Towers B X) ℤ), I.IsKInjective →
        IsIso ((towerDirectImage B f).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient (Towers B X) (.up ℤ)).obj I)))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      adj B f = (termwiseAdjunction B f).mapDerivedCategoryRightDerivedAdjunction) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
      PreservesFiniteLimits (towerJ B j) ∧
      PreservesFiniteColimits (towerJ B j) ∧
      PreservesFiniteLimits (towerPullback B j) ∧
      PreservesFiniteColimits (towerPullback B j) ∧
      jAdj B j = Adjunction.ofNatIsoRight
        (((moduleJAdj B j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction)
        (towerPullback B j).rightDerivedFunctorIsoMapDerivedCategory) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f ↦ constantRing_isIso B f
  · intro C _ φ X Y f
    exact Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom φ)
  · intro X
    let A := CommRingCat.of B
    let a := Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}
    let e := Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
      (Scheme.ProEt.topology X)
    have hρ : Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A =
        e.inv.app (coefficients B X) := by
      apply ((sheafificationAdjunction (Scheme.ProEt.topology X)
        CommRingCat.{u + 1}).homEquiv _ _).injective
      rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
      rw [Adjunction.homEquiv_unit]
      apply NatTrans.ext
      funext W
      change (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app
          ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj W) =
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app W ≫
            (e.inv.app (coefficients B X)).hom.app W
      rw [Functor.sheafPushforwardContinuousId'_inv_app_hom_app]
      exact (Category.id_comp _).symm.trans
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app W.unop).op)
    apply (a.homEquiv _ _).injective
    change a.homEquiv _ _ ((a.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change _ = a.unit.app _ ≫
      (Scheme.proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1}).map
        (((conjugateEquiv Adjunction.id a).symm e.inv).app _)
    rw [← unit_conjugateEquiv_symm Adjunction.id a]
    change _ = 𝟙 _ ≫ e.inv.app (coefficients B X)
    rw [Category.id_comp]
    exact hρ
  · exact fun f g ↦ constantRingIso_comp B f g
  · intro X Y f
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      fun M n ↦ rfl, fun N n ↦ rfl⟩
  · intro X
    let O := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let O' := ((AsSmall.down : Scheme.proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
       RingCat.{u + 1} (Scheme.proEtaleModelTopology X)
        (Scheme.ProEt.topology X)).obj O
    let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
        (Scheme.ProEt.topology X) (Scheme.proEtaleModelTopology X) :=
      Scheme.proEtaleModelUp_isContinuous X
    let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
        (Scheme.proEtaleModelTopology X) (Scheme.ProEt.topology X) := by
      change AsSmall.down.IsContinuous _ _
      infer_instance
    let e : ringedSiteModules.{u + 1} O' ≌ Modules B X :=
      SheafOfModules.pushforwardPushforwardEquivalence
        (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 O) (𝟙 O')
        (by ext V; dsimp [AsSmall.equiv]; erw [O'.obj.map_id]; rfl)
        (by ext V; dsimp [AsSmall.equiv]; erw [O.obj.map_id]; rfl)
    let d := towerDiagramModuleEquivalence ℕᵒᵖ (Scheme.proEtaleSiteModel X)
      (Scheme.proEtaleModelTopology X) O'
    let M := d.trans (e.congrRight (E := ℕᵒᵖ))
    refine ⟨_, _, M, fun _ _ _ ↦ Iff.rfl, (by rfl), ?_, inferInstance, inferInstance⟩
    exact Functor.additive_of_preserves_binary_products _
  · intro X
    let M := Modules B X
    let H := separator M
    have hH := isSeparator_separator M
    have hS : ObjectProperty.IsSeparating
        (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint M j).obj H) := by
      intro F F' f g hfg
      apply NatTrans.ext
      funext j
      apply hH.def
      intro a
      let ad := evaluationAdjunctionRight M j
      apply (ad.homEquiv H F').symm.injective
      have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((ad.homEquiv H F).symm a)
      exact (ad.homEquiv_naturality_right_symm a f).trans
        (h.trans (ad.homEquiv_naturality_right_symm a g).symm)
    let : HasSeparator (Towers B X) := ⟨_, hS.isSeparator_coproduct⟩
    let : HasFilteredColimitsOfSize.{u + 1, u + 1} (Towers B X) :=
      ⟨fun _ _ _ ↦ inferInstance⟩
    let : AB5OfSize.{u + 1, u + 1} (Towers B X) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact {}
  · intro X K
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, s, hI, hs⟩
  · intro X Y f I hI
    let := hI
    let := (termwiseAdjunction B f).preservesKInjectiveComplexes
    infer_instance
  · intro X Y f
    refine ⟨?_, ?_⟩
    · dsimp only [R]
      infer_instance
    intro I hI
    let := hI
    infer_instance
  · intro X Y f
    rfl
  · intro U X j _
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, rfl⟩

end AlgebraicGeometry.ProEtale.StrictTower

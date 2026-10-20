/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.CategoryTheory.RingedCoefficientChangePresentations
import Sheaf.CategoryTheory.RingedCoefficientRestrictionDerivedPresentation
import Sheaf.CategoryTheory.RingedCoefficientRestrictionCoefficientChange
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Derived ringed-topos counit under coefficient restriction

Source: Stacks, Tags 03D7, 07A6 and 0D6E
(blueprint: lem-pur-ringed-coefficient-restriction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedCoefficientCounit

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  (A : CommRingCat.{r}) (RX RI : Sheaf JX CommRingCat.{r})
  (RY : Sheaf JY CommRingCat.{r})
  (inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r))
  (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
  [leftExact : PreservesFiniteLimits inverse]
  (IA : SheafOfModules.AlgebraicInverseImage inverse
    (constantRing JY A) (constantRing JX A))
  (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)

private theorem hasKInjectives
    {E : Type u} [Category.{v} E] [EssentiallySmall.{r} E]
    (J : GrothendieckTopology E)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r}) : Abelian.HasKInjectiveResolutions (modules R) := by
  let S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let B := SheafOfModules.{r} S
  let F := (PresheafOfModules.toPresheaf.{r} S.obj) ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{r}).obj (equivSmallModel.{r} E).inverse.op
  have : LocallySmall.{r} (PresheafOfModules.{r} S.obj) := locallySmall_of_faithful F
  have : LocallySmall.{r} B := locallySmall_of_faithful (SheafOfModules.forget S)
  have hsep : ObjectProperty.IsSeparating (.ofObj fun U : E ↦
      (PresheafOfModules.sheafification.{r} (𝟙 S.obj)).obj
        ((PresheafOfModules.free S.obj).obj (shrinkYoneda.{r}.obj U))) := by
    let adj := (PresheafOfModules.freeAdjunction S.obj).comp
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 S.obj))
    intro M N f g h
    apply ((SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars (𝟙 S.obj)) ⋙
      PresheafOfModules.toPresheaf S.obj ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)).map_injective
    ext ⟨U⟩ x
    let a := shrinkYonedaEquiv.symm x
    have heq := h _ (ObjectProperty.ofObj_apply _ U) ((adj.homEquiv _ _).symm a)
    have hh := congrArg (adj.homEquiv _ _) heq
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at hh
    have hx := congrArg shrinkYonedaEquiv hh
    simp only [shrinkYonedaEquiv_comp, a, Equiv.apply_symm_apply] at hx
    change f.val.app (Opposite.op U) x = g.val.app (Opposite.op U) x at hx ⊢
    exact hx
  have : HasFilteredColimitsOfSize.{r, r} B := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{r, r} B :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf.{r} S)⟩
  have : HasCoproductsOfShape E B := hasCoproductsOfShape_of_small B E
  have : HasSeparator B := ⟨_, hsep.isSeparator_coproduct⟩
  have : IsGrothendieckAbelian.{r} B := {}
  exact inferInstance

omit [UnivLE.{max u v, r}] [HasSheafify JY AddCommGrpCat.{r}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{r}] leftExact in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryTranspose
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    (M : modules RY) (N : modules RX) (h : o.pull.obj M ⟶ N) :
    o.adjA.homEquiv _ _ (o.scalarUnit.app M ≫ (restriction aX).map h) =
      (restriction aY).map (o.adjR.homEquiv _ _ h) ≫ o.ordinaryKappa.hom.app N := by
  apply (underlying (constantRing JY A)).map_injective
  apply (cancel_mono (o.pushAUnderlying.hom.app ((restriction aX).obj N))).mp
  rw [o.adjAFormula]
  simp only [Functor.map_comp, Category.assoc, o.ordinaryKappaFormula,
    o.scalarUnitFormula, o.inverseRestrictionFormula]
  rw [Iso.inv_hom_id_app_assoc]
  exact (o.adjRFormula M N h).symm

omit [UnivLE.{max u v, r}] [HasSheafify JY AddCommGrpCat.{r}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{r}] leftExact in
private theorem ordinaryComplexTranspose
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI) [IA.modules.Additive]
    (P : CochainComplex (modules RY) ℤ) (I : CochainComplex (modules RX) ℤ)
    (h : (onComplex o.pull).obj P ⟶ I) :
    (o.adjA.mapHomologicalComplex (.up ℤ)).homEquiv _ _
        ((NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).app P ≫
          (onComplex (restriction aX)).map h) =
      (onComplex (restriction aY)).map
          ((o.adjR.mapHomologicalComplex (.up ℤ)).homEquiv _ _ h) ≫
        (NatTrans.mapHomologicalComplex o.ordinaryKappa.hom (.up ℤ)).app I := by
  simp only [Adjunction.homEquiv_unit]
  apply HomologicalComplex.hom_ext
  intro n
  change o.adjA.unit.app ((restriction aY).obj (P.X n)) ≫
      o.pushA.map (o.scalarUnit.app (P.X n) ≫ (restriction aX).map (h.f n)) =
    (restriction aY).map (o.adjR.unit.app (P.X n) ≫ o.pushR.map (h.f n)) ≫
      o.ordinaryKappa.hom.app (I.X n)
  have hh := ordinaryTranspose A RX RI RY inverse direct geom IA IR c aX aY aI o
    (P.X n) (I.X n) (h.f n)
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [o.adjA.homEquiv_unit, o.adjR.homEquiv_unit] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [UnivLE.{max u v, r}] leftExact in
private theorem localizedKappaEquation
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI) [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o)
    (P : CochainComplex (modules RY) ℤ) (I : CochainComplex (modules RX) ℤ)
    (hI : I.IsKInjective)
    (T : CochainComplex (modules (constantRing JX A)) ℤ) (hT : T.IsKInjective)
    (j : (onComplex (restriction aX)).obj I ⟶ T) [QuasiIso j]
    (h : P ⟶ (onComplex o.pushR).obj I) :
    p.y.map (DerivedCategory.Q.map h ≫ p.r.eta.app I) ≫
        p.kappa.hom.app (DerivedCategory.Q.obj I) ≫
        p.a.right.map (p.xFactors.hom.app I ≫ DerivedCategory.Q.map j) =
      p.yFactors.hom.app P ≫ DerivedCategory.Q.map
        ((onComplex (restriction aY)).map h ≫
          (NatTrans.mapHomologicalComplex o.ordinaryKappa.hom (.up ℤ)).app I ≫
          (onComplex o.pushA).map j) ≫ p.a.eta.app T := by
  have hk := p.kappaFormula I hI T hT j
  have hk' := congrArg (fun z ↦ p.yFactors.hom.app ((onComplex o.pushR).obj I) ≫ z ≫
    p.a.right.map (p.xFactors.hom.app I ≫ DerivedCategory.Q.map j)) hk
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← p.a.right.map_comp,
    Iso.inv_hom_id_app_assoc, IsIso.inv_hom_id, p.a.right.map_id,
    ] at hk'
  erw [Category.comp_id] at hk'
  rw [p.y.map_comp]
  simp only [Category.assoc]
  rw [hk']
  have hn := p.yFactors.hom.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]


set_option maxHeartbeats 800000 in
-- The representative formula elaborates several composites of module-sheaf functors.
omit [UnivLE.{max u v, r}] leftExact in
private theorem derivedTransposeOnRepresentative
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI) [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o)
    (P : CochainComplex (modules RY) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := JY) (R := RY) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := JY) (R := RY) (P.X n))
    (I : CochainComplex (modules RX) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (modules (constantRing JX A)) ℤ) (hT : T.IsKInjective)
    (j : (onComplex (restriction aX)).obj I ⟶ T) [QuasiIso j]
    (f : (onComplex o.pull).obj P ⟶ I) :
    p.tau.app (DerivedCategory.Q.obj P) ≫
        p.x.map (p.r.epsilon.app P ≫ DerivedCategory.Q.map f) =
      (p.a.adj.homEquiv _ _).symm
        (p.y.map (DerivedCategory.Q.map
          ((o.adjR.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫ p.r.eta.app I) ≫
            p.kappa.hom.app (DerivedCategory.Q.obj I)) := by
  let g := (o.adjR.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f
  let k : (onComplex IA.modules).obj ((onComplex (restriction aY)).obj P) ⟶ T :=
    (NatTrans.mapHomologicalComplex o.scalarUnit (.up ℤ)).app P ≫
    (onComplex (restriction aX)).map f ≫ j
  have ht : (o.adjA.mapHomologicalComplex (.up ℤ)).homEquiv _ _ k =
      (onComplex (restriction aY)).map g ≫
        (NatTrans.mapHomologicalComplex o.ordinaryKappa.hom (.up ℤ)).app I ≫
          (onComplex o.pushA).map j := by
    dsimp only [k]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rw [ordinaryComplexTranspose A RX RI RY inverse direct geom IA IR c aX aY aI o]
    rfl
  have hA := p.a.homFormula ((onComplex (restriction aY)).obj P) T hT
    ((onComplex (restriction aY)).map g ≫
      (NatTrans.mapHomologicalComplex o.ordinaryKappa.hom (.up ℤ)).app I ≫
        (onComplex o.pushA).map j)
  rw [← ht, Equiv.symm_apply_apply] at hA
  have hk := localizedKappaEquation A RX RI RY inverse direct geom IA IR c
    aX aY aI o p P I hI T hT j g
  let t := p.xFactors.hom.app I ≫ DerivedCategory.Q.map j
  have : IsIso t := by dsimp [t]; infer_instance
  apply (cancel_mono t).mp
  dsimp only [t]
  erw [← Adjunction.homEquiv_naturality_right_symm]
  simp only [Category.assoc]
  change _ = (p.a.adj.homEquiv _ _).symm
    (p.y.map (DerivedCategory.Q.map g ≫ p.r.eta.app I) ≫
      p.kappa.hom.app (DerivedCategory.Q.obj I) ≫
        p.a.right.map (p.xFactors.hom.app I ≫ DerivedCategory.Q.map j))
  erw [hk, Adjunction.homEquiv_naturality_left_symm, ← ht, hA]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (p.xFactors.hom.naturality f)]
  have htau := p.tauFormula P hP hf
  dsimp only [k]
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simp only [Functor.map_comp]
  rw [reassoc_of% htau]

omit leftExact in
private theorem counitOnInjective
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI) [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o)
    (I : CochainComplex (modules RX) ℤ) (hI : I.IsKInjective) :
    p.tau.app (p.r.right.obj (DerivedCategory.Q.obj I)) ≫
        p.x.map (p.r.adj.counit.app (DerivedCategory.Q.obj I)) =
      p.a.left.map (p.kappa.hom.app (DerivedCategory.Q.obj I)) ≫
        p.a.adj.counit.app (p.x.obj (DerivedCategory.Q.obj I)) := by
  have := hasKInjectives JX (constantRing JX A)
  obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((onComplex (restriction aX)).obj I)
  let := hj
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients ((onComplex o.pushR).obj I)
  let := hq
  have hflat (n : ℤ) : SheafOfModules.IsFlatOnSite (J := JY) (R := RY) (P.X n) := by
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso RY (P.X n)).symm (hf n)
  let h := DerivedCategory.Q.map q ≫ p.r.eta.app I
  have : IsIso (p.r.eta.app I) := p.r.onInjective I hI
  have : IsIso h := by dsimp [h]; infer_instance
  have he := derivedTransposeOnRepresentative A RX RI RY inverse direct geom IA IR c
    aX aY aI o p P hP hflat I hI T hT j
      (((o.adjR.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm q)
  rw [Equiv.apply_symm_apply] at he
  have hr := p.r.homFormula P I hI q
  rw [← hr] at he
  change p.tau.app (DerivedCategory.Q.obj P) ≫
      p.x.map ((p.r.adj.homEquiv _ _).symm h) =
    (p.a.adj.homEquiv _ _).symm
      (p.y.map h ≫ p.kappa.hom.app (DerivedCategory.Q.obj I)) at he
  apply (cancel_epi (p.a.left.map (p.y.map h))).mp
  rw [Adjunction.homEquiv_counit] at he
  rw [Adjunction.homEquiv_counit] at he
  have hn := p.tau.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simpa only [Functor.map_comp, Category.assoc] using he

omit leftExact in
private theorem counitCompatibility
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI) [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o) : CounitCompatibility p := by
  have := hasKInjectives JX RX
  intro K
  obtain ⟨M, ⟨e⟩⟩ := (Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K)
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective M
  let := hj
  let s : DerivedCategory.Q.obj I ≅ K := (asIso (DerivedCategory.Q.map j)).symm ≪≫ e
  have he := counitOnInjective A RX RI RY inverse direct geom IA IR c aX aY aI o p I hI
  apply (cancel_epi (p.a.left.map (p.y.map (p.r.right.map s.hom)))).mp
  have ht := p.tau.naturality (p.r.right.map s.hom)
  have hr := p.r.adj.counit.naturality s.hom
  have hk := p.kappa.hom.naturality s.hom
  have ha := p.a.adj.counit.naturality (p.x.map s.hom)
  dsimp only [Functor.comp_map, Functor.id_map] at ht hr hk ha
  rw [reassoc_of% ht]
  rw [← p.x.map_comp, hr, p.x.map_comp]
  rw [← Category.assoc, he]
  rw [Category.assoc, ← ha, ← Category.assoc, ← p.a.left.map_comp, ← hk]
  simp only [Functor.map_comp, Category.assoc]

include leftExact in
/-- Canonical coefficient comparisons exist and respect the derived counit and every
compatible coefficient homomorphism. Exactness of coefficient restriction is supplied
by the resulting presentation. No flatness of aX or aY is assumed.
Source: Stacks 03D7, 07A6, 0FND and 0D6E
(blueprint: lem-pur-ringed-coefficient-restriction-counit).

Proof:
1. Obtain the normalized derived presentation from exists_derivedPresentation. Its existence
is separate from the counit calculation, which applies to every such presentation.
2. Faithfulness of the underlying sheaf functor, the ordinary adjunction formulas and the
scalar-unit formula give ordinaryTranspose. Apply it degreewise to obtain the complex
transpose. The kappa normalization and factorization naturality give localizedKappaEquation.
3. Resolve the restricted K-injective target by a K-injective complex. Apply the constant
coefficient derived Hom formula and the ordinary complex transpose; tauFormula then gives
derivedTransposeOnRepresentative. Resolve pushR(I) by a flat-term K-flat complex P. The
representative equation and r.homFormula identify the two inverse adjuncts. Expanding inverse
adjuncts as images followed by counits and cancelling the invertible resolution map proves
the counit square on I.
4. Free sheaves on shrink-Yoneda representables give a separating family. Their coproduct and
exact filtered colimits yield Grothendieck abelianness in the coefficient universe, hence
K-injective resolutions. Every derived object is isomorphic to Q(I) for such an I. Transport
the square by naturality of tau, kappa and the counits to prove CounitCompatibility.
5. Apply coefficientChange_exists to the compatible coefficient maps, supplying the two
CounitCompatibility results just proved. Its construction and naturality conclusions give
the remaining conjunction. -/
theorem ringedCoefficientRestrictionCounit
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (haI : (sheafCompose JX (forget CommRingCat.{r})).map aI =
      IA.ringUnderlying.inv ≫ inverse.map
        ((sheafCompose JY (forget CommRingCat.{r})).map aY) ≫ IR.ringUnderlying.hom)
    (hc : aI ≫ c = aX)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))] :
    Nonempty (DerivedPresentation o) ∧
    ∀ p : DerivedPresentation o, CounitCompatibility p ∧
      ∀ (RX' RI' : Sheaf JX CommRingCat.{r}) (RY' : Sheaf JY CommRingCat.{r})
        (IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI') (c' : RI' ⟶ RX')
        (aX' : constantRing JX A ⟶ RX') (aY' : constantRing JY A ⟶ RY')
        (aI' : constantRing JX A ⟶ RI')
        (o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI')
        [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]
        (p' : DerivedPresentation o') (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI'),
        aX ≫ bX = aX' → aY ≫ bY = aY' → aI ≫ bI = aI' →
        c ≫ bX = bI ≫ c' →
        IR.ringUnderlying.hom ≫ (sheafCompose JX (forget CommRingCat.{r})).map bI =
          inverse.map ((sheafCompose JY (forget CommRingCat.{r})).map bY) ≫
            IR'.ringUnderlying.hom →
        Nonempty (CoefficientChange p p' bX bY bI) ∧
          ∀ m : CoefficientChange p p' bX bY bI, m.IsNatural := by
  obtain ⟨p⟩ := exists_derivedPresentation A RX RI RY inverse direct geom IA IR c
    aX aY aI haI hc o
  refine ⟨⟨p⟩, ?_⟩
  intro p
  refine ⟨counitCompatibility A RX RI RY inverse direct geom IA IR c
    aX aY aI o p, ?_⟩
  intro RX' RI' RY' IR' c' aX' aY' aI' o' hRX' hRY' p' bX bY bI
    haX haY haI' hc' hIR
  exact coefficientChange_exists A RX RI RY inverse direct geom IA IR c
    aX aY aI o p (counitCompatibility A RX RI RY inverse direct geom IA IR c
      aX aY aI o p) RX' RI' RY' IR' c' aX' aY' aI' o' p'
    (counitCompatibility A RX' RI' RY' inverse direct geom IA IR' c'
      aX' aY' aI' o' p') bX bY bI
    haX haY haI' hc' hIR

end CategoryTheory.RingedCoefficientCounit

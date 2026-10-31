/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps
import all WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorLinearTransport
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
/-! # The canonical continuous integral Galois fibre functor

Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9.
(blueprint: new-e7-canonical-integral-galois-functor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite Topology
namespace AlgebraicGeometry.Scheme

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A continuous integral representation functor with its prescribed fibre and finite action.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, integral stage.
(blueprint: new-e7-canonical-integral-galois-functor). -/
structure IntegralGaloisForwardData
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] where
  T : LisseIntegralSheaf l E Y ⥤ galoisIntegralRepresentations l E P δ
  τ : T ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
    lisseIntegralFiberFunctor l E Y y
  /-- Faithfulness is already proved before reconstructing inverse objects or lifting maps. -/
  faithful : T.Faithful
  /-- The limit action is the supplied finite evaluation action on every stalk projection. -/
  evaluation :
    ∀ (F : LisseIntegralSheaf l E Y) (n : ℕ),
      ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
        (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))),
      ∀ (g : G) (z : (T.obj F).obj.V),
        pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
            ((τ.hom.app F ≫
              limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n))
                ((T.obj F).obj.ρ g z)) =
          (c.γ g).hom.app (galoisUnderlyingFLC
            (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)) h)
            (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
              ((τ.hom.app F ≫
                limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)) z))


variable {Y : Scheme.{u}}
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  (c : GaloisLisseFiniteCorrespondence y G)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem flcEvaluation_continuous (X : Y.FLC) :
    letI : TopologicalSpace ((flcFiber y).obj X) := ⊥
    Continuous (fun p : G × (flcFiber y).obj X ↦ (c.γ p.1).hom.app X p.2) := by
  let : TopologicalSpace ((flcFiber y).obj X) := ⊥
  let : DiscreteTopology ((flcFiber y).obj X) := ⟨rfl⟩
  rw [continuous_prod_of_discrete_right]
  intro x
  have h₁ : Continuous (SetFunctorAut.evaluation (flcFiber y)) := continuous_induced_dom
  have h₂ : Continuous (fun g : G ↦ SetFunctorAut.evaluation (flcFiber y) (c.γ g) X) :=
    (continuous_apply X).comp (h₁.comp c.γ.continuous)
  have h₃ : Continuous (fun a : Aut ((flcFiber y).obj X) ↦
      (a.hom : (flcFiber y).obj X → (flcFiber y).obj X)) := continuous_induced_dom
  exact (continuous_apply x).comp (h₃.comp h₂)

private theorem integralTopology_eq (F : LisseIntegralSheaf l E Y) :
    let J := Padic.coefficientExtensionMaximalIdeal l E
    let D := F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber
    letI : ∀ j : ℕᵒᵖ, TopologicalSpace (D.obj j) := fun _ ↦ ⊥
    TopologicalSpace.induced
      (fun x : ↥(limit D) ↦ (limitSectionsLinearEquiv D x).val) inferInstance =
      J.adicModuleTopology ↥(limit D) := by
  intro J D
  let S := ModuleCat.sectionsSubmodule D
  let e := limitSectionsLinearEquiv D
  have hf (n : ℕ) : Module.Finite (Padic.coefficientExtensionIntegers l E) (D.obj (op n)) := by
    let : Finite (D.obj (op n)) := finite_integral_level l E F n y
    exact Module.Finite.of_finite
  have h := Padic.adicLimit_finite_modules l E D hf
    (integralStalk_annihilated Y y l E F) (F.property.2.2 Ω y)
  let : ∀ j : ℕᵒᵖ, TopologicalSpace (D.obj j) := fun _ ↦ ⊥
  have hs : TopologicalSpace.induced (fun x : S ↦ x.val) inferInstance =
      J.adicModuleTopology S := h.2.2
  let : TopologicalSpace ↥(limit D) := J.adicModuleTopology ↥(limit D)
  let : TopologicalSpace S := J.adicModuleTopology S
  let eH : @Homeomorph ↥(limit D) S (J.adicModuleTopology ↥(limit D))
      (J.adicModuleTopology S) :=
    { e.toEquiv with
      continuous_toFun := Padic.adicLinearMap_continuous J e.toLinearMap
      continuous_invFun := Padic.adicLinearMap_continuous J e.symm.toLinearMap }
  calc
    TopologicalSpace.induced (fun x : ↥(limit D) ↦ (e x).val) inferInstance =
        TopologicalSpace.induced (fun x : ↥(limit D) ↦ e x)
          (TopologicalSpace.induced (fun x : S ↦ x.val) inferInstance) :=
      (induced_compose (f := fun x : ↥(limit D) ↦ e x)
        (g := fun x : S ↦ x.val)).symm
    _ = TopologicalSpace.induced (fun x : ↥(limit D) ↦ e x)
        (J.adicModuleTopology S) := congrArg (TopologicalSpace.induced (fun x ↦ e x)) hs
    _ = J.adicModuleTopology ↥(limit D) := eH.isInducing.eq_induced.symm

private noncomputable def integralAction (F : LisseIntegralSheaf l E Y) :
    Representation (Padic.coefficientExtensionIntegers l E) G
      ((lisseIntegralFiberFunctor l E Y y).obj F) where
  toFun g := (((integralFamily l E Y
    (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
      y y (c.γ g)).hom.app F).hom
  map_one' := by
    change (((integralFamily l E Y
      (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
        y y (c.γ 1)).hom.app F).hom = LinearMap.id
    rw [map_one]
    change (((integralFamily l E Y
      (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
        y y (Iso.refl (flcFiber y))).hom.app F).hom = _
    rw [(integralFamily l E Y _).identity]
    rfl
  map_mul' g h := by
    ext x
    change ((integralFamily l E Y
      (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
        y y (c.γ (g*h))).hom.app F x =
      ((integralFamily l E Y
        (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
          y y (c.γ g)).hom.app F
        (((integralFamily l E Y
          (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
            y y (c.γ h)).hom.app F x)
    rw [map_mul]
    change ((integralFamily l E Y
      (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
        y y ((c.γ h) ≪≫ (c.γ g))).hom.app F x = _
    rw [(integralFamily l E Y _).composition]
    rfl
private theorem integralAction_evaluation (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
      (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))),
    ∀ (g : G) (x : (lisseIntegralFiberFunctor l E Y y).obj F),
      pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
        (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          (integralAction y G c l E F g x)) =
      (c.γ g).hom.app (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E)
        (F.obj.obj (op n)) h)
        (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
          (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) x)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let Fₙ : LisseModuleSheafCategory Y R :=
    ⟨F.obj.obj (op n), integral_level_lisse l E F n⟩
  obtain ⟨h, _⟩ := lisseLinearFibrePathFamily_evaluation R y y (c.γ 1) Fₙ
  refine ⟨h, ?_⟩
  intro g x
  obtain ⟨_, he⟩ := lisseLinearFibrePathFamily_evaluation R y y (c.γ g) Fₙ
  have hπ : ((integralFamily l E Y (lisseLinearFibrePathFamily Y R)).map
      y y (c.γ g)).hom.app F ≫
      limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) =
    limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
      ((lisseLinearFibrePathFamily Y R).map y y (c.γ g)).hom.app Fₙ := by
    exact limMap_π _ (op n)
  have hπx := ConcreteCategory.congr_hom hπ x
  exact (congrArg (pathUnderlyingStalk y R Fₙ.obj) hπx).trans (he _)

private theorem integralAction_continuous (F : LisseIntegralSheaf l E Y) :
    let M := (lisseIntegralFiberFunctor l E Y y).obj F
    let J := Padic.coefficientExtensionMaximalIdeal l E
    letI : TopologicalSpace M := J.adicModuleTopology M
    Continuous (fun p : G × M ↦ integralAction y G c l E F p.1 p.2) := by
  intro M J
  let : TopologicalSpace M := J.adicModuleTopology M
  let R := Padic.coefficientExtensionIntegers l E
  let D := F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber
  let : ∀ j : ℕᵒᵖ, TopologicalSpace (D.obj j) := fun _ ↦ ⊥
  let e := limitSectionsLinearEquiv D
  have htop : TopologicalSpace.induced (fun x : M ↦ (e x).val) inferInstance =
      J.adicModuleTopology M := integralTopology_eq y l E F
  have hi : IsInducing (fun x : M ↦ (e x).val) := ⟨htop.symm⟩
  have hι : Continuous (fun x : M ↦ (e x).val) := hi.continuous
  apply hi.continuous_iff.mpr
  apply continuous_pi
  intro j
  let n := j.unop
  obtain ⟨h, he⟩ := integralAction_evaluation y G c l E F n
  let X := galoisUnderlyingFLC R (F.obj.obj (op n)) h
  let κ : D.obj j ≃ (flcFiber y).obj X :=
    pathUnderlyingStalk y R (F.obj.obj (op n))
  let : TopologicalSpace ((flcFiber y).obj X) := ⊥
  let : DiscreteTopology ((flcFiber y).obj X) := ⟨rfl⟩
  let : DiscreteTopology (D.obj j) := ⟨rfl⟩
  have hp : Continuous (fun x : M ↦ limit.π D j x) :=
    (continuous_apply j).comp hι
  have hk : Continuous (fun x : D.obj j ↦ κ x) := continuous_of_discreteTopology
  have hk' : Continuous (fun x : (flcFiber y).obj X ↦ κ.symm x) :=
    continuous_of_discreteTopology
  have hinput : Continuous (fun p : G × M ↦
      (p.1, κ (limit.π D j p.2))) :=
    continuous_fst.prodMk (hk.comp (hp.comp continuous_snd))
  have hh := hk'.comp ((flcEvaluation_continuous y G c X).comp hinput)
  exact hh.congr (fun p ↦ by
    change κ.symm ((c.γ p.1).hom.app X (κ (limit.π D (op n) p.2))) =
      limit.π D (op n) (integralAction y G c l E F p.1 p.2)
    exact (congrArg κ.symm (he p.1 p.2).symm).trans (κ.symm_apply_apply _))

private noncomputable def integralForward :
    LisseIntegralSheaf l E Y ⥤ Rep.{u+1} (Padic.coefficientExtensionIntegers l E) G where
  obj F := Rep.of (integralAction y G c l E F)
  map f := Rep.ofHom
    { toLinearMap := ((lisseIntegralFiberFunctor l E Y y).map f).hom
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact (ConcreteCategory.congr_hom
          (((integralFamily l E Y
            (lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E))).map
              y y (c.γ g)).hom.naturality f) x).symm }
  map_id F := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    change ((lisseIntegralFiberFunctor l E Y y).map (𝟙 F)).hom = LinearMap.id
    simp
  map_comp f g := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    change ((lisseIntegralFiberFunctor l E Y y).map (f ≫ g)).hom = _
    rw [Functor.map_comp]
    rfl
private theorem integralForward_finite (F : LisseIntegralSheaf l E Y) :
    Module.Finite (Padic.coefficientExtensionIntegers l E)
      ((integralForward y G c l E).obj F).V :=
  lisseIntegralFiber_finite Y y l E F
variable [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)

omit [IsNoetherian Y] [Y.IsSeparated] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem flcFiber_faithful (c : GaloisLisseFiniteCorrespondence y G) :
    (flcFiber y).Faithful := by
  let B := CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  let H := c.Φ.inverse ⋙ FiniteEtale.fiber y ⋙ B
  let : H.Faithful := inferInstance
  let τ : H ≅ flcFiber y :=
    Functor.isoWhiskerLeft c.Φ.inverse c.η.symm ≪≫ c.Φ.invFunIdAssoc (flcFiber y)
  exact Functor.Faithful.of_iso τ

omit [ConnectedSpace Y] [IsNoetherian Y] [Y.IsSeparated] in
private theorem pathUnderlyingStalk_naturality
    (R : Type (u + 1)) [Ring R]
    {F H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (f : F ⟶ H)
    (x : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F)) :
    pathUnderlyingStalk y R H
        (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} R)).map f x) =
      ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).map
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f)
        (pathUnderlyingStalk y R F x) := by
  have h := ConcreteCategory.congr_hom ((pathUnderlyingNatIso y R).hom.naturality f) x
  exact h

omit [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem integralFiber_faithful (c : GaloisLisseFiniteCorrespondence y G) :
    (lisseIntegralFiberFunctor l E Y y).Faithful where
  map_injective := by
    intro F H f g hfg
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext j
    let n := j.unop
    let R := Padic.coefficientExtensionIntegers l E
    let S := (pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)
    have hlevel : S.map (f.hom.app j) = S.map (g.hom.app j) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨z, hz⟩ := (lisseIntegralFiber_projection Y y l E F n).1 x
      have hp := congrArg (fun a ↦ a ≫ limit.π (H.obj ⋙ S) j) hfg
      have hfπ : (lisseIntegralFiberFunctor l E Y y).map f ≫
          limit.π (H.obj ⋙ S) j =
          limit.π (F.obj ⋙ S) j ≫ S.map (f.hom.app j) :=
        limMap_π _ j
      have hgπ : (lisseIntegralFiberFunctor l E Y y).map g ≫
          limit.π (H.obj ⋙ S) j =
          limit.π (F.obj ⋙ S) j ≫ S.map (g.hom.app j) :=
        limMap_π _ j
      rw [hfπ, hgπ] at hp
      have hpz := ConcreteCategory.congr_hom hp z
      change S.map (f.hom.app j) (limit.π (F.obj ⋙ S) j z) =
        S.map (g.hom.app j) (limit.π (F.obj ⋙ S) j z) at hpz
      exact hz ▸ hpz
    let Fₙ : LisseModuleSheafCategory Y R :=
      ⟨F.obj.obj j, integral_level_lisse l E F n⟩
    let Hₙ : LisseModuleSheafCategory Y R :=
      ⟨H.obj.obj j, integral_level_lisse l E H n⟩
    obtain ⟨hF, _⟩ := lisseLinearFibrePathFamily_evaluation R y y (c.γ 1) Fₙ
    obtain ⟨hH, _⟩ := lisseLinearFibrePathFamily_evaluation R y y (c.γ 1) Hₙ
    let A := galoisUnderlyingFLC R Fₙ.obj hF
    let B := galoisUnderlyingFLC R Hₙ.obj hH
    let U := sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R))
    let ff : A ⟶ B := ObjectProperty.homMk (U.map (f.hom.app j))
    let gg : A ⟶ B := ObjectProperty.homMk (U.map (g.hom.app j))
    let : (flcFiber y).Faithful := flcFiber_faithful y G c
    have hset : ff = gg := by
      apply (flcFiber y).map_injective
      apply ConcreteCategory.hom_ext
      intro x
      obtain ⟨z, rfl⟩ := (pathUnderlyingStalk y R Fₙ.obj).surjective x
      change ((pointSmallEtale y).sheafFiber).map (U.map (f.hom.app j))
          (pathUnderlyingStalk y R Fₙ.obj z) =
        ((pointSmallEtale y).sheafFiber).map (U.map (g.hom.app j))
          (pathUnderlyingStalk y R Fₙ.obj z)
      rw [← pathUnderlyingStalk_naturality, ← pathUnderlyingStalk_naturality]
      exact congrArg (pathUnderlyingStalk y R Hₙ.obj)
        (ConcreteCategory.congr_hom hlevel z)
    have hu : U.map (f.hom.app j) = U.map (g.hom.app j) :=
      congrArg (fun a : A ⟶ B ↦ a.hom) hset
    exact U.map_injective hu


omit [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem integralForward_continuous (F : LisseIntegralSheaf l E Y) :
    Representation.IsContinuousIntegral l E P ((integralForward y G c l E).obj F).V
      ((galoisRepLinearAction _ ((integralForward y G c l E).obj F)).comp
        δ.symm.toMonoidHom) := by
  refine ⟨integralForward_finite y G c l E F, ?_⟩
  let M := (lisseIntegralFiberFunctor l E Y y).obj F
  let : TopologicalSpace M :=
    (Padic.coefficientExtensionMaximalIdeal l E).adicModuleTopology M
  have h := (integralAction_continuous y G c l E F).comp
    ((δ.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  exact h

private noncomputable def integralForwardData :
    IntegralGaloisForwardData y G c P δ l E := by
  let T : LisseIntegralSheaf l E Y ⥤ galoisIntegralRepresentations l E P δ :=
    ObjectProperty.lift _ (integralForward y G c l E)
      (integralForward_continuous y G c l E P δ)
  let τ : T ⋙ ObjectProperty.ι _ ⋙
      forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
      lisseIntegralFiberFunctor l E Y y :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)
  let : (lisseIntegralFiberFunctor l E Y y).Faithful := integralFiber_faithful y G l E c
  have hf : T.Faithful := Functor.Faithful.of_comp_iso τ
  refine ⟨T, τ, hf, ?_⟩
  intro F n
  exact integralAction_evaluation y G c l E F n

/-- Construct the normalized integral fibre functor with its actual continuous action.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, third bullet.
(blueprint: new-e7-canonical-integral-galois-functor).

Use the already proved linear path family at each lisse integral level and apply the
module limit functor. The path laws give an action on the actual geometric fibre;
path naturality makes the fibre map of every sheaf morphism equivariant, giving T.
Its underlying functor is definitionally the integral fibre functor, so the fibre
comparison is the identity. The existing finite integral fibre theorem supplies
finite generation. Adic reconstruction identifies the topology of compatible stalk
sections with the maximal-ideal-adic topology; the canonical module-limit/sections
linear equivalence preserves both adic topologies. Thus continuity can be checked on
every finite projection. Under the canonical set-stalk comparison each projected
action is evaluation of c.γ. Evaluation is continuous for the functor automorphism
topology, and the finite stalk is discrete, so every joint projected action is
continuous. This proves joint continuity on the module limit; composition with the
specified δ inverse gives the required action of P. The limit-map projection formula
and the linear path evaluation formula give exactly the recorded evaluation field.

For faithfulness, the supplied finite-etale equivalence and its fibre comparison
make the finite set-stalk functor faithful. If two tower maps induce the same limit
fibre map, surjectivity of every finite projection makes their level module-fibre
maps equal. Naturality of the canonical underlying-stalk comparison identifies the
underlying set-fibre maps. Finite set-stalk faithfulness gives equality of level
sheaf maps, and hence equality of towers. Transfer this faithfulness along the
identity natural comparison to T. -/
theorem canonical_integral_galois_functor_exists :
    Nonempty (IntegralGaloisForwardData y G c P δ l E) := by
  exact ⟨integralForwardData y G c l E P δ⟩

end AlgebraicGeometry.Scheme

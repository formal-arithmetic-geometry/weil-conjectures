/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-! # Adjoint tests for inverse images of tensor products

Source: Stacks Project, Modules on Sites, Tags 03D3, 03D7 and Section 03EK.
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtaleTensorComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Forget commutativity in the coefficient sheaf. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestRing {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- The existing module category on the original site. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
abbrev proEtaleTestModules {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  CategoryTheory.ringedSiteModules.{u + 1, u + 1, u, u + 1} (proEtaleTestRing R)

/-- Forget the module structure to sets. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestUnderlying {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf (proEtaleTestRing R) ⋙
    sheafCompose (ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- The recorded sheafified sectionwise tensor, at the original site universes.
Source: Stacks 03EK (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestTensor {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N : proEtaleTestModules R) :=
  (SheafOfModules.siteSheafTensorRight N).obj M

/-- The sheafification image of a pure tensor. Source: Stacks 03EK
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestPure {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N : proEtaleTestModules R) (V : T.ProEtᵒᵖ)
    (s : M.val.obj V) (t : N.val.obj V) :=
  SheafOfModules.siteSheafTensorTmul M N V s t

/-- Direct image of modules with the action induced by the actual ring-adjunction unit.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestDirectImage {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange h)
    (J := ProEt.topology T) (K := ProEt.topology T')
    (S := proEtaleTestRing R)
    (R := proEtaleTestRing ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The original-unit section, evaluated in the already specified small-model construction.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestUnitSection {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : proEtaleTestModules R) (V : T.ProEtᵒᵖ) (s : M.val.obj V) :
    ((proEtaleModuleInverseImage h R).obj M).val.obj
      (op ((proEtaleBaseChange h).obj V.unop)) :=
  inverseSection h M V.unop s


private theorem module_hom_ext {T : Scheme.{u}} {R : Rings T} {M N : Modules R}
    (a b : M ⟶ N) (h : ∀ (V : T.ProEtᵒᵖ) (s : M.val.obj V),
      a.val.app V s = b.val.app V s) : a = b := by
  ext V s
  exact h V s

private theorem directImage_map_apply {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Rings T} {K K' : Modules (inverseRing h R)} (k : K ⟶ K')
    (V : T.ProEtᵒᵖ) (s : K.val.obj (op ((proEtaleBaseChange h).obj V.unop))) :
    ((proEtaleTestDirectImage h R).map k).val.app V s =
      k.val.app (op ((proEtaleBaseChange h).obj V.unop)) s := rfl

private noncomputable def fromModelHomEquiv {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A))
    (N : SheafOfModules.{u + 1} A) :
    ((proEtaleModuleFromModel A).obj P ⟶ N) ≃
      (P ⟶ (proEtaleModuleToModel A).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.down.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.up.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl


section TestAdjunction

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y)

private noncomputable def directEquiv
    (M : Modules R) (N : Modules (inverseRing f R)) :
    ((proEtaleModuleToModel (proEtaleTestRing R)).obj M ⟶
      (SheafOfModules.pushforward (proEtaleModelRingUnit f R)).obj
        ((proEtaleModuleToModel (proEtaleTestRing (inverseRing f R))).obj N)) ≃
      (M ⟶ (proEtaleTestDirectImage f R).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.up.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.down.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
private noncomputable def homEquiv
    (M : Modules R) (N : Modules (inverseRing f R)) :
    ((proEtaleModuleInverseImage f R).obj M ⟶ N) ≃ (M ⟶ (proEtaleTestDirectImage f R).obj N) :=
  (fromModelHomEquiv _ _ _).trans
    (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).homEquiv
      _ _).trans (directEquiv f R M N))
private theorem homEquiv_left
    (M M' : Modules R) (N : Modules (inverseRing f R))
    (k : M ⟶ M') (h : (proEtaleModuleInverseImage f R).obj M' ⟶ N) :
    homEquiv f R M N ((proEtaleModuleInverseImage f R).map k ≫ h) =
      k ≫ homEquiv f R M' N h := by
  have hn := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).homEquiv_naturality_left
    ((proEtaleModuleToModel (proEtaleTestRing R)).map k) (fromModelHomEquiv _ _ _ h)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact congrArg (fun z ↦ z.val.app (AsSmall.up.op.obj U) m) hn
private theorem homEquiv_right
    (M : Modules R) (N N' : Modules (inverseRing f R))
    (k : N ⟶ N') (h : (proEtaleModuleInverseImage f R).obj M ⟶ N) :
    homEquiv f R M N' (h ≫ k) =
      homEquiv f R M N h ≫ (proEtaleTestDirectImage f R).map k := by
  have hn := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).homEquiv_naturality_right
    (fromModelHomEquiv _ _ _ h)
      ((proEtaleModuleToModel (proEtaleTestRing (inverseRing f R))).map k)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact congrArg (fun z ↦ z.val.app (AsSmall.up.op.obj U) m) hn
@[irreducible] private noncomputable def testAdj :
    proEtaleModuleInverseImage f R ⊣ proEtaleTestDirectImage f R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f R
      homEquiv_naturality_left_symm := by
        intro M M' N k h
        apply (homEquiv f R M N).injective
        rw [Equiv.apply_symm_apply, homEquiv_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun h k ↦ homEquiv_right f R _ _ _ k h }
private theorem testAdj_homEquiv :
    (testAdj f R).homEquiv = homEquiv f R := by
  rw [testAdj, Adjunction.mkOfHomEquiv_homEquiv]
-- The Hom equivalence makes the module unit literally the model unit on sections.
private theorem testAdj_unit_apply
    (M : SheafOfModules.{u + 1} (proEtaleTestRing R)) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
    ((testAdj f R).unit.app M).val.app U m =
      ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel _).obj M)).val.app (AsSmall.up.op.obj U) m := by
  rw [← (testAdj f R).homEquiv_id M, testAdj_homEquiv]
  change ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).homEquiv
    ((proEtaleModuleToModel (proEtaleTestRing R)).obj M) _
    (fromModelHomEquiv _ _ _ (𝟙 ((proEtaleModuleInverseImage f R).obj M)))).val.app
      (AsSmall.up.op.obj U) m = _
  rw [Adjunction.homEquiv_unit]
  rfl

end TestAdjunction

/-- The specified unit sections assemble into a unique module morphism.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof: evaluate the small-model adjunction unit on every original site object.
Its components are linear through the ring unit. Its naturality equation, transported
back along AsSmall.up, is exactly the required module naturality. Sectionwise
extensionality proves uniqueness. This assembles existing data without choosing an action. -/
theorem proEtaleTestModuleUnit_exists {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (M : proEtaleTestModules R) :
    ∃! η : M ⟶ (proEtaleTestDirectImage h R).obj
        ((proEtaleModuleInverseImage h R).obj M),
      ∀ (V : T.ProEtᵒᵖ) (s : M.val.obj V),
        η.val.app V s = proEtaleTestUnitSection h M V s := by
  refine ⟨(testAdj h R).unit.app M, ?_, ?_⟩
  · exact testAdj_unit_apply h R M
  · intro a ha
    apply module_hom_ext (R := R)
    intro V s
    exact (ha V s).trans (testAdj_unit_apply h R M V s).symm

/-- The unique module map with the actual adjunction-unit components.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestModuleUnit {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (M : proEtaleTestModules R) :
    M ⟶ (proEtaleTestDirectImage h R).obj ((proEtaleModuleInverseImage h R).obj M) :=
  Classical.choose (proEtaleTestModuleUnit_exists h R M)

private theorem testUnit_eq {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Rings T) (M : Modules R) :
    proEtaleTestModuleUnit h R M = (testAdj h R).unit.app M :=
  ((Classical.choose_spec (proEtaleTestModuleUnit_exists h R M)).2 _
    (testAdj_unit_apply h R M)).symm

/-- The module-valued expression `h_* α ∘ η`, using the specified constructions.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestAdjunct {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {M : proEtaleTestModules R}
    {K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)}
    (α : (proEtaleModuleInverseImage h R).obj M ⟶ K) :
    M ⟶ (proEtaleTestDirectImage h R).obj K :=
  proEtaleTestModuleUnit h R M ≫ (proEtaleTestDirectImage h R).map α

private theorem adjunct_eq {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Rings T} {M : Modules R} {K : Modules (inverseRing h R)}
    (α : (inverse h R).obj M ⟶ K) :
    proEtaleTestAdjunct h α = (testAdj h R).homEquiv M K α := by
  rw [Adjunction.homEquiv_unit]
  exact congrArg (fun e ↦ e ≫ (proEtaleTestDirectImage h R).map α) (testUnit_eq h R M)

private theorem adjunct_apply {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Rings T} {M : Modules R} {K : Modules (inverseRing h R)}
    (α : (inverse h R).obj M ⟶ K) (V : T.ProEtᵒᵖ) (s : M.val.obj V) :
    (proEtaleTestAdjunct h α).val.app V s =
      α.val.app (op ((proEtaleBaseChange h).obj V.unop))
        (proEtaleTestUnitSection h M V s) := by
  have e₁ : (proEtaleTestAdjunct h α).val.app V s =
      ((proEtaleTestDirectImage h R).map α).val.app V
        ((proEtaleTestModuleUnit h R M).val.app V s) := rfl
  exact e₁.trans ((directImage_map_apply h (R := R) α V _).trans
    (congrArg (fun x ↦ α.val.app (op ((proEtaleBaseChange h).obj V.unop)) x)
      ((Classical.choose_spec (proEtaleTestModuleUnit_exists h R M)).1 V s)))


/-- The Bilin set introduced in the statement: sectionwise R-bilinear maps commuting
with every restriction, equivalently morphisms from the product of the underlying sheaves.
Source: Stacks 03EK (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
def proEtaleTestBilin {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N H : proEtaleTestModules R) :=
  { β : ∀ V : T.ProEtᵒᵖ,
      M.val.obj V →ₗ[R.obj.obj V] N.val.obj V →ₗ[R.obj.obj V] H.val.obj V //
    ∀ {V W : T.ProEtᵒᵖ} (f : V ⟶ W) (s : M.val.obj V) (t : N.val.obj V),
      β W (M.val.map f s) (N.val.map f t) = H.val.map f (β V s t) }

private noncomputable def tensorPresheafEquiv {T : Scheme.{u}} {R : Rings T}
    (M N H : Modules R) :
    (SheafOfModules.siteTensorPresheaf M.val N.val ⟶ H.val) ≃ proEtaleTestBilin M N H where
  toFun f := ⟨fun V ↦ TensorProduct.curry (f.app V).hom, by
    intro V W i s t
    exact congrArg (fun z ↦ z (s ⊗ₜ[R.obj.obj V] t)) (f.naturality i)⟩
  invFun β :=
    { app := fun V ↦ ModuleCat.ofHom (TensorProduct.lift (β.val V))
      naturality := by
        intro V W i
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro s t
        exact β.property i s t }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    rfl
  right_inv β := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro t
    rfl

private noncomputable def tensorHomEquiv {T : Scheme.{u}} {R : Rings T}
    (M N H : Modules R) : (tensor M N ⟶ H) ≃ proEtaleTestBilin M N H :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology T)
    (R := proEtaleTestRing R) (𝟙 _)).homEquiv
      (SheafOfModules.siteTensorPresheaf M.val N.val) H).trans
        (tensorPresheafEquiv M N H)

private theorem tensorHomEquiv_apply {T : Scheme.{u}} {R : Rings T}
    (M N H : Modules R) (a : tensor M N ⟶ H) (V : T.ProEt)
    (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (tensorHomEquiv M N H a).val (op V) s t = a.val.app (op V) (pure M N V s t) := rfl

private theorem coefficientQuotient_pure {T : Scheme.{u}} {R S : Rings T} (φ : R ⟶ S)
    (M N : Modules S) (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (coefficientQuotient φ M N).val.app (op V)
      (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t) = pure M N V s t :=
  (Classical.choose_spec (coefficientQuotient_exists φ M N)).1 V s t

private theorem scalarIdentification_unit {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R S : Rings T} (φ : R ⟶ S) (M : Modules S) (V : T.ProEt)
    (s : M.val.obj (op V)) :
    (scalarIdentification h φ M).hom.val.app (op ((proEtaleBaseChange h).obj V))
      (inverseSection h ((restrict φ).obj M) V s) = inverseSection h M V s :=
  (Classical.choose_spec (scalarIdentification_exists h φ M)).1 V s

private theorem moduleSetsIdentification_unit {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Rings T} (M : Modules R) (V : T.ProEt) (s : M.val.obj (op V)) :
    (moduleSetsIdentification h M).hom.hom.app (op ((proEtaleBaseChange h).obj V))
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).unit.app
        (moduleSets M)).hom.app (op V) s) = inverseSection h M V s :=
  (Classical.choose_spec (moduleSetsIdentification_exists h M)).1 V s

private theorem inverseSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} (k : M ⟶ N) (V : Y.ProEt)
    (m : M.val.obj (op V)) :
    ((inverse f R).map k).val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f M V m) = inverseSection f N V (k.val.app (op V) m) := by
  have hn := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).unit.naturality
      ((proEtaleModuleToModel (proEtaleTestRing R)).map k)
  exact (congrArg (fun z ↦ z.val.app
    (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)) m) hn).symm

private theorem tensorMap_pure {T : Scheme.{u}} {R : Rings T}
    {M M' N N' : Modules R} (a : M ⟶ M') (b : N ⟶ N')
    (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (tensorMap a b).val.app (op V) (pure M N V s t) =
      pure M' N' V (a.val.app (op V) s) (b.val.app (op V) t) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology T)
    (R := proEtaleTestRing R) (𝟙 _)
  let q := SheafOfModules.siteTensorHom a.val N.val ≫
    SheafOfModules.siteTensorSecondMap M'.val b.val
  have hn := adj.unit.naturality q
  have hh := congrArg (fun z ↦ z.app (op V) (s ⊗ₜ[R.obj.obj (op V)] t)) hn
  change _ = (((adj.unit.app (SheafOfModules.siteTensorPresheaf M'.val N'.val)).app
    (op V)) ((a.val.app (op V) s) ⊗ₜ[R.obj.obj (op V)] (b.val.app (op V) t)))
  let L := PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology T)
    (R := proEtaleTestRing R) (𝟙 _)
  change (L.map (SheafOfModules.siteTensorHom a.val N.val) ≫
    L.map (SheafOfModules.siteTensorSecondMap M'.val b.val)).val.app (op V)
      (pure M N V s t) = _
  rw [← L.map_comp]
  exact hh.symm

private theorem pure_restrict {T : Scheme.{u}} {R : Rings T} (M N : Modules R)
    {V W : T.ProEtᵒᵖ} (f : V ⟶ W) (s : M.val.obj V) (t : N.val.obj V) :
    (tensor M N).val.map f (SheafOfModules.siteSheafTensorTmul M N V s t) =
      SheafOfModules.siteSheafTensorTmul M N W (M.val.map f s) (N.val.map f t) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology T)
    (R := proEtaleTestRing R) (𝟙 _)
  exact (congrArg (fun z ↦ z (s ⊗ₜ[R.obj.obj V] t))
    ((adj.unit.app (SheafOfModules.siteTensorPresheaf M.val N.val)).naturality f)).symm

/-- The adjoint bilinear test, with the specified set-sheaf adjunct and full naturality.
Source: Stacks 03D3, 03D7 and Section 03EK
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof:
1. Identify the geometric-module functors with the specified inverse and direct images,
using their transported addition and scalar actions. The direct action is through η_R.
2. geometric_module_transport gives the module Hom bijection and identifies its
underlying map with h_*α composed with η. The forward linearity follows from linearity
of the unit and α; the inverse linearity follows from the transport theorem, without
any assertion about generation by original sections. Naturality gives the two formulas.
3. Compose this bijection with tensor_bilinear_universal on the original site (transport
to its small model if needed). A bilinear sheaf map is exactly a restriction-compatible
family of sectionwise curried linear maps. Its formula is evaluation on the original
unit pure tensors. This is a bijection and is natural in all three modules, since
(u tensor v)(s tensor t) = u(s) tensor v(t).
4. Injectivity of that bijection gives the equality test. The converse follows by
substitution. No generation of sections on arbitrary target-site objects is used. -/
theorem proEtale_inverseImage_tensor_adjoint_test {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)),
      Function.Bijective (fun α :
        (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K ↦
          proEtaleTestAdjunct h α)) ∧
    (∀ (M N M' N' : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (a : M ⟶ M') (b : N ⟶ N')
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M' N') ⟶ K),
      proEtaleTestAdjunct h
          ((proEtaleModuleInverseImage h R).map (tensorMap a b) ≫ α) =
        tensorMap a b ≫ proEtaleTestAdjunct h α) ∧
    (∀ (M N : proEtaleTestModules R)
      (K K' : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) (k : K ⟶ K'),
      proEtaleTestAdjunct h (α ≫ k) =
        proEtaleTestAdjunct h α ≫ (proEtaleTestDirectImage h R).map k) ∧
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K),
      (proEtaleTestUnderlying R).map (proEtaleTestAdjunct h α) =
        (proEtaleSheafAdjunction h (Type (u + 1))).homEquiv _ _
          ((moduleSetsIdentification h (proEtaleTestTensor M N)).hom ≫
            (proEtaleTestUnderlying
              ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)).map α)) ∧
    (∃ E : ∀ (M N : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)),
        ((proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) ≃
          proEtaleTestBilin M N ((proEtaleTestDirectImage h R).obj K),
      (∀ (M N : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K)
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K α).val V s t = α.val.app (op ((proEtaleBaseChange h).obj V.unop))
          (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
            (proEtaleTestPure M N V s t))) ∧
      (∀ (M N M' N' : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (a : M ⟶ M') (b : N ⟶ N')
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M' N') ⟶ K)
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K ((proEtaleModuleInverseImage h R).map (tensorMap a b) ≫ α)).val V s t =
          (E M' N' K α).val V (a.val.app V s) (b.val.app V t)) ∧
      (∀ (M N : proEtaleTestModules R)
        (K K' : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) (k : K ⟶ K')
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K' (α ≫ k)).val V s t =
          k.val.app (op ((proEtaleBaseChange h).obj V.unop)) ((E M N K α).val V s t))) ∧
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α β : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K),
      α = β ↔ ∀ (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        α.val.app (op ((proEtaleBaseChange h).obj V.unop))
            (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
              (proEtaleTestPure M N V s t)) =
          β.val.app (op ((proEtaleBaseChange h).obj V.unop))
            (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
              (proEtaleTestPure M N V s t))) := by
  have hleft (M M' : Modules R) (K : Modules (inverseRing h R))
      (a : M ⟶ M') (α : (inverse h R).obj M' ⟶ K) :
      proEtaleTestAdjunct h ((inverse h R).map a ≫ α) =
        a ≫ proEtaleTestAdjunct h α := by
    simp only [adjunct_eq, Adjunction.homEquiv_naturality_left]
  have hright (M : Modules R) (K K' : Modules (inverseRing h R))
      (α : (inverse h R).obj M ⟶ K) (k : K ⟶ K') :
      proEtaleTestAdjunct h (α ≫ k) =
        proEtaleTestAdjunct h α ≫ (proEtaleTestDirectImage h R).map k := by
    simp only [adjunct_eq, Adjunction.homEquiv_naturality_right]
  let E (M N : Modules R) (K : Modules (inverseRing h R)) :
      ((inverse h R).obj (tensor M N) ⟶ K) ≃
        proEtaleTestBilin M N ((proEtaleTestDirectImage h R).obj K) :=
    ((testAdj h R).homEquiv (tensor M N) K).trans
      (tensorHomEquiv M N ((proEtaleTestDirectImage h R).obj K))
  have hE (M N : Modules R) (K : Modules (inverseRing h R))
      (α : (inverse h R).obj (tensor M N) ⟶ K) (V : T.ProEtᵒᵖ)
      (s : M.val.obj V) (t : N.val.obj V) :
      (E M N K α).val V s t = α.val.app (op ((proEtaleBaseChange h).obj V.unop))
        (proEtaleTestUnitSection h (tensor M N) V (proEtaleTestPure M N V s t)) := by
    change (tensorHomEquiv M N _ ((testAdj h R).homEquiv _ _ α)).val V s t = _
    rw [← adjunct_eq, tensorHomEquiv_apply, adjunct_apply]
  refine ⟨?_, ?_, ?_, ?_, ⟨E, hE, ?_, ?_⟩, ?_⟩
  · intro M N K
    simpa only [adjunct_eq] using ((testAdj h R).homEquiv (tensor M N) K).bijective
  · intro M N M' N' K a b α
    exact hleft _ _ _ _ _
  · intro M N K K' α k
    exact hright _ _ _ _ _
  · intro M N K α
    ext V s
    change (proEtaleTestAdjunct h α).val.app V s =
      α.val.app _ ((moduleSetsIdentification h (tensor M N)).hom.hom.app _
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).unit.app
          (moduleSets (tensor M N))).hom.app V s))
    rw [adjunct_apply]
    exact congrArg (fun x ↦ α.val.app (op ((proEtaleBaseChange h).obj V.unop)) x)
      (moduleSetsIdentification_unit h (tensor M N) V.unop s).symm
  · intro M N M' N' K a b α V s t
    change (tensorHomEquiv M N _ ((testAdj h R).homEquiv _ _
      ((inverse h R).map (tensorMap a b) ≫ α))).val V s t = _
    rw [← adjunct_eq, hleft, tensorHomEquiv_apply]
    change (proEtaleTestAdjunct h α).val.app V
      ((tensorMap a b).val.app V (pure M N V.unop s t)) = _
    rw [tensorMap_pure, adjunct_eq]
    exact (tensorHomEquiv_apply M' N' _ _ V.unop _ _).symm
  · intro M N K K' α k V s t
    rw [hE, hE]
    rfl
  · intro M N K α β
    constructor
    · rintro rfl
      intros
      rfl
    · intro hab
      apply (E M N K).injective
      apply Subtype.ext
      funext V
      apply LinearMap.ext
      intro s
      apply LinearMap.ext
      intro t
      rw [hE, hE]
      exact hab V s t



private theorem coefficient_tensorMap_pure {T : Scheme.{u}} {R S : Rings T}
    (c : R ⟶ S) {M N : Modules R} (P Q : Modules S)
    (a : M ⟶ (restrict c).obj P) (b : N ⟶ (restrict c).obj Q)
    (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V))
    (p : P.val.obj (op V)) (q : Q.val.obj (op V))
    (ha : a.val.app (op V) s = p) (hb : b.val.app (op V) t = q) :
    (tensorMap a b ≫ coefficientQuotient c P Q).val.app (op V) (pure M N V s t) =
      pure P Q V p q := by
  change (coefficientQuotient c P Q).val.app (op V)
    ((tensorMap a b).val.app (op V) (pure M N V s t)) = _
  rw [tensorMap_pure, coefficientQuotient_pure, ha, hb]

private theorem coefficient_tensorMap_restrict {T : Scheme.{u}} {R S : Rings T}
    (c : R ⟶ S) {M N : Modules R} (P Q : Modules S)
    (a : M ⟶ (restrict c).obj P) (b : N ⟶ (restrict c).obj Q)
    (V W : T.ProEtᵒᵖ) (i : W ⟶ V)
    (s : M.val.obj V) (t : N.val.obj V)
    (p : P.val.obj W) (q : Q.val.obj W)
    (ha : a.val.app V s = P.val.map i p)
    (hb : b.val.app V t = Q.val.map i q) :
    (tensorMap a b ≫ coefficientQuotient c P Q).val.app V (pure M N V.unop s t) =
      (tensor P Q).val.map i (pure P Q W.unop p q) := by
  exact (coefficient_tensorMap_pure c P Q a b V.unop s t
    (P.val.map i p) (Q.val.map i q) ha hb).trans
      (pure_restrict P Q i p q).symm

/-- Coefficient-change evaluations for supplied normalized maps. The quotient and scalar
identifications are the existing uniquely characterized canonical maps, not supplied
arbitrary arrows. Source: Stacks 03EK, and original parent proof step 4
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof: naturality of the unit with the coefficient quotient sends the original unit
pure tensor to the larger-ring pure tensor. The scalar identification preserves unit
sections. Applying the supplied larger-ring b gives the displayed target value. On
the other route the supplied smaller-ring b first gives the smaller-ring pure tensor;
tensorMap of the scalar identifications and then the canonical quotient give precisely
the same larger-ring pure tensor. Only the two supplied normalization equations are used. -/
theorem proEtale_inverseImage_tensor_coefficient_evaluations
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (b : ∀ (S : Rings T) (P Q : Modules S),
      (inverse h S).obj (tensor P Q) ⟶ tensor ((inverse h S).obj P) ((inverse h S).obj Q))
    (hb : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (b S P Q).val.app (op ((proEtaleBaseChange h).obj V))
          (inverseSection h (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse h S).obj P) ((inverse h S).obj Q) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V s) (inverseSection h Q V t))
    {R S : Rings T} (φ : R ⟶ S) (M N : Modules S)
    (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (((inverse h R).map (coefficientQuotient φ M N) ≫
        (scalarIdentification h φ (tensor M N)).hom ≫
        (restrict (inverseRingMap h φ)).map (b S M N)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
              (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)) =
      pure ((inverse h S).obj M) ((inverse h S).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) ∧
    ((b R ((restrict φ).obj M) ((restrict φ).obj N) ≫
        tensorMap (scalarIdentification h φ M).hom (scalarIdentification h φ N).hom ≫
        coefficientQuotient (inverseRingMap h φ)
          ((inverse h S).obj M) ((inverse h S).obj N)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
              (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)) =
      pure ((inverse h S).obj M) ((inverse h S).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) := by
  constructor
  · change (b S M N).val.app _
      ((scalarIdentification h φ (tensor M N)).hom.val.app _
        (((inverse h R).map (coefficientQuotient φ M N)).val.app _
          (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
            (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)))) = _
    rw [inverseSection_map, coefficientQuotient_pure, scalarIdentification_unit, hb]
  · change (coefficientQuotient (inverseRingMap h φ)
      ((inverse h S).obj M) ((inverse h S).obj N)).val.app _
        ((tensorMap (scalarIdentification h φ M).hom
          (scalarIdentification h φ N).hom).val.app _
            ((b R ((restrict φ).obj M) ((restrict φ).obj N)).val.app _
              (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
                (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)))) = _
    rw [hb, tensorMap_pure, coefficientQuotient_pure, scalarIdentification_unit,
      scalarIdentification_unit]


set_option linter.unusedVariables false in
private theorem composition_evaluations_aux
    {T'' T' T : Scheme.{u}} (g : T'' ⟶ T') (h : T' ⟶ T)
    (R : Rings T)
    (δ : AlgebraicGeometry.ProEtale.setPullback (g ≫ h) ≅
      AlgebraicGeometry.ProEtale.setPullback h ⋙ AlgebraicGeometry.ProEtale.setPullback g)
    (hδ : ∀ H : Sheaf (ProEt.topology T) (Type (u + 1)),
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStar (Type (u + 1)) (g ≫ h)).map (δ.hom.app H) =
        ((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).comp
          (AlgebraicGeometry.ProEtale.setPullbackAdjunction g)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStarComp (Type (u + 1)) g h).hom.app
            ((AlgebraicGeometry.ProEtale.setPullback h ⋙
              AlgebraicGeometry.ProEtale.setPullback g).obj H))
    (c : inverseRing (g ≫ h) R ≅ inverseRing g (inverseRing h R))
    (hc : (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets c.hom =
      δ.hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom)
    (d : ∀ P : Modules R, (inverse (g ≫ h) R).obj P ≅
      (restrict c.hom).obj ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)))
    (hd : ∀ P : Modules R,
      (moduleSetsIdentification (g ≫ h) P).hom ≫ moduleMapSets (d P).hom =
        δ.hom.app (moduleSets P) ≫
          (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
          (moduleSetsIdentification g ((inverse h R).obj P)).hom)
    (bh : ∀ (S : Rings T) (P Q : Modules S), (inverse h S).obj (tensor P Q) ⟶
      tensor ((inverse h S).obj P) ((inverse h S).obj Q))
    (bg : ∀ (S : Rings T') (P Q : Modules S), (inverse g S).obj (tensor P Q) ⟶
      tensor ((inverse g S).obj P) ((inverse g S).obj Q))
    (bc : ∀ (S : Rings T) (P Q : Modules S), (inverse (g ≫ h) S).obj (tensor P Q) ⟶
      tensor ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q))
    (hbh : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bh S P Q).val.app (op ((proEtaleBaseChange h).obj V))
          (inverseSection h (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse h S).obj P) ((inverse h S).obj Q) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V s) (inverseSection h Q V t))
    (hbg : ∀ (S : Rings T') (P Q : Modules S) (V : T'.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bg S P Q).val.app (op ((proEtaleBaseChange g).obj V))
          (inverseSection g (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse g S).obj P) ((inverse g S).obj Q)
          ((proEtaleBaseChange g).obj V) (inverseSection g P V s) (inverseSection g Q V t))
    (hbc : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bc S P Q).val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
          (inverseSection (g ≫ h) (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q)
          ((proEtaleBaseChange (g ≫ h)).obj V)
          (inverseSection (g ≫ h) P V s) (inverseSection (g ≫ h) Q V t))
    (M N : Modules R) (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (((d (tensor M N)).hom ≫
        (restrict c.hom).map ((inverse g (inverseRing h R)).map (bh R M N)) ≫
        (restrict c.hom).map
          (bg (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor (X := T'') (R := inverseRing g (inverseRing h R))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) ∧
    ((bc R M N ≫ tensorMap (d M).hom (d N).hom ≫ coefficientQuotient c.hom
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor (X := T'') (R := inverseRing g (inverseRing h R))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) := by
  let A := (proEtaleBaseChange (g ≫ h)).obj V
  let B := (proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V)
  let τ : op B ⟶ op A :=
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
  have hdunit (P : Modules R) (p : P.val.obj (op V)) :
      (d P).hom.val.app (op A) (inverseSection (g ≫ h) P V p) =
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)).val.map τ
          (inverseSection g ((inverse h R).obj P) ((proEtaleBaseChange h).obj V)
            (inverseSection h P V p)) := by
    let z := (AlgebraicGeometry.ProEtale.setPullback g).map
      (moduleSetsIdentification h P).hom ≫
        (moduleSetsIdentification g ((inverse h R).obj P)).hom
    let x := ((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).unit.app
      (moduleSets P)).hom.app (op V) p
    let y := ((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
      ((AlgebraicGeometry.ProEtale.setPullback h).obj (moduleSets P))).hom.app
        (op ((proEtaleBaseChange h).obj V)) x
    have hdv := congrArg (fun q ↦ q.hom.app (op A)
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app
        (moduleSets P)).hom.app (op V) p)) (hd P)
    have hδv := congrArg (fun q ↦ q.hom.app (op V) p) (hδ (moduleSets P))
    rw [Adjunction.comp_unit_app] at hδv
    have hn := congrArg (fun q ↦ q (y)) (z.hom.naturality τ)
    have hη := congrArg (fun q ↦ q.hom.app (op ((proEtaleBaseChange h).obj V)) x)
      ((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.naturality
        (moduleSetsIdentification h P).hom)
    have eh := moduleSetsIdentification_unit h P V p
    have eg := moduleSetsIdentification_unit g ((inverse h R).obj P)
      ((proEtaleBaseChange h).obj V) (inverseSection h P V p)
    have ec := moduleSetsIdentification_unit (g ≫ h) P V p
    change (moduleSetsIdentification (g ≫ h) P).hom.hom.app (op A) _ = _ at ec
    change (d P).hom.val.app (op A)
      ((moduleSetsIdentification (g ≫ h) P).hom.hom.app (op A) _) =
        z.hom.app (op A) ((δ.hom.app (moduleSets P)).hom.app (op A) _) at hdv
    rw [ec] at hdv
    change (δ.hom.app (moduleSets P)).hom.app (op A) _ =
      ((AlgebraicGeometry.ProEtale.setPullback h ⋙
        AlgebraicGeometry.ProEtale.setPullback g).obj (moduleSets P)).obj.map τ y at hδv
    have hdv' := hdv.trans (congrArg (fun t ↦ z.hom.app (op A) t) hδv)
    clear hdv
    have hdv := hdv'
    clear hdv'
    change z.hom.app (op A) (_ ) =
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)).val.map τ
        (z.hom.app (op B) y) at hn
    have hdv' := hdv.trans hn
    clear hdv
    have hdv := hdv'
    clear hdv'
    change ((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
      (moduleSets ((inverse h R).obj P))).hom.app (op ((proEtaleBaseChange h).obj V))
        ((moduleSetsIdentification h P).hom.hom.app (op ((proEtaleBaseChange h).obj V)) x) =
      ((AlgebraicGeometry.ProEtale.setPullback g).map
        (moduleSetsIdentification h P).hom).hom.app (op B) y at hη
    change _ = inverseSection h P V p at eh
    rw [eh] at hη
    change (moduleSetsIdentification g ((inverse h R).obj P)).hom.hom.app (op B) _ = _ at eg
    change (d P).hom.val.app (op A) _ =
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)).val.map τ
        ((moduleSetsIdentification g ((inverse h R).obj P)).hom.hom.app (op B)
          (((AlgebraicGeometry.ProEtale.setPullback g).map
            (moduleSetsIdentification h P).hom).hom.app (op B) y)) at hdv
    have hz : z.hom.app (op B) y =
        inverseSection g ((inverse h R).obj P) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V p) := by
      exact (congrArg (fun t ↦ (moduleSetsIdentification g ((inverse h R).obj P)).hom.hom.app
        (op B) t) hη.symm).trans eg
    exact hdv.trans (congrArg (fun t ↦
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)).val.map τ t) hz)
  constructor
  · change (bg (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N)).val.app (op A)
      (((inverse g (inverseRing h R)).map (bh R M N)).val.app (op A)
        ((d (tensor M N)).hom.val.app (op A)
          (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)))) = _
    rw [hdunit]
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    rw [inverseSection_map (X := T'') (Y := T') g
      (R := inverseRing h R) (bh R M N)]
    rw [hbh R M N V s t]
    exact congrArg (fun x ↦
      (tensor (X := T'') (R := inverseRing g (inverseRing h R))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map τ x)
      (hbg (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N)
        ((proEtaleBaseChange h).obj V) (inverseSection h M V s) (inverseSection h N V t))
  · have e₁ := congrArg (fun x ↦
      (tensorMap (d M).hom (d N).hom ≫ coefficientQuotient c.hom
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.app (op A) x)
        (hbc R M N V s t)
    have e₂ := coefficient_tensorMap_restrict (T := T'')
      (R := inverseRing (g ≫ h) R) (S := inverseRing g (inverseRing h R))
      (M := (inverse (g ≫ h) R).obj M) (N := (inverse (g ≫ h) R).obj N) c.hom
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
      (d M).hom (d N).hom (op A) (op B) τ
      (inverseSection (g ≫ h) M V s) (inverseSection (g ≫ h) N V t)
      (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s))
      (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h N V t)) (hdunit M s) (hdunit N t)
    exact e₁.trans e₂


-- The fixed statement includes ring compatibility; module normalization suffices below.
set_option linter.unusedVariables false in
/-- Composition evaluations for a supplied algebraic, unit-normalized set compositor.
The ring isomorphism c and module components d express exactly compatibility with the
transported operations: their underlying set maps are the supplied δ components. The
unit equation uses the canonical fibre-product associator via lowerStarComp. No
existence assertion for δ, b_h, b_g or b_hg is made.
Source: Stacks 03D2 and 03EK, and original parent proof step 7
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof:
1. The supplied unit equation for δ sends the composite unit image of s tensor t to
its iterated unit image, after restriction along the canonical associator. Its
algebraic compatibility gives exactly the same formula for d on modules.
2. Naturality of the g-unit with b_h sends that iterated image to the g-unit of
h-inverse(s) tensor h-inverse(t). These are sections on the original object h^*V
of the intermediate site, so the assumed normalization of b_g applies. The result
is the tensor of the two iterated unit images, restricted along the associator.
3. On the other route b_hg first gives the composite unit images of s and t. The
tensor map of d followed by the coefficient quotient sends them to the tensor of
their d-images. The supplied unit equation identifies these with the same iterated
unit images. Restriction commutes with the pure pairing. This proves both evaluated
equalities without assuming naturality or invertibility of any supplied b. -/
theorem proEtale_inverseImage_tensor_composition_evaluations
    {T'' T' T : Scheme.{u}} (g : T'' ⟶ T') (h : T' ⟶ T)
    (R : Rings T)
    (δ : AlgebraicGeometry.ProEtale.setPullback (g ≫ h) ≅
      AlgebraicGeometry.ProEtale.setPullback h ⋙ AlgebraicGeometry.ProEtale.setPullback g)
    (hδ : ∀ H : Sheaf (ProEt.topology T) (Type (u + 1)),
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStar (Type (u + 1)) (g ≫ h)).map (δ.hom.app H) =
        ((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).comp
          (AlgebraicGeometry.ProEtale.setPullbackAdjunction g)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStarComp (Type (u + 1)) g h).hom.app
            ((AlgebraicGeometry.ProEtale.setPullback h ⋙
              AlgebraicGeometry.ProEtale.setPullback g).obj H))
    (c : inverseRing (g ≫ h) R ≅ inverseRing g (inverseRing h R))
    (hc : (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets c.hom =
      δ.hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom)
    (d : ∀ P : Modules R, (inverse (g ≫ h) R).obj P ≅
      (restrict c.hom).obj ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)))
    (hd : ∀ P : Modules R,
      (moduleSetsIdentification (g ≫ h) P).hom ≫ moduleMapSets (d P).hom =
        δ.hom.app (moduleSets P) ≫
          (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
          (moduleSetsIdentification g ((inverse h R).obj P)).hom)
    (bh : ∀ (S : Rings T) (P Q : Modules S), (inverse h S).obj (tensor P Q) ⟶
      tensor ((inverse h S).obj P) ((inverse h S).obj Q))
    (bg : ∀ (S : Rings T') (P Q : Modules S), (inverse g S).obj (tensor P Q) ⟶
      tensor ((inverse g S).obj P) ((inverse g S).obj Q))
    (bc : ∀ (S : Rings T) (P Q : Modules S), (inverse (g ≫ h) S).obj (tensor P Q) ⟶
      tensor ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q))
    (hbh : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bh S P Q).val.app (op ((proEtaleBaseChange h).obj V))
          (inverseSection h (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse h S).obj P) ((inverse h S).obj Q) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V s) (inverseSection h Q V t))
    (hbg : ∀ (S : Rings T') (P Q : Modules S) (V : T'.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bg S P Q).val.app (op ((proEtaleBaseChange g).obj V))
          (inverseSection g (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse g S).obj P) ((inverse g S).obj Q)
          ((proEtaleBaseChange g).obj V) (inverseSection g P V s) (inverseSection g Q V t))
    (hbc : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bc S P Q).val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
          (inverseSection (g ≫ h) (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q)
          ((proEtaleBaseChange (g ≫ h)).obj V)
          (inverseSection (g ≫ h) P V s) (inverseSection (g ≫ h) Q V t))
    (M N : Modules R) (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (((d (tensor M N)).hom ≫
        (restrict c.hom).map ((inverse g (inverseRing h R)).map (bh R M N)) ≫
        (restrict c.hom).map
          (bg (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) ∧
    ((bc R M N ≫ tensorMap (d M).hom (d N).hom ≫ coefficientQuotient c.hom
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) := by
  exact composition_evaluations_aux g h R δ hδ c hc d hd bh bg bc hbh hbg hbc M N V s t

end AlgebraicGeometry.ProEtaleTensorComparison

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.AlgebraicGeometry.ProEtaleOperations

/-! # Inverse image along an isomorphism of schemes

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

## Main statements

- `proEtaleIsoPostcompose_equivalence`: the covering-preserving site equivalence.
- `existsUnique_proEtaleIsoInverseImageIdentification`: its normalized section identification.
- `proEtaleIsoInverseImage_equivalence`: equivalence and preservation of limits and colimits.
- `proEtaleIso_inverseLimitComparison`: the canonical inverse-limit comparison.
- `proEtaleIso_constantComparison`: invertible constant comparison and naturality.
- `proEtaleIso_constantModuleEquivalence`: the same equivalence for module sheaves.
- `proEtaleIso_constantRingModuleEquivalence`: module sheaves over any constant ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Change only the structure map of an object of the pro-etale site.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def proEtaleIsoPostcompose {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)

/-- The site equivalence and its specified inverse preserve covering families.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: compose structure maps with `f` or its inverse; the composites identify naturally
with the identity, with the identity on underlying schemes. These functors preserve weak
etaleness and coverings since the underlying schemes and covering arrows are unchanged. -/
theorem proEtaleIsoPostcompose_equivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsEquivalence ∧
      Nonempty (proEtaleIsoPostcompose f ⋙ proEtaleIsoPostcompose (inv f) ≅ 𝟭 X.ProEt) ∧
      Nonempty (proEtaleIsoPostcompose (inv f) ⋙ proEtaleIsoPostcompose f ≅ 𝟭 Y.ProEt) ∧
      Nonempty (CoverPreserving (ProEt.topology X) (ProEt.topology Y)
        (proEtaleIsoPostcompose f)) ∧
      Nonempty (CoverPreserving (ProEt.topology Y) (ProEt.topology X)
        (proEtaleIsoPostcompose (inv f))) := by
  let e₁ : proEtaleIsoPostcompose f ⋙ proEtaleIsoPostcompose (inv f) ≅ 𝟭 X.ProEt :=
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale f) (inferInstance : WeaklyEtale (inv f))).symm ≪≫
      MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (f ≫ inv f)
        (IsIso.hom_inv_id f)
  let e₂ : proEtaleIsoPostcompose (inv f) ⋙ proEtaleIsoPostcompose f ≅ 𝟭 Y.ProEt :=
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale (inv f)) (inferInstance : WeaklyEtale f)).symm ≪≫
      MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y (inv f ≫ f)
        (IsIso.inv_hom_id f)
  let E := CategoryTheory.Equivalence.mk (proEtaleIsoPostcompose f)
    (proEtaleIsoPostcompose (inv f)) e₁.symm e₂
  exact ⟨E.isEquivalence_functor, ⟨e₁⟩, ⟨e₂⟩,
    ⟨ProEt.coverPreserving_overMap (inferInstance : WeaklyEtale f)⟩,
    ⟨ProEt.coverPreserving_overMap (inferInstance : WeaklyEtale (inv f))⟩⟩

/-- The distinguished comma-category arrow `(u,id)` from the map/pullback adjunction.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoCommaArrow {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : X.ProEt) : U ⟶ (proEtaleBaseChange f).obj ((proEtaleIsoPostcompose f).obj U) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial).unit.app U

private theorem isoPostcompose_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)

attribute [local instance] isoPostcompose_continuous

private noncomputable def isoSheafAdjunction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D] :
    (proEtaleIsoPostcompose f).sheafPushforwardContinuous D
      (ProEt.topology X) (ProEt.topology Y) ⊣ proEtaleSheafDirectImage f D :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial).sheafPushforwardContinuous _ _

/-- The canonical identification is uniquely fixed by the coprojection at `(u,id)`.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the distinguished comma object is initial before taking opposites, hence terminal
in the colimit index. Its coprojection is invertible. The inverse evaluates each
coprojection by the unique arrow into that terminal object. The resulting presheaf is
already a sheaf because the site equivalence preserves covers and overlap schemes;
sheafification leaves it unchanged. The construction is natural in objects and sheaves.
The prescribed inverse determines the natural isomorphism uniquely. -/
theorem existsUnique_proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    ∃! e : proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
        sheafToPresheaf (ProEt.topology Y) D ⋙
          (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op,
      ∀ (F : Sheaf (ProEt.topology Y) D) (U : X.ProEt),
        (e.inv.app F).app (op U) =
          ((proEtaleSheafAdjunction f D).unit.app F).hom.app
              (op ((proEtaleIsoPostcompose f).obj U)) ≫
            ((proEtaleSheafInverseImage f D).obj F).obj.map
              (proEtaleIsoCommaArrow f U).op := by
  let a := proEtaleSheafAdjunction f D
  let b := isoSheafAdjunction f D
  let e := Functor.isoWhiskerRight (a.leftAdjointUniq b) (sheafToPresheaf (ProEt.topology X) D)
  refine ⟨e, ?_, ?_⟩
  · intro F U
    simp? [e, Adjunction.leftAdjointUniq, b, isoSheafAdjunction,
      proEtaleIsoCommaArrow, a, Adjunction.sheafPushforwardContinuous,
      Adjunction.whiskerLeft, Adjunction.op]
    erw [Category.id_comp]
  · intro e' h
    apply Iso.ext_inv
    ext F U
    exact (h F U.unop).trans (by
      simp? [e, Adjunction.leftAdjointUniq, b, isoSheafAdjunction,
        proEtaleIsoCommaArrow, a, Adjunction.sheafPushforwardContinuous,
        Adjunction.whiskerLeft, Adjunction.op]
      erw [Category.id_comp])

/-- The canonical section identification, natural both in the sheaf and in the site object.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
      sheafToPresheaf (ProEt.topology Y) D ⋙
        (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op :=
  (existsUnique_proEtaleIsoInverseImageIdentification f D).exists.choose

/-- The recorded adjunction is an equivalence, so its quasi-inverse is the recorded direct
image. Its inverse image preserves arbitrary limits and colimits, and is exact in the
abelian case by preservation of finite limits and colimits.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: both site functors are inverse equivalences preserving covers; the section
identification identifies inverse image with transport of sheaves. Thus the unit and
counit are isomorphisms, and an equivalence preserves every existing limit and colimit. -/
theorem proEtaleIsoInverseImage_equivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    (proEtaleSheafInverseImage f D).IsEquivalence ∧
      IsIso (proEtaleSheafAdjunction f D).unit ∧
      IsIso (proEtaleSheafAdjunction f D).counit ∧
      PreservesLimitsOfSize.{w', w} (proEtaleSheafInverseImage f D) ∧
      PreservesColimitsOfSize.{w', w} (proEtaleSheafInverseImage f D) := by
  let h := proEtaleIsoPostcompose_equivalence f
  let F := proEtaleIsoPostcompose f
  let G := proEtaleIsoPostcompose (inv f)
  let := Functor.isContinuous_comp F G (ProEt.topology X)
    (ProEt.topology Y) (ProEt.topology X)
  let := Functor.isContinuous_comp G F (ProEt.topology Y)
    (ProEt.topology X) (ProEt.topology Y)
  let E := CategoryTheory.Equivalence.mk
    (F.sheafPushforwardContinuous D (ProEt.topology X) (ProEt.topology Y))
    (G.sheafPushforwardContinuous D (ProEt.topology Y) (ProEt.topology X))
    ((Functor.sheafPushforwardContinuousComp G F D _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' h.2.2.1.some D _).symm)
    (Functor.sheafPushforwardContinuousComp F G D _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' h.2.1.some D _)
  let : (F.sheafPushforwardContinuous D (ProEt.topology X)
    (ProEt.topology Y)).IsEquivalence := E.isEquivalence_functor
  let : (proEtaleSheafDirectImage f D).IsEquivalence :=
    (isoSheafAdjunction f D).isEquivalence_right_of_isEquivalence_left
  let : (proEtaleSheafInverseImage f D).IsEquivalence :=
    (proEtaleSheafAdjunction f D).isEquivalence_left_of_isEquivalence_right
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The canonical comparison induced by the inverse images of all tower projections.
The indexing natural number `r` denotes the original positive index `r+1`.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the equivalence preserves the limit cone; its comparison `limit.post` is therefore
invertible. By its universal property its composites with the projections are exactly
the inverse images of the original projections. -/
theorem proEtaleIso_inverseLimitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D]
    (F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) D) [HasLimit F]
    [HasLimit (F ⋙ proEtaleSheafInverseImage f D)] :
    IsIso (limit.post F (proEtaleSheafInverseImage f D)) := by
  let := (proEtaleIsoInverseImage_equivalence.{u, v, 0, 0} f D).1
  infer_instance

private theorem constantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] [HasWeakSheafify (ProEt.topology Y) D]
    (A : D) : IsIso (proEtaleConstantInverseImageMap f D A) := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT : IsTerminal ((proEtaleBaseChange f).obj T) :=
    hT.isTerminalObj (proEtaleBaseChange f)
  let eR : proEtaleSheafDirectImage f D ⋙
      (sheafSections (ProEt.topology Y) D).obj (op T) ≅
        (sheafSections (ProEt.topology X) D).obj (op ((proEtaleBaseChange f).obj T)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let adj₁ := ((constantSheafAdj (ProEt.topology Y) D hT).comp
    (proEtaleSheafAdjunction f D)).ofNatIsoRight eR
  let adj₂ := constantSheafAdj (ProEt.topology X) D hGT
  let e := adj₁.leftAdjointUniq adj₂
  have he : proEtaleConstantInverseImageMap f D A = e.hom.app A := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj₁, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    unfold proEtaleConstantInverseImageMap
    rw [← Adjunction.homEquiv_symm_apply]
    simp only [eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
    change (constantSheafAdj (ProEt.topology Y) D hT).homEquiv _ _
      ((proEtaleSheafAdjunction f D).homEquiv _ _
        (((proEtaleSheafAdjunction f D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    unfold proEtaleConstantDirectImageMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj D hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [adj₂, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rw [Adjunction.homEquiv_apply]
    simp only [constantPresheafAdj_unit_app, Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- Constant coefficient comparisons are isomorphisms and natural in the coefficient
object; in particular this asserts the ring-sheaf statement for every commutative ring.
Source: Stacks Project, Tags 09A5, 00WX and 0H7J
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: under the canonical section identification the constant-presheaf map is the
identity. Sheafification preserves this identification. Naturality follows from the
naturality of the constant-presheaf map and the inverse-image adjunction counit. -/
theorem proEtaleIso_constantComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] [HasWeakSheafify (ProEt.topology Y) D] :
    (∀ A : D, IsIso (proEtaleConstantInverseImageMap f D A)) ∧
      ∀ (A B : D) (a : A ⟶ B),
        proEtaleConstantInverseImageMap f D A ≫
            (constantSheaf (ProEt.topology X) D).map a =
          (proEtaleSheafInverseImage f D).map
              ((constantSheaf (ProEt.topology Y) D).map a) ≫
            proEtaleConstantInverseImageMap f D B := by
  refine ⟨constantComparison_isIso f D, ?_⟩
  intro A B a
  symm
  let L := proEtaleSheafInverseImage f D
  let adj := proEtaleSheafAdjunction f D
  change L.map _ ≫ (adj.homEquiv _ _).symm _ =
    (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _)
    ((presheafToSheaf (ProEt.topology Y) D).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((proEtaleBaseChange f).op.obj U))
    ((toSheafification (ProEt.topology X) D).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

/-- The canonical ring-coefficient identification, with the recorded structure map as hom.
Source: Stacks Project, Tags 09A5 and 0H7J
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoConstantRingComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (A : CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A) ≅
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A :=
  @asIso _ _ _ _ (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A)
    ((proEtaleIso_constantComparison f CommRingCat.{u + 1}).1 A)

private noncomputable def isoBaseChangeEquivalence {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] : Y.ProEt ≌ X.ProEt := by
  let : (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale f)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence f).1
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial
  let : (proEtaleBaseChange f).IsEquivalence :=
    adj.isEquivalence_right_of_isEquivalence_left
  exact adj.toEquivalence.symm

private noncomputable def isoModulePushforwardEquivalence {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f]
    (RY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ρ : RY ⟶ (proEtaleSheafDirectImage f RingCat.{u + 1}).obj RX) [IsIso ρ] :
    SheafOfModules.{u + 1} RX ≌ SheafOfModules.{u + 1} RY := by
  let E := isoBaseChangeEquivalence f
  have : E.functor.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleBaseChange_isContinuous f
  have : E.inverse.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    isoPostcompose_continuous f
  let shAdj := E.toAdjunction.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology Y) (ProEt.topology X)
  let ψ : RX ⟶ (E.inverse.sheafPushforwardContinuous RingCat _ _).obj RY :=
    shAdj.unit.app RX ≫ (E.inverse.sheafPushforwardContinuous _ _ _).map (inv ρ)
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RX.obj =
      ψ.hom ≫ E.inverse.op.whiskerLeft ρ.hom := by
    ext U : 2
    simp [ψ, shAdj]
  have H₂ : ρ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RY.obj = 𝟙 RY.obj := by
    have hh : ρ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RY = 𝟙 RY := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality (inv ρ)]
      have ht := shAdj.left_triangle_components RX
      calc
        _ = ρ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RX) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RX)) ≫ inv ρ := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = ρ ≫ 𝟙 _ ≫ inv ρ := congrArg (fun h ↦ ρ ≫ h ≫ inv ρ) ht
        _ = _ := by simp
    exact congrArg (fun h ↦ h.hom) hh
  exact SheafOfModules.pushforwardPushforwardEquivalence E ρ ψ H₁ H₂

/-- For modules over any constant commutative ring, the specified tensor pullback and
sectionwise direct image are inverse equivalences. The unit and counit below specify the
quasi-inverse; the pullback already includes its canonical coefficient extension.
Source: Stacks Project, Tags 09A5, 00WX and 03D2
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the site equivalence transports module actions sectionwise, and the constant-ring
comparison is invertible. Tensor extension along it undoes restriction of scalars.
The two composites are the identity by the tensor unit isomorphisms and site equivalence. -/
theorem proEtaleIso_constantModuleEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (A : CommRingCat.{u + 1}) :
    (proEtaleRingModulePullback f
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
      (proEtaleIsoConstantRingComparison f A)).IsEquivalence ∧
    Nonempty (𝟭 _ ≅
      proEtaleRingModulePullback f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ⋙
      proEtaleRingModuleDirectImage f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A)) ∧
    Nonempty (proEtaleRingModuleDirectImage f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ⋙
      proEtaleRingModulePullback f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ≅ 𝟭 _) := by
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A
  let S := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A
  let c := proEtaleIsoConstantRingComparison f A
  let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
    f CommRingCat.{u + 1}).1
  have : IsIso (proEtaleRingDirectImageMap f R S c) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let ρ := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap f R S c)
  let E := isoModulePushforwardEquivalence f
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ρ
  let : (proEtaleRingModuleDirectImage f R S c).IsEquivalence := E.isEquivalence_functor
  let adj := (proEtaleRingModuleOperations_properties f R S c).2.2.2.2.some
  let : (proEtaleRingModulePullback f R S c).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  exact ⟨inferInstance, ⟨asIso adj.unit⟩, ⟨asIso adj.counit⟩⟩

/-- Module sheaves over an arbitrary constant ring are transported equivalently, with
the actual sectionwise direct image as inverse. No commutativity of the ring is needed.
Source: Stacks Project, Tags 09A5, 00YV, 0H7J and 03D2
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: postcomposition with `f` and its inverse gives inverse covering-preserving site
equivalences. Transport a module action along these equivalences. The constant-ring
identifications preserve every constant section, so the transported restriction maps are
semilinear and the resulting module maps are linear. Both composites are naturally the
identity, sectionwise by the identity on the underlying schemes. Direct image is exactly
precomposition by base change with scalars restricted along the recorded constant-section
map. Therefore it is the inverse functor of this equivalence; the forward functor is its
inverse-image left adjoint, determined up to the unique adjunction isomorphism. -/
theorem proEtaleIso_constantRingModuleEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (A : RingCat.{u + 1}) :
    ∃ e : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology Y) RingCat.{u + 1}).obj A) ≌
        ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj A),
      e.inverse = SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
        (J := ProEt.topology Y) (K := ProEt.topology X)
        (proEtaleConstantDirectImageMap f RingCat.{u + 1} A) := by
  let a := proEtaleSheafAdjunction f RingCat.{u + 1}
  let := (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} f RingCat.{u + 1}).1
  let := (proEtaleIso_constantComparison f RingCat.{u + 1}).1 A
  have hρ : proEtaleConstantDirectImageMap f RingCat.{u + 1} A =
      a.unit.app _ ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map
        (proEtaleConstantInverseImageMap f RingCat.{u + 1} A) := by
    exact (a.homEquiv _ _).apply_symm_apply
      (proEtaleConstantDirectImageMap f RingCat.{u + 1} A) |>.symm
  have : IsIso (proEtaleConstantDirectImageMap f RingCat.{u + 1} A) := by
    rw [hρ]
    infer_instance
  exact ⟨(isoModulePushforwardEquivalence f _ _
    (proEtaleConstantDirectImageMap f RingCat.{u + 1} A)).symm, rfl⟩

end AlgebraicGeometry.Scheme

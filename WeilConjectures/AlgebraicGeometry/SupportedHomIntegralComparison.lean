/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedHomResolutionComparison
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Integral transport of the normalized supported Hom comparison

Source: Stacks Tags 03FD and 06XR; the supported-Hom construction in the proof of
lem-amb-cartier-kummer-map (blueprint: lem-pur-supported-hom-integral-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
attribute [local instance] hasExt_of_enoughInjectives

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
private theorem integral_unit_apply (V : Y.Etale) (m : ULift.{u + 1} ℤ) :
    (integralUnitAux g).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ ((sheafSections
    Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj (AddCommGrpCat.of (ULift.{u + 1}
        ℤ)))) ≫ e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app (AddCommGrpCat.of
          (ULift.{u + 1} ℤ))) = adjZ.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1}
          ℤ)))).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1}
        ℤ)))).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u +
      1} ℤ)))).naturality
      f.op)).hom m)).symm
  let θ := integralUnitAux g
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj (AddCommGrpCat.of
    (ULift.{u + 1} ℤ))
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

set_option maxHeartbeats 1000000 in
-- The Cech comparison transports between the two sheaf encodings.
private lemma forgotten_injective_acyclic (B : Type (u + 1)) [CommRing B]
    (T : Scheme.{u}) (U : T.Etale)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) [Injective G] :
    (etaleSectionFunctor U).rightAcyclic ((moduleAbelianForget B T).obj G) := by
  obtain ⟨e, ⟨eAb⟩⟩ := AlgebraicGeometry.moduleSheaf_constantRing_equivalence B T
  let O := (sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of B))
  let I : SheafOfModules.{u + 1} O := e.functor.obj G
  have : Injective I := (e.map_injective_iff G).mpr inferInstance
  have htop : T.smallEtaleTopology.toPrecoverage.toGrothendieck =
      T.smallEtaleTopology := by
    apply le_antisymm
    · exact T.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let J := T.smallEtaleTopology.toPrecoverage
  have hcech (U : T.Etale) (ι : Type (u + 1)) (V : ι → T.Etale)
      (f : ∀ t : ι, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ T.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : ι ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨c⟩ := Scheme.nonempty_etale_siteCech_complex_iso T U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso c.symm)
  intro n
  have hz := Scheme.isZero_rightDerived_etale_of_cech_vanishing T Set.univ
    (fun U _ V f ↦ Sieve.ofArrows V f ∈ T.smallEtaleTopology U)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ V W f hf ↦ ⟨V, W, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech U (Set.mem_univ _) (n + 1) (Nat.succ_pos n)
  exact hz.of_iso (((etaleSectionFunctor U).rightDerived (n + 1)).mapIso (eAb.app G).symm)

private lemma sectionLift_quasiIso (B : Type (u + 1)) [CommRing B]
    (T : Scheme.{u}) (U : T.Etale)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F) (J : InjectiveResolution ((moduleAbelianForget B T).obj F))
    (t : ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      J.cocomplex)
    (ht : (moduleAbelianForget B T).map (I.ι.f 0) ≫ t.f 0 = J.ι.f 0) :
    QuasiIso (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map t) := by
  let A := moduleAbelianForget B T
  let E := etaleSectionFunctor U
  let hA := forgotten_injective_acyclic B T U
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hc := exact_comp_comparison_formula A E hA F I J t ht q
  have he : homologyMap ((E.mapHomologicalComplex (.up ℕ)).map t) q =
      (I.isoRightDerivedObj (A ⋙ E) q).inv ≫
        (exact_comp_comparison A E hA q).hom.app F ≫ (J.isoRightDerivedObj E q).hom := by
    rw [hc]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

private lemma coneMap_eq (A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    homotopyCofiber.mapArrowHom r r' (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk a b h) = CochainComplex.mappingCone.map r r' a b h.symm := by
  ext n : 1
  apply homotopyCofiber.ext_from_X r (n + 1) n rfl
  · conv_lhs =>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.inrCompHomotopy_hom]
    change a.f (n + 1) ≫ (CochainComplex.mappingCone.inl r').v (n + 1) n (by omega) =
      (CochainComplex.mappingCone.inl r).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone.map r r' a b h.symm).f n
    simp [CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
  · conv_lhs =>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.inrCompHomotopy_hom]
    change b.f n ≫ (CochainComplex.mappingCone.inr r').f n =
      (CochainComplex.mappingCone.inr r).f n ≫
        (CochainComplex.mappingCone.map r r' a b h.symm).f n
    simp [CochainComplex.mappingCone.map]

/-- The augmentation-compatible map from a forgotten module resolution is invertible
on relative cohomology. Source: Stacks Tag 03FD, relative cone five lemma
(blueprint: lem-pur-supported-hom-integral-comparison).
Proof: use the constant-ring module equivalence and forgotten injective acyclicity
at every etale object. The acyclic-resolution comparison makes the section maps at
T and W quasi-isomorphisms. Their commuting restriction square induces the displayed
cone map; the five lemma on its cone triangles makes it a quasi-isomorphism as well.
Extension by zero handles degree zero and negative degrees uniformly. -/
theorem supportedHomIntegralMap_isIso (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F) (J : InjectiveResolution ((moduleAbelianForget B T).obj F))
    (t : ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      J.cocomplex)
    (ht : (moduleAbelianForget B T).map (I.ι.f 0) ≫ t.f 0 = J.ι.f 0) (q : ℕ) :
    IsIso (homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) t)
      (q : ℤ)) := by
  let U := Scheme.Etale.mk i.openComplement.ι
  let K := ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let r := relativeSectionRestriction T U K
  let r' := relativeSectionRestriction T U J.cocomplex
  let a := extendMap
    (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map t)
      ComplexShape.embeddingUpNat
  let b := extendMap (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map t)
    ComplexShape.embeddingUpNat
  have h : a ≫ r' = r ≫ b := relativeSectionMap_square T U t
  have : QuasiIso a := by
    have := sectionLift_quasiIso B T (Scheme.Etale.mk (𝟙 T)) F I J t ht
    exact (quasiIso_extendMap_iff _ _).mpr inferInstance
  have : QuasiIso b := by
    have := sectionLift_quasiIso B T U F I J t ht
    exact (quasiIso_extendMap_iff _ _).mpr inferInstance
  have hm : QuasiIso (CochainComplex.mappingCone.map r r' a b h.symm) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso AddCommGrpCat.{u + 1} _).mp
    exact Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap r r' a b h.symm))
      (DerivedCategory.mappingCone_triangle_distinguished r)
      (DerivedCategory.mappingCone_triangle_distinguished r')
      (by exact inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
      (by exact inferInstanceAs (IsIso (DerivedCategory.Q.map b)))
  have : QuasiIso (relativeSectionMap T U t) := by
    change QuasiIso ((shiftFunctor _ (-1 : ℤ)).map
      (homotopyCofiber.mapArrowHom r r' (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
        (Arrow.homMk a b h)))
    rw [coneMap_eq]
    infer_instance
  infer_instance

private lemma sectionMap_forget (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) :
    relativeSectionMap T U a ≫ relativeForgetComplex T U J =
      relativeForgetComplex T U I ≫ HomologicalComplex.extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a)
        ComplexShape.embeddingUpNat := by
  let e := (shiftFunctorAdd' (CochainComplex AddCommGrpCat.{u + 1} ℤ)
      (1 : ℤ) (-1 : ℤ) 0 (by decide)).symm ≪≫
    shiftFunctorZero (CochainComplex AddCommGrpCat.{u + 1} ℤ) ℤ
  let f := HomologicalComplex.extendMap
    (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a)
    ComplexShape.embeddingUpNat
  change relativeSectionMap T U a ≫
      ((shiftFunctor _ (-1 : ℤ)).map _ ≫ e.hom.app _) =
    ((shiftFunctor _ (-1 : ℤ)).map _ ≫ e.hom.app _) ≫ f
  unfold relativeSectionMap relativeFiberMap
  rw [← Category.assoc, ← Functor.map_comp]
  erw [coneMap_fst]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact e.hom.naturality f


private lemma sectionMap_snd (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) (q : ℤ) :
    (relativeSectionMap T U a).f q ≫
      ((CochainComplex.mappingCone (relativeSectionRestriction T U J)).shiftFunctorObjXIso
        (-1) q (q + -1) rfl).hom ≫
          homotopyCofiber.sndX (relativeSectionRestriction T U J) (q + -1) =
    ((CochainComplex.mappingCone (relativeSectionRestriction T U I)).shiftFunctorObjXIso
        (-1) q (q + -1) rfl).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T U I) (q + -1) ≫
        (extendMap (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map a)
          ComplexShape.embeddingUpNat).f (q + -1) := by
  let r := relativeSectionRestriction T U I
  let r' := relativeSectionRestriction T U J
  let f := extendMap
    (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map a)
      ComplexShape.embeddingUpNat
  let g := extendMap (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map a)
    ComplexShape.embeddingUpNat
  have h := relativeSectionMap_square T U a
  change (homotopyCofiber.mapArrowHom r r'
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk f g h)).f (q + -1) ≫ homotopyCofiber.sndX r' (q + -1) =
        homotopyCofiber.sndX r (q + -1) ≫ g.f (q + -1)
  rw [coneMap_eq]
  apply homotopyCofiber.ext_from_X r (q + -1 + 1) (q + -1) rfl
  · change (CochainComplex.mappingCone.inl r).v (q + -1 + 1) (q + -1)
      (by omega) ≫
      (CochainComplex.mappingCone.map r r' f g h.symm).f (q + -1) ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    change f.f _ ≫ homotopyCofiber.inlX r' _ _ _ ≫ homotopyCofiber.sndX r' _ = _
    simp
  · change (CochainComplex.mappingCone.inr r).f (q + -1) ≫
      (CochainComplex.mappingCone.map r r' f g h.symm).f (q + -1) ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, comp_f]
    change g.f _ ≫ homotopyCofiber.inrX r' _ ≫ homotopyCofiber.sndX r' _ = _
    simp only [homotopyCofiber.inrX_sndX, homotopyCofiber.inrX_sndX_assoc]
    exact Category.comp_id _

private lemma extended_map_apply
    {I J : CochainComplex AddCommGrpCat.{u + 1} ℕ}
    (a : I ⟶ J) (q : ℕ) (x : I.X q) :
    (extendMap a ComplexShape.embeddingUpNat).f (q : ℤ)
        ((I.extendXIso ComplexShape.embeddingUpNat rfl).inv x) =
      (J.extendXIso ComplexShape.embeddingUpNat rfl).inv (a.f q x) := by
  have he := ConcreteCategory.congr_hom
    (extendMap_f a ComplexShape.embeddingUpNat (i := q) rfl)
    ((I.extendXIso ComplexShape.embeddingUpNat rfl).inv x)
  change (extendMap a ComplexShape.embeddingUpNat).f (q : ℤ)
      ((I.extendXIso ComplexShape.embeddingUpNat rfl).inv x) =
    (J.extendXIso ComplexShape.embeddingUpNat rfl).inv
      (a.f q ((I.extendXIso ComplexShape.embeddingUpNat rfl).hom
        ((I.extendXIso ComplexShape.embeddingUpNat rfl).inv x))) at he
  rw [Iso.inv_hom_id_apply] at he
  exact he

/-- The normalized supported Hom comparison commutes with the actual integral generator.
Source: Stacks Tags 03FD and 06XR; supported-Hom paragraph of lem-amb-cartier-kummer-map
(blueprint: lem-pur-supported-hom-integral-comparison).
Proof: represent the Ext class by a cocycle k. Exact-functor cocycle transport represents
its forgotten class by U(k) followed by t; precomposition gives gamma followed by U(k)
followed by t. The constant-generator identity gamma p_Z = U(p_B) eta is checked on
one and transported by sheafification. Thus the first cone coordinate is t applied to
module evaluation, and the second coordinate is zero. The normalization of the integral
comparison and naturality of homology projections give the asserted equality. -/
theorem supportedHomIntegralComparison (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (I : InjectiveResolution F) (J : InjectiveResolution ((moduleAbelianForget B T).obj F))
    (t : ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      J.cocomplex)
    (ht : (moduleAbelianForget B T).map (I.ι.f 0) ≫ t.f 0 = J.ι.f 0)
    (q : ℕ) (y : Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B))) F q) :
    relativeExtensionComparison i ((moduleAbelianForget B T).obj F) J q
      ((Ext.mk₀.{u + 1} (supportedIntegralGenerator B i)).comp
        (Ext.mapExactFunctor.{u + 1, u + 1} (moduleAbelianForget B T) y) (zero_add q)) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) t) (q : ℤ)
        (supportedHomResolutionComparison B i F I q y) := by
  let U := Scheme.Etale.mk i.openComplement.ι
  let A := moduleAbelianForget B T
  let K := (A.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let C := relativeSectionComplex T U K
  let D := relativeSectionComplex T U J.cocomplex
  let m := relativeSectionMap T U t
  obtain ⟨k, hk, rfl⟩ := I.extMk_surjective y (q + 1) rfl
  have hkt : (A.map k ≫ t.f q) ≫ J.cocomplex.d q (q + 1) = 0 := by
    calc
      _ = A.map k ≫ (A.map (I.cocomplex.d q (q + 1)) ≫ t.f (q + 1)) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun φ ↦ A.map k ≫ φ) (t.comm q (q + 1)))
      _ = A.map (k ≫ I.cocomplex.d q (q + 1)) ≫ t.f (q + 1) :=
        (A.map_comp_assoc _ _ _).symm
      _ = 0 := by rw [hk, A.map_zero, zero_comp]
  have hext := exactFunctor_resolution_cocycle.{_, _, _, _, u + 1, u + 1} A (𝟙 (A.obj F)) I J t
    (by simpa using ht) q k hk hkt
  rw [Ext.comp_mk₀_id] at hext
  rw [hext, InjectiveResolution.mk₀_comp_extMk]
  obtain ⟨z, hz₁, hz₂, hz₃⟩ := supportedHomResolutionComparison_normalized B i F I q k hk
  rw [hz₃]
  let w := cyclesMap m (q : ℤ) z
  have hw : D.iCycles q w = m.f q (C.iCycles q z) :=
    ConcreteCategory.congr_hom (cyclesMap_i m (q : ℤ)) z
  have hn := (Classical.choose_spec
    (relativeExtensionComparison_existsUnique i (A.obj F) J)).1.onCocycle q
      (supportedIntegralGenerator B i ≫ A.map k ≫ t.f q)
        (by rw [Category.assoc, hkt, comp_zero]) w
  have hfst : (relativeForgetComplex T U J.cocomplex).f q (D.iCycles q w) =
      (extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex) ComplexShape.embeddingUpNat rfl).inv
        ((supportedIntegralGenerator B i ≫ A.map k ≫ t.f q).hom.app
          (op (Scheme.Etale.mk (𝟙 T)))
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) := by
    rw [hw, ← ConcreteCategory.comp_apply, ← comp_f, sectionMap_forget, comp_f,
      ConcreteCategory.comp_apply, hz₁]
    refine (extended_map_apply
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).map t)
      q _).trans ?_
    apply congrArg (fun x ↦
      (extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex) ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv x)
    change (t.f q).hom.app _ ((A.map k).hom.app _
      ((supportedConstantUnit B i).hom.app _
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app _ (1 : B)))) =
      (t.f q).hom.app _ ((A.map k).hom.app _
        ((supportedIntegralUnit i ≫ supportedIntegralGenerator B i).hom.app _
          (supportedIntegralOne T)))
    rw [← coefficient_unit]
    change _ = (t.f q).hom.app _ ((A.map k).hom.app _
      ((supportedConstantUnit B i).hom.app _
        ((ordinaryFiniteIntegralGenerator B T).hom.app _ (supportedIntegralOne T))))
    have hg := generator_apply B T (Scheme.Etale.mk (𝟙 T)) (ULift.up 1)
    have hg' : (ordinaryFiniteIntegralGenerator B T).hom.app
        (op (Scheme.Etale.mk (𝟙 T))) (supportedIntegralOne T) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
          (op (Scheme.Etale.mk (𝟙 T))) (1 : B) := by
      simpa only [supportedIntegralOne, Int.cast_one] using hg
    exact congrArg (fun x ↦ (t.f q).hom.app _
      ((A.map k).hom.app _ ((supportedConstantUnit B i).hom.app _ x))) hg'.symm
  have hsnd : (((CochainComplex.mappingCone
        (relativeSectionRestriction T U J.cocomplex)).shiftFunctorObjXIso
          (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T U J.cocomplex) ((q : ℤ) + -1))
        (D.iCycles q w) = 0 := by
    let pI := ((CochainComplex.mappingCone
      (relativeSectionRestriction T U K)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T U K) ((q : ℤ) + -1)
    let pJ := ((CochainComplex.mappingCone
      (relativeSectionRestriction T U J.cocomplex)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T U J.cocomplex) ((q : ℤ) + -1)
    let g := (extendMap (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).map t)
      ComplexShape.embeddingUpNat).f ((q : ℤ) + -1)
    have he : pJ (m.f q (C.iCycles q z)) = g (pI (C.iCycles q z)) :=
      ConcreteCategory.congr_hom (sectionMap_snd T U t (q : ℤ)) (C.iCycles q z)
    have hi : pI (C.iCycles q z) = 0 := hz₂
    exact (congrArg (fun x ↦ pJ x) hw).trans
      (he.trans ((congrArg (fun x ↦ g x) hi).trans g.hom.map_zero))
  have he := hn hfst hsnd
  change relativeExtensionComparison i (A.obj F) J q
    (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} J
      (supportedIntegralGenerator B i ≫ A.map k ≫ t.f q) (q + 1) rfl _) =
      D.homologyπ q w at he
  exact he.trans (ConcreteCategory.congr_hom (homologyπ_naturality m (q : ℤ)) z).symm

end AlgebraicGeometry.Etale

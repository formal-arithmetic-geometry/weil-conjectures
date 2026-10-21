/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneLocalData
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import Sheaf.Paper.RankOneKummerGenerator
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-! # Ordinary finite-coefficient Kummer calculation

Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3,
and Section 16, Example 16.3; blueprint sk-prop-a1-kummer, Coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.homologyFunctor


open AlgebraicGeometry.Scheme

private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))


private noncomputable def finiteLineConstantIso
    (A : Type (u + 1)) [CommRing A] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {T : Scheme.{u}} (p : T ⟶ Spec (.of Ω)) (m : ℕ)
    (hA : (m : A) = 0) (hm : (m : Ω) ≠ 0) :
    finiteEtaleTateLine T m A hA ≅
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) :=
  finiteEtaleLineAbIso T m A hA ≪≫
    (Etale.extendScalars A T).mapIso
      (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf p hm).some.symm ≪≫
    Etale.extendScalarsConstantZModIso T hA

private noncomputable def evaluationHiso
    (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj
        (((sections X.smallEtaleTopology A (Scheme.Etale.mk j)).rightDerived q).obj F) ≅
      AddCommGrpCat.of (Sheaf.H
        ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj
          ((Etale.moduleAbelianForget A X).obj F)) q) := by
  have := (Etale.module_cohomology_conventions A X).2.1 F (Scheme.Etale.mk j) q
  exact asIso ((Etale.moduleEvaluationForgetComparison A X (Scheme.Etale.mk j) q).app F) ≪≫
    (evaluationExt X (Scheme.Etale.mk j) q).app ((Etale.moduleAbelianForget A X).obj F) ≪≫
      (etaleCohomologyOverOpenEquiv j ((Etale.moduleAbelianForget A X).obj F) q).toAddCommGrpIso

private noncomputable def restrictedConstantIso
    (A : Type (u + 1)) [CommRing A] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : F ≅ (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :
    (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj
        ((Etale.moduleAbelianForget A X).obj F) ≅
      (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)) :=
  (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).mapIso
      ((Etale.moduleAbelianForget A X).mapIso e ≪≫ Etale.forget₂SheafConstantSheafIso A X) ≪≫
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
      inferInstance).symm.app _) ≪≫
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} j).app _

private theorem constantSections_bijective
    (X : Scheme.{u}) (M : AddCommGrpCat.{u + 1}) (T : X.Etale)
    [ConnectedSpace T.left] :
    Function.Bijective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op T)) := by
  let ψ := (X.constantSheafToPointFunctionSheaf M).hom.app (op T)
  have hψ : Function.Injective ψ := by
    have : Mono ((sheafToPresheaf _ _).map (X.constantSheafToPointFunctionSheaf M)) :=
      Functor.map_mono _ _
    have : Mono ψ := (NatTrans.mono_iff_mono_app _).1 this (op T)
    exact (AddCommGrpCat.mono_iff_injective _).1 this
  obtain ⟨x₀⟩ := ‹ConnectedSpace T.left›.toNonempty
  refine ⟨fun m m' h ↦ ?_, fun σ ↦ ?_⟩
  · exact congrFun ((Scheme.constantSheafToPointFunctionSheaf_app_toSheafify X M T m).symm.trans
      ((congrArg ψ h).trans (Scheme.constantSheafToPointFunctionSheaf_app_toSheafify X M T m'))) x₀
  · let D : T.left → M := ψ σ
    have hloc : IsLocallyConstant D := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
        (Presheaf.imageSieve_mem X.smallEtaleTopology
          (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) σ) x
      have hD (w' : W.left) : D (g.left w') = m := by
        have h₁ := congrArg (fun s ↦ (X.constantSheafToPointFunctionSheaf M).hom.app (op W) s w') hm
        have h₂ := NatTrans.naturality_apply (X.constantSheafToPointFunctionSheaf M).hom g.op σ
        simp only at h₁
        rw [Scheme.constantSheafToPointFunctionSheaf_app_toSheafify] at h₁
        exact (congrFun h₂ w').symm.trans h₁.symm
      have hEtale : AlgebraicGeometry.Etale g.left :=
        MorphismProperty.of_postcomp @AlgebraicGeometry.Etale g.left T.hom T.prop
          (by simpa only [MorphismProperty.Over.w] using W.prop)
      refine ⟨Set.range g.left, g.left.isOpenMap.isOpen_range, ⟨w, hgw⟩, ?_⟩
      · rintro _ ⟨w', rfl⟩
        rw [hD, ← hgw, hD]
    refine ⟨D x₀, hψ ?_⟩
    rw [Scheme.constantSheafToPointFunctionSheaf_app_toSheafify]
    funext x
    exact hloc.apply_eq_of_preconnectedSpace x₀ x


private theorem constantRestriction_isIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {V W : X.Etale} (j : W ⟶ V) [ConnectedSpace V.left] [ConnectedSpace W.left] :
    IsIso (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)).obj.map j.op) := by
  let M := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let Cmod := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let t := CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  have hV : IsIso (t.app (op V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (constantSections_bijective X M V)
  have hW : IsIso (t.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (constantSections_bijective X M W)
  have hres : C.obj.map j.op = inv (t.app (op V)) ≫ t.app (op W) := by
    have hn : t.app (op W) = t.app (op V) ≫ C.obj.map j.op := by
      have h := t.naturality j.op
      change 𝟙 M ≫ t.app (op W) = t.app (op V) ≫ C.obj.map j.op at h
      exact (Category.id_comp _).symm.trans h
    rw [hn, IsIso.inv_hom_id_assoc]
  have : IsIso (C.obj.map j.op) := by rw [hres]; infer_instance
  let e := Etale.forget₂SheafConstantSheafIso A X
  have heq : ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      (Cmod.obj.map j.op)) = e.hom.hom.app (op V) ≫ C.obj.map j.op ≫
        e.inv.hom.app (op W) := by
    let ee := (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e
    have heW : e.inv.hom.app (op W) ≫ e.hom.hom.app (op W) = 𝟙 _ :=
      Iso.inv_hom_id_app ee (op W)
    apply (cancel_mono (e.hom.hom.app (op W))).mp
    rw [Category.assoc, Category.assoc, heW, Category.comp_id]
    exact e.hom.hom.naturality j.op
  have hforget : IsIso ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      (Cmod.obj.map j.op)) := by rw [heq]; infer_instance
  exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

private theorem finiteLine_zero_restriction
    (A : Type (u + 1)) [CommRing A] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (m : ℕ) (hA : (m : A) = 0) (hm : (m : Ω) ≠ 0) :
    let X := Line (Spec (.of Ω))
    let F := Scheme.finiteEtaleTateSheaf A m X hA 1
    IsIso ((NatTrans.rightDerived
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (restriction (Spec (.of Ω))).op) 0).app F) := by
  let X := Line (Spec (.of Ω))
  let F := Scheme.finiteEtaleTateSheaf A m X hA 1
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let e : F ≅ C := finiteLineConstantIso A Ω (lineProjection (Spec (.of Ω))) m hA hm
  have hj := AffineSpace.range_basicOpen_ι_coord (Spec (.of Ω))
  have : ConnectedSpace X := by dsimp [X, Line]; infer_instance
  have : ConnectedSpace (Punctured (Spec (.of Ω))) :=
    Etale.connectedSpace_of_range_eq_compl_zeroSection
      (openImmersion (Spec (.of Ω))) hj
  have : ConnectedSpace (Scheme.Etale.mk (𝟙 X)).left := by
    change ConnectedSpace X
    infer_instance
  have : ConnectedSpace (openObject (Spec (.of Ω))).left := by
    change ConnectedSpace (Punctured (Spec (.of Ω)))
    infer_instance
  have hC : IsIso (C.obj.map (restriction (Spec (.of Ω))).op) :=
    constantRestriction_isIso A X (restriction (Spec (.of Ω)))
  have hF : IsIso (F.obj.map (restriction (Spec (.of Ω))).op) := by
    have heq : F.obj.map (restriction (Spec (.of Ω))).op =
        e.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
          C.obj.map (restriction (Spec (.of Ω))).op ≫
            e.inv.hom.app (op (openObject (Spec (.of Ω)))) := by
      let ee := (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso e
      have heW : e.inv.hom.app (op (openObject (Spec (.of Ω)))) ≫
          e.hom.hom.app (op (openObject (Spec (.of Ω)))) = 𝟙 _ :=
        Iso.inv_hom_id_app ee _
      apply (cancel_mono (e.hom.hom.app (op (openObject (Spec (.of Ω)))))).mp
      rw [Category.assoc, Category.assoc, heW, Category.comp_id]
      exact e.hom.hom.naturality (restriction (Spec (.of Ω))).op
    rw [heq]
    infer_instance
  let E := sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X))
  let G := sections X.smallEtaleTopology A (openObject (Spec (.of Ω)))
  let α : E ⟶ G := (sheafSections X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).map (restriction (Spec (.of Ω))).op
  have : IsIso (α.app F) := hF
  have heq := rightDerived_zero_transformation α F
  have hcomp : IsIso (E.toRightDerivedZero.app F ≫ (NatTrans.rightDerived α 0).app F) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.toRightDerivedZero.app F) _

private theorem finiteLine_vanishing
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (m : ℕ) (hmpos : 0 < m) (hA : (m : A) = 0) (hm : (m : Ω) ≠ 0) :
    let X := Line (Spec (.of Ω))
    let F := Scheme.finiteEtaleTateSheaf A m X hA 1
    (∀ q : ℕ, 0 < q → IsZero
      (((sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X))).rightDerived q).obj F)) ∧
    (∀ q : ℕ, 2 ≤ q → IsZero
      (((sections X.smallEtaleTopology A (openObject (Spec (.of Ω)))).rightDerived q).obj F)) := by
  let X := Line (Spec (.of Ω))
  let F := Scheme.finiteEtaleTateSheaf A m X hA 1
  let B := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A)
  have hB (b : B) : m • b = 0 := by
    rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
  let e : F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A) := finiteLineConstantIso A Ω
        (lineProjection (Spec (.of Ω))) m hA hm
  constructor
  · intro q hq
    have hs := AffineSpace.subsingleton_sheafH_constantSheaf_line B hm hB q hq
    let ψ := evaluationHiso A (𝟙 X) F q ≪≫
      (Sheaf.functorH _ q).mapIso (restrictedConstantIso A (𝟙 X) F e)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (@Equiv.subsingleton _ _ ψ.addCommGroupIsoToAddEquiv.toEquiv hs)
  · intro q hq
    have hj := AffineSpace.range_basicOpen_ι_coord (Spec (.of Ω))
    have hBid : m • 𝟙 B = 0 := by ext b; exact hB b
    have hs := AffineSpace.subsingleton_sheafH_constantSheaf_multiplicativeGroup
      (openImmersion (Spec (.of Ω))) hj B hmpos hBid q hq
    let ψ := evaluationHiso A (openImmersion (Spec (.of Ω))) F q ≪≫
      (Sheaf.functorH _ q).mapIso
        (restrictedConstantIso A (openImmersion (Spec (.of Ω))) F e)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (@Equiv.subsingleton _ _ ψ.addCommGroupIsoToAddEquiv.toEquiv hs)

/-- The ordinary Kummer computation for arbitrary finite coefficient rings, with
its natural coordinate generator. Source: blueprint rank-one calculation, steps 1--3
and 5; Milne, Proposition 14.3 and Example 16.3.

Proof: a primitive m-th root in the algebraically closed field identifies the
finite twist with the constant A sheaf through the scalar-extension adjunction.
The adopted AffineLineKummer theorems compute higher cohomology for all finite
abelian coefficients killed by m, by finite abelian group decomposition. The
module/abelian, represented Ext and open-object cohomology isomorphisms transport
these vanishings to the displayed derived evaluations. On a connected etale object,
constant sections equal the coefficient group: the mono into point functions
identifies a section with a locally constant function, hence a constant function.
Both curves are connected, so restriction of their constant sections is invertible.
Naturality and the right-derived degree-zero isomorphisms give the last assertion.
The separate finite_kummer_generator theorem supplies the normalized degree-one
basis. These arguments include the zero coefficient ring.
(blueprint: lem-pur-rank-one-finite-kummer-cohomology). -/
theorem finite_kummer_cohomology
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓΩ : IsUnit (ℓ : Ω)) (hN : 1 ≤ N)
    (hA : ((ℓ ^ N : ℕ) : A) = 0)
    (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(Line (Spec (.of Ω)), ⊤)))
    (f : (Line (Spec (.of Ω))).rootsOfUnitySheaf (ℓ ^ N) ⟶
      (Etale.moduleAbelianForget A (Line (Spec (.of Ω)))).obj
        (Scheme.finiteEtaleTateSheaf A (ℓ ^ N) (Line (Spec (.of Ω))) hA 1))
    (hf : ∀ V z, f.hom.app V z =
      Scheme.finiteEtaleTateOneGenerator A (ℓ ^ N) (Line (Spec (.of Ω))) hA V 1 z) :
    let X := Line (Spec (.of Ω))
    let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
    let κ := kummerClass A X (openObject (Spec (.of Ω))) F (ℓ ^ N) hm f
    (∃ τ : ModuleCat.of A A ≅
        ((sections X.smallEtaleTopology A (openObject (Spec (.of Ω)))).rightDerived 1).obj F,
      τ.hom 1 = κ (coordinateUnit (Spec (.of Ω)))) ∧
    (∀ q : ℕ, 0 < q → IsZero
      (((sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X))).rightDerived q).obj F)) ∧
    (∀ q : ℕ, 2 ≤ q → IsZero
      (((sections X.smallEtaleTopology A (openObject (Spec (.of Ω)))).rightDerived q).obj F)) ∧
    IsIso ((NatTrans.rightDerived
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (restriction (Spec (.of Ω))).op) 0).app F) := by
  have hmΩ : ((ℓ ^ N : ℕ) : Ω) ≠ 0 := by
    simpa only [Nat.cast_pow] using (hℓΩ.pow N).ne_zero
  obtain ⟨hX, hU⟩ := finiteLine_vanishing A Ω (ℓ ^ N)
    (pow_pos hℓ.pos N) hA hmΩ
  refine ⟨?_, hX, hU, ?_⟩
  · exact finite_kummer_generator A Ω ℓ N hℓ hℓΩ hN hA hm f hf
  · exact finiteLine_zero_restriction A Ω (ℓ ^ N) hA hmΩ

end WeilConjectures.PurityFiniteSetting.RankOne

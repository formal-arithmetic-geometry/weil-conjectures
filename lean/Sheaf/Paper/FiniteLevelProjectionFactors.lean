module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekLocalizing
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-level proper and open projection factors

Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3);
Stacks Tags 0F0G, 09A6, 09AL, 0GL1 and 0B56; Bhatt--Scholze, Section 5.3
(blueprint: lem-sp-finite-level-projection-factors).

The two arrows are the existing counit and unit transposes, respectively. Their
bifunctor-valued natural transformations give naturality in both arguments.
The fixed-scalar section-action functor and its normalized operation comparisons below
state the coefficient-transport clause for the same scalar universe and the same arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

namespace FiniteLevelComparison

variable (A : Type (u + 1)) [CommRing A]

/-- The discrete constant condensed coefficient, without a scalar universe lift.
Source: blueprint integral direct-image proof (3), coefficient identification
(blueprint: lem-sp-finite-level-projection-factors). -/
abbrev coefficient : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj (AddCommGrpCat.of A)

/-- Constant sheafification transports commutativity of the ring-object structure.
Source: blueprint coefficient identification, Stacks 03CY
(blueprint: lem-sp-finite-level-projection-factors).
Proof: the constant presheaf functor respects the pointwise braiding, as does monoidal
sheafification. Applying these functors to commutative multiplication preserves its
commutativity equation. -/
@[instance] theorem coefficient_comm : IsCommMonObj (coefficient A) := by
  let : (Functor.const Profiniteᵒᵖ : Ab.{u + 1} ⥤ Profiniteᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
    { braided X Y := by
        apply NatTrans.ext
        funext V
        exact (Category.id_comp ((β_ X Y).hom)).trans
          (Category.comp_id ((β_ X Y).hom)).symm }
  let : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided :=
    inferInstanceAs (Functor.const Profiniteᵒᵖ ⋙
      presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided
  exact Functor.isCommMonObj_obj
    (F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Internal modules over the pullback of the discrete constant coefficient.
Source: blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors). -/
abbrev Internal (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (coefficient A) T)

/-- The section ring of the actual internal coefficient, with its reconstructed multiplication.
Source: Stacks 00YV (blueprint: lem-sp-finite-level-projection-factors). -/
abbrev sectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)

private theorem monHomMapExplicit {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (f : M ⟶ N)
    (hf : @IsMonHom _ _ _ M N mM mN f) :
    let := mM
    let := mN
    IsMonHom (F.map f) := by
  let := mM
  let := mN
  let := hf
  infer_instance

private theorem monHomInvExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (e : M ≅ N)
    (h : @IsMonHom _ _ _ M N mM mN e.hom) :
    @IsMonHom _ _ _ N M mN mM e.inv := by
  let := mM
  let := mN
  let := h
  infer_instance

private theorem monHomCompExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N O : C} (mM : MonObj M) (mN : MonObj N) (mO : MonObj O)
    (f : M ⟶ N) (g : N ⟶ O)
    (hf : @IsMonHom _ _ _ M N mM mN f)
    (hg : @IsMonHom _ _ _ N O mN mO g) :
    @IsMonHom _ _ _ M O mM mO (f ≫ g) := by
  let := mM
  let := mN
  let := mO
  let := hf
  let := hg
  infer_instance

private def constantSectionMap
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, z}] [HasSheafify J Ab.{z}]
    [(J.W (A := Ab.{z})).IsMonoidal]
    (B : Type (z)) [CommRing B]
    (R : Sheaf J Ab.{z}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    [@IsMonHom _ _ _ _ _
      ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{z}).monObjObj R) φ] :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf J R).obj where
  app U := by
    letI := CommRingCat.commRing
      ((InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
    refine CommRingCat.ofHom
      (R := B) (S := (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U) ?_
    refine
      { toFun := fun a ↦ φ.app U a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{z}).monObjObj R) φ inferInstance
      convert! ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1) using 1
      simp only [Functor.const_obj_obj, Monoidal.tensorUnit_obj, ObjectProperty.ι_obj,
        Functor.obj.η_def, Category.assoc, NatTrans.comp_app, Functor.const_map_app,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change (φ.app U) (1 : B) =
        (φ.app U) ((CategoryTheory.MonObj.one (X := AddCommGrpCat.of B)).hom (ULift.up 1))
      rw [AddCommGrpCat.ringMonObj_one_apply]
      simp
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{z}).monObjObj R) φ inferInstance
      exact ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
  naturality U V f := by
    ext a
    exact ConcreteCategory.congr_hom (φ.naturality f) a

private theorem normalizedRingMap_existsUnique
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, z}] [HasSheafify J Ab.{z}]
    [(J.W (A := Ab.{z})).IsMonoidal] [HasWeakSheafify J CommRingCat.{z}]
    (B : Type (z)) [CommRing B]
    (R : Sheaf J Ab.{z}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    (hφ : @IsMonHom _ _ _ _ _
      ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{z}).monObjObj R) φ) :
    ∃! c : (constantSheaf J CommRingCat.{z}).obj (CommRingCat.of B) ⟶
        InternalAbelianSheafModule.sectionRingSheaf J R,
      ∀ (V : Cᵒᵖ) (a : B),
        c.hom.app V ((toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app V a) = φ.app V a := by
  let := hφ
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of B)
  let S := InternalAbelianSheafModule.sectionRingSheaf J R
  let c₀ := constantSectionMap J B R φ
  let adj := sheafificationAdjunction J CommRingCat.{z}
  let c := (adj.homEquiv _ (InternalAbelianSheafModule.sectionRingSheaf J R)).symm c₀
  have hc (V : Cᵒᵖ) (a : B) :
      c.hom.app V ((toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app V a) = φ.app V a := by
    exact ConcreteCategory.congr_hom (congr_app
      ((adj.homEquiv P S).apply_symm_apply c₀) V) a
  refine ExistsUnique.intro c hc ?_
  intro d hd
  apply (adj.homEquiv P S).injective
  apply NatTrans.ext
  funext V
  apply CommRingCat.hom_ext
  ext a
  exact (hd V a).trans (hc V a).symm

/-- The canonical ring comparison is uniquely specified on constant sections.
Source: Stacks 00YV, 03CY and blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors).
Proof: the monoidal constant-pullback isomorphism identifies the underlying abelian sheaves.
Its compatibility with multiplication makes its section maps ring homomorphisms.
Sheafification extends the constant-section maps uniquely. The inverse monoidal comparison
proves invertibility. -/
theorem scalarMap_existsUnique (T : Scheme.{u}) :
    ∃! c : (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of A) ⟶ sectionRing A T,
      ∀ (V : T.ProEtᵒᵖ) (a : A),
        c.hom.app V ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app V a) =
        ((constantSchemeIso T).hom.app (AddCommGrpCat.of A)).hom.app V
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V a) := by
  let J := Scheme.ProEt.topology T
  let P : T.ProEtᵒᵖ ⥤ Ab.{u + 1} := (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of.{u + 1} A)
  let F := constantSheaf J Ab.{u + 1}
  let G := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let H := upperStarFromPoint T
  let R : Sheaf J Ab.{u + 1} := condensedRingObj (coefficient A) T
  let f := (constantSchemeIso T).hom.app (AddCommGrpCat.of.{u + 1} A)
  have hi := Functor.isMonHom_compAlgHom G H (constantSchemeIso T).inv
    (AddCommGrpCat.of.{u + 1} A)
  let mQ := H.monObjObj (G.obj (AddCommGrpCat.of.{u + 1} A))
  let mF := F.monObjObj (AddCommGrpCat.of.{u + 1} A)
  have hf := monHomInvExplicit mQ mF
    ((constantSchemeIso T).app (AddCommGrpCat.of.{u + 1} A)).symm hi
  let mP := (Functor.const T.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of.{u + 1} A)
  let mS := (presheafToSheaf J Ab.{u + 1}).monObjObj P
  have hm : F.monObjObj (AddCommGrpCat.of.{u + 1} A) = mS :=
    Functor.monObjObj_comp _ _ _
  have hf' := IsMonHom.of_eq f hm rfl (hf := hf)
  let φ := toSheafify J P ≫ f.hom
  have hφ : @IsMonHom _ _ _ _ _ mP
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ := by
    have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have hv := monHomMapExplicit (sheafToPresheaf J Ab.{u + 1}) mS _ f hf'
    exact monHomCompExplicit mP _ _ _ _ hu hv
  have h := normalizedRingMap_existsUnique.{u + 1, u, u + 1} J A R φ hφ
  exact h

/-- The unique normalized section-ring map; no arbitrary coefficient isomorphism is chosen.
Source: Stacks 00YV and 03CY (blueprint: lem-sp-finite-level-projection-factors). -/
def scalarMap (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of A) ⟶ sectionRing A T :=
  (scalarMap_existsUnique A T).choose

/-- Section action followed by restriction to the original scalar sections.
Source: Stacks 00YV, 03CY (blueprint: lem-sp-finite-level-projection-factors). -/
def encoding (T : Scheme.{u}) :
    Internal A T ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)).functor ⋙
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarMap A T)) ⋙
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of A)) ⋙
  constantRingModuleRestriction (Scheme.ProEt.topology T) A

private theorem scalarMap_isIso (T : Scheme.{u}) : IsIso (scalarMap A T) := by
  let J := Scheme.ProEt.topology T
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let F := sheafCompose J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of A)
  let g := F.map (scalarMap A T)
  have hg : e.inv ≫ g = (constantSchemeIso T).hom.app (AddCommGrpCat.of A) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (condensedRingObj (coefficient A) T).property
    have he : toSheafify J
        ((Functor.const T.ProEtᵒᵖ).obj (V.obj (CommRingCat.of A))) ≫ e.inv.hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of A) V).inv ≫
        (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact (scalarMap_existsUnique A T).choose_spec.1 U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (scalarMap A T) F

private def restrictCancelIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{z}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{z} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem restrictionIsEquivalence
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{z}} (e : S ≅ R) :
    (SheafOfModules.restrictScalars.{z} e.hom).IsEquivalence := by
  exact (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (restrictCancelIso e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso e.hom e.inv e.hom_inv_id)).isEquivalence_functor

/-- The specified section-action functor is an additive equivalence.
Source: Stacks 00YV, 03CY (blueprint: lem-sp-finite-level-projection-factors).
Proof: scalarMap is invertible by the monoidal constant-pullback comparison. Compose the
section-action equivalence, restriction along the two ring isomorphisms, and the constant
ring module equivalence. Each functor retains the underlying additive maps. -/
theorem encoding_properties (T : Scheme.{u}) :
    (encoding A T).IsEquivalence ∧ (encoding A T).Additive := by
  let := scalarMap_isIso A T
  let J := Scheme.ProEt.topology T
  have h₁ : (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (scalarMap A T))).IsEquivalence :=
    restrictionIsEquivalence
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (asIso (scalarMap A T)))
  have h₂ : (SheafOfModules.restrictScalars.{u + 1}
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A))).IsEquivalence :=
    restrictionIsEquivalence
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
        (CommRingCat.of A))
  obtain ⟨e, he, ha, _⟩ := (constant_ring_module_sheaves J A).1
  have h₃ : (constantRingModuleRestriction J A).IsEquivalence :=
    he ▸ e.isEquivalence_functor
  have h₀ := (InternalAbelianSheafModule.sectionModuleEquivalence J
    (condensedRingObj (coefficient A) T)).isEquivalence_functor
  constructor
  · unfold encoding
    infer_instance
  · refine ⟨?_⟩
    intro M N f g
    ext V x
    rfl

/-- The actual termwise derived section-action equivalence.
Source: blueprint integral direct-image proof (3), Stacks 015F
(blueprint: lem-sp-finite-level-projection-factors). -/
def derivedEncoding (T : Scheme.{u}) :
    DerivedCategory (Internal A T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  letI := (encoding_properties A T).1
  letI := (encoding_properties A T).2
  letI : (encoding A T).asEquivalence.functor.Additive :=
    inferInstanceAs (encoding A T).Additive
  letI : (encoding A T).asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  (encoding A T).asEquivalence.mapDerivedCategory

/-- The tensor comparison is uniquely normalized on pure tensors of sections.
Source: Stacks 03EK, 07A4 (blueprint: lem-sp-finite-level-projection-factors).
The internal pure tensor is the coequalizer projection of the lax sheaf-to-presheaf
tensor comparison applied to `x ⊗ y`.
Proof: section action identifies balanced bilinear maps. The resulting tensor comparison
and regular-unit map satisfy the monoidal axioms on pure tensors. Pure tensors locally
generate, which determines the tensor map; the unitor axioms determine the unit map.
The inverse section-action equivalence supplies the inverse comparisons. -/
theorem monoidal_existsUnique (T : Scheme.{u}) :
    ∃! m : (encoding A T).Monoidal,
      letI := m
      ∀ (M N : Internal A T) (V : T.ProEtᵒᵖ)
        (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((Functor.OplaxMonoidal.δ (encoding A T) M N).hom.app V)
          (((Mod.tensorObjπ M N).hom.app V)
            (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              M.X N.X).app V) (x ⊗ₜ[ℤ] y))) =
        (Functor.LaxMonoidal.μ
          (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
          ((encoding A T).obj M) ((encoding A T).obj N)).app V
            (x ⊗ₜ[A] y) := by
  sorry

/-- The sectionwise normalized strong monoidal structure.
Source: Stacks 03EK (blueprint: lem-sp-finite-level-projection-factors). -/
@[instance_reducible] def monoidal (T : Scheme.{u}) : (encoding A T).Monoidal :=
  (monoidal_existsUnique A T).choose

/-- The normalized equivalence preserves flat objects, so its derived tensorator is canonical.
Source: Stacks 07A4 (blueprint: lem-sp-finite-level-projection-factors).
Proof: the inverse equivalence supplies every tensor test; exactness and the pure-tensor
comparison identify the two tests and hence flatness. -/
theorem encoding_preservesFlat (T : Scheme.{u}) : (encoding A T).PreservesFlat := by
  have := (encoding_properties A T).1
  let := monoidal A T
  exact (encoding A T).preservesFlat_of_isEquivalence

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

section tensorIsoPerformance

attribute [local irreducible] encoding CondensedRing.upperStar upperStarFromPoint

/-- The K-flat derived tensor comparison, using the specified sectionwise tensorator.
Source: Stacks 07A4 (blueprint: lem-sp-finite-level-projection-factors). -/
def tensorIso (T : Scheme.{u}) (K L : DerivedCategory (Internal A T)) :
    (derivedEncoding A T).functor.obj (K ⊗ L) ≅
      (derivedEncoding A T).functor.obj K ⊗ (derivedEncoding A T).functor.obj L := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A T).2
  letI := monoidal A T
  letI := encoding_preservesFlat A T
  letI := (encoding A T).leftDerivedFunctorMonoidal
  letI := Functor.Monoidal.transport (encoding A T).leftDerivedFunctorIsoMapDerivedCategory
  change (encoding A T).mapDerivedCategory.obj (K ⊗ L) ≅
    (encoding A T).mapDerivedCategory.obj K ⊗ (encoding A T).mapDerivedCategory.obj L
  exact asIso (Functor.OplaxMonoidal.δ (encoding A T).mapDerivedCategory K L)

end tensorIsoPerformance

/-- The underived direct-image comparison is uniquely the identity on sections.
Source: Stacks 03D7 (blueprint: lem-sp-finite-level-projection-factors).
Proof: both functors evaluate on the same pullback site object. Constant sections commute
with pullback; normalization of scalarMap therefore identifies scalar actions. The identity
on these sections is a linear natural map and its inverse is the same identity. -/
theorem pushMap_existsUnique {S T : Scheme.{u}} (f : S ⟶ T) :
    ∃! q : CondensedRing.lowerStar (coefficient A) f ⋙ encoding A T ⟶
      encoding A S ⋙ lowerStar (ModuleCat.{u + 1} A) f,
      ∀ (M : Internal A S) (V : T.ProEtᵒᵖ)
        (x : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)),
        ((q.app M).hom.app V) x = x := by
  sorry

/-- The identity-on-sections direct-image comparison.
Source: Stacks 03D7 (blueprint: lem-sp-finite-level-projection-factors). -/
def pushMap {S T : Scheme.{u}} (f : S ⟶ T) :
    CondensedRing.lowerStar (coefficient A) f ⋙ encoding A T ⟶
      encoding A S ⋙ lowerStar (ModuleCat.{u + 1} A) f :=
  (pushMap_existsUnique A f).choose

/-- The identity-on-sections comparison is invertible.
Source: Stacks 03D7 (blueprint: lem-sp-finite-level-projection-factors).
Proof: its inverse is the identity on the same section groups and scalar actions. -/
theorem pushMap_isIso {S T : Scheme.{u}} (f : S ⟶ T) : IsIso (pushMap A f) := by
  have hsections (M : Internal A S) (V : T.ProEtᵒᵖ) :
      Function.Bijective (((pushMap A f).app M).hom.app V) := by
    have hx := (pushMap_existsUnique A f).choose_spec.1 M V
    exact ⟨fun x y h ↦ (hx x).symm.trans (h.trans (hx y)),
      fun x ↦ ⟨x, hx x⟩⟩
  have hcomponents (M : Internal A S) : IsIso ((pushMap A f).app M) := by
    let (V : T.ProEtᵒᵖ) : IsIso (((pushMap A f).app M).hom.app V) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hsections M V)
    have hpres : IsIso ((pushMap A f).app M).hom := NatIso.isIso_of_isIso_app _
    apply (isIso_iff_of_reflects_iso ((pushMap A f).app M)
      (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).mp
    exact hpres
  let := hcomponents
  exact NatIso.isIso_of_isIso_app _

attribute [local irreducible] encoding CondensedRing.upperStar upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

/-- Inverse-image comparison obtained by uniqueness of left adjoints, fixing both adjunctions.
Source: Stacks 03D7 (blueprint: lem-sp-finite-level-projection-factors). -/
def pullIso {S T : Scheme.{u}} (f : S ⟶ T) :
    CondensedRing.upperStar (coefficient A) f ⋙ encoding A S ≅
      encoding A T ⋙ upperStar (ModuleCat.{u + 1} A) f := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A S).1
  letI := pushMap_isIso A f
  let ET := (encoding A T).asEquivalence
  let ES := (encoding A S).asEquivalence
  let k := Iso.isoCompInverse (H := ET) (asIso (pushMap A f)) ≪≫
    Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ES) k
  let a := ET.toAdjunction.comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp ES.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- Extension comparison obtained from the specified open adjunction and pullback comparison.
Source: Stacks 03DJ (blueprint: lem-sp-finite-level-projection-factors). -/
def openIso {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙ encoding A T ≅
      encoding A S ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} A) j := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A S).1
  let ET := (encoding A T).asEquivalence
  let ES := (encoding A S).asEquivalence
  let k := Iso.isoCompInverse (H := ES) (pullIso A j) ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := ES.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Total right-derived identity-on-sections comparison.
Source: Stacks 015F (blueprint: lem-sp-finite-level-projection-factors). -/
def derivedPushIso {S T : Scheme.{u}} (f : S ⟶ T) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
      (derivedEncoding A T).functor ≅
    (derivedEncoding A S).functor ⋙
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A S).1
  letI := (encoding_properties A T).2
  letI := (encoding_properties A S).2
  letI := pushMap_isIso A f
  change (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
    (encoding A T).mapDerivedCategory ≅ (encoding A S).mapDerivedCategory ⋙
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (pushMap A f)) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _

/-- Total left-derived inverse-image comparison, localized from the specified mate.
Source: Stacks 015F, 07A6 (blueprint: lem-sp-finite-level-projection-factors). -/
def derivedPullIso {S T : Scheme.{u}} (f : S ⟶ T) :
    (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor ⋙
      (derivedEncoding A S).functor ≅
    (derivedEncoding A T).functor ⋙
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A S).1
  letI := (encoding_properties A T).2
  letI := (encoding_properties A S).2
  change (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor ⋙
    (encoding A S).mapDerivedCategory ≅ (encoding A T).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  exact Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (coefficient A) f) _ ≪≫
    Functor.mapDerivedCategorySquareIso (pullIso A f) ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm

/-- Derived extension comparison, localized from the specified open-adjunction mate.
Source: Stacks 015F, 03DJ (blueprint: lem-sp-finite-level-projection-factors). -/
def derivedOpenIso {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
      (derivedEncoding A T).functor ≅
    (derivedEncoding A S).functor ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory := by
  letI := (encoding_properties A T).1
  letI := (encoding_properties A S).1
  letI := (encoding_properties A T).2
  letI := (encoding_properties A S).2
  change (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
    (encoding A T).mapDerivedCategory ≅ (encoding A S).mapDerivedCategory ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openIso A j) ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- Exact restriction comparison, with the canonical total-left-derived normalization.
Source: Stacks 03DJ, 015F (blueprint: lem-sp-finite-level-projection-factors). -/
def derivedRestrictionIso {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    (CondensedRing.upperStar (coefficient A) j).mapDerivedCategory ⋙
      (derivedEncoding A S).functor ≅
    (derivedEncoding A T).functor ⋙ (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (coefficient A) j).symm _ ≪≫
    derivedPullIso A j ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j)

/-- The actual compactification comparison, composed from the normalized operation maps.
Source: blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors). -/
def compactificationIso {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
      (CondensedRing.lowerStar (coefficient A) p).rightDerivedFunctor ⋙
      (derivedEncoding A Y).functor ≅
    (derivedEncoding A X).functor ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _ (derivedPushIso A p) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedOpenIso A j) _ ≪≫ Functor.associator _ _ _

-- Proper adjunction comparison split into unit and counit statements.
/-- Unit half of the fixed-scalar proper adjunction comparison. -/
theorem proper_adjunction_comparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : DerivedCategory (Internal A Y),
      (derivedEncoding A Y).functor.map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f).unit.app K) ≫
        (derivedPushIso A f).hom.app
          ((CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
          ((derivedPullIso A f).hom.app K) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
        ((derivedEncoding A Y).functor.obj K)) := by
  sorry

/-- Counit half of the fixed-scalar proper adjunction comparison. -/
theorem proper_adjunction_comparison_counit {X Y : Scheme.{u}} (f : X ⟶ Y) :
(∀ K : DerivedCategory (Internal A X),
      (derivedEncoding A X).functor.map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f).counit.app K) =
        (derivedPullIso A f).hom.app
          ((CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          ((derivedPushIso A f).hom.app K) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
          ((derivedEncoding A X).functor.obj K))  := by
  sorry

theorem proper_adjunction_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : DerivedCategory (Internal A Y),
      (derivedEncoding A Y).functor.map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f).unit.app K) ≫
        (derivedPushIso A f).hom.app
          ((CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
          ((derivedPullIso A f).hom.app K) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
        ((derivedEncoding A Y).functor.obj K)) ∧
    (∀ K : DerivedCategory (Internal A X),
      (derivedEncoding A X).functor.map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f).counit.app K) =
        (derivedPullIso A f).hom.app
          ((CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          ((derivedPushIso A f).hom.app K) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
          ((derivedEncoding A X).functor.obj K)) := by
  exact ⟨proper_adjunction_comparison_unit A f, proper_adjunction_comparison_counit A f⟩

/-- The fixed-scalar comparison identifies the unit and counit of exact open extension.
Source: Stacks 03DJ, 015F; blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors).
Proof: openIso is defined by uniqueness of left adjoints with the specified pullIso.
The two mate equations identify the underived unit and counit. Termwise localization
preserves them; the total left-derived restriction comparison is its exact normalization. -/
theorem open_adjunction_comparison {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ K : DerivedCategory (Internal A X),
      (derivedEncoding A X).functor.map
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (coefficient A) j).unit.app K) ≫
        (derivedRestrictionIso A j).hom.app
          ((CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedOpenIso A j).hom.app K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((derivedEncoding A X).functor.obj K)) ∧
    (∀ K : DerivedCategory (Internal A Z),
      (derivedEncoding A Z).functor.map
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (coefficient A) j).counit.app K) =
        (derivedOpenIso A j).hom.app
          ((CondensedRing.upperStar (coefficient A) j).mapDerivedCategory.obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedRestrictionIso A j).hom.app K) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
          ((derivedEncoding A Z).functor.obj K)) := by
  sorry

/-- The internal proper counit projection is the item's fixed-scalar proper projection map.
Source: Stacks 0B56, blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors).
Proof: on K-flat representatives the normalized pure-tensor comparison commutes with
inverse image. The counit equation in proper_adjunction_comparison therefore identifies
both transposes. Apply the adjunction Hom bijection, then the direct-image and tensor
comparisons. Naturality descends the equation to arbitrary unbounded derived inputs. -/
theorem proper_projection_comparison [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Internal A X)) (L : DerivedCategory (Internal A Y)) :
    (derivedEncoding A Y).functor.map
      (((Adjunction.rightAdjointProjectionMap
        (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) f)
        (CondensedRing.leftDerivedUpperStarTensor (coefficient A) f)).app K).app L) ≫
      (derivedPushIso A f).hom.app
        (K ⊗ (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
        ((tensorIso A X K
          ((CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor.obj L)).hom) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
        (𝟙 _ ⊗ₘ (derivedPullIso A f).hom.app L) =
    (tensorIso A Y ((CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor.obj K) L).hom ≫
      ((derivedPushIso A f).hom.app K ⊗ₘ 𝟙 _) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app
        ((derivedEncoding A X).functor.obj K)).app ((derivedEncoding A Y).functor.obj L) := by
  sorry

/-- The internal open unit projection is the item's fixed-scalar open projection map.
Source: Stacks 0GL1, 0B56, blueprint integral direct-image proof (3)
(blueprint: lem-sp-finite-level-projection-factors).
Proof: on K-flat representatives the pure-tensor normalization identifies the pullback
comparison and its inverse. The open unit equation identifies the unit tensors. Taking
the transpose under the identified open adjunctions proves the displayed equality. -/
theorem open_projection_comparison [Finite A] {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (Internal A X)) (L : DerivedCategory (Internal A Z)) :
    (derivedEncoding A Z).functor.map
      (((CondensedRing.openImmersionProjectionComparison' (coefficient A) j).app K).app L) ≫
      (tensorIso A Z
        ((CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory.obj K)
        L).hom ≫ ((derivedOpenIso A j).hom.app K ⊗ₘ 𝟙 _) =
    (derivedOpenIso A j).hom.app
      (K ⊗ (CondensedRing.upperStar (coefficient A) j).leftDerivedFunctor.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((tensorIso A X K
          ((CondensedRing.upperStar (coefficient A) j).leftDerivedFunctor.obj L)).hom) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        (𝟙 _ ⊗ₘ (derivedPullIso A j).hom.app L) ≫
      ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j).app
        ((derivedEncoding A X).functor.obj K)).app ((derivedEncoding A Z).functor.obj L) := by
  sorry

/-- The coefficient identification preserves all Tor intervals and finite constant local
models, and identifies the bounded constructible finite-Tor subcategories.
Source: blueprint integral direct-image proof (3), Stacks 03CY, 08BJ, 08FZ
(blueprint: lem-sp-finite-level-projection-factors).
Proof: exactness and the normalized tensor comparison identify every degree-zero tensor
test and hence each Tor interval. Section action and scalarMap identify constant finite
presentations on each member of a pro-etale cover with constant finite A-modules. Over a
finite ring, finite and finitely presented modules coincide. Transport the same covers
and finite stratifications; finite constant local models are exactly locally constant
finite-stalk sheaves. Exactness identifies the homology sheaves and boundedness. -/
theorem coefficient_models [Finite A] (T : Scheme.{u}) [IsNoetherian T] :
    (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔
        Scheme.HasFixedCoefficientProEtaleTorAmplitude T A
          ((derivedEncoding A T).functor.obj K) a b)) ∧
    (∀ M : Internal A T,
      HasFiniteConstantLocalModel (coefficient A) T M ↔
        ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : C.I₀,
          ∃ P : ModuleCat.{u + 1} A, Finite P ∧
            Nonempty ((upperStar (ModuleCat.{u + 1} A) (C.f i)).obj ((encoding A T).obj M) ≅
              (constantSheaf (Scheme.ProEt.topology (C.X i)) (ModuleCat.{u + 1} A)).obj P)) ∧
    (∀ K : DerivedCategory (Internal A T),
      (constantModelBoundedConstructible (coefficient A) T K ∧
        DerivedCategory.finiteTorAmplitude _ K) ↔
      ((DerivedCategory.TStructure.t.bounded ((derivedEncoding A T).functor.obj K) ∧
        ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
          ((DerivedCategory.homologyFunctor _ i).obj ((derivedEncoding A T).functor.obj K))) ∧
        ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude T A
          ((derivedEncoding A T).functor.obj K) a b)) := by
  sorry

end FiniteLevelComparison

private theorem etale_constructible_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hv⟩
    refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr ?_⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr ?_⟩⟩, ?_⟩
    · exact fun i hi ↦ hv i (Or.inl hi)
    · exact fun i hi ↦ hv i (Or.inr hi)
    · exact fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb i hi

private theorem intrinsic_constructible_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (_root_.DerivedCategory.TStructure.t.bounded K ∧
      ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  have he := congrFun (exceptionalTransport_constructible_comparison A T) K
  constructor
  · intro h
    obtain ⟨L, hL, ⟨e⟩⟩ := he.mp h
    exact ⟨L, (etale_constructible_iff A T L).mp hL, ⟨e⟩⟩
  · rintro ⟨L, hL, ⟨e⟩⟩
    exact he.mpr ⟨L, (etale_constructible_iff A T L).mpr hL, ⟨e⟩⟩

/-- The proper counit projection and open unit projection are invertible, and extension
by zero preserves bounded intrinsic constructibility and finite Tor amplitude.
The inverse open arrow is the canonical forward open projection comparison.

Source: blueprint integral direct-image proof, paragraph (3); Stacks 0F0G, 09A6,
09AL, 0GL1, 07A4 and 0B56
(blueprint: lem-sp-finite-level-projection-factors).

Proof plan (the seven steps of the node):
1. Use FiniteLevelComparison.derivedEncoding for the exact scalar universe.
Its coefficient_models and tensorIso comparisons identify unbounded derived tensors and all
Tor intervals, and identify finite constant models. finiteCoefficientModelComparison
identifies their stratified constructibility with intrinsic finite-stalk constructibility.
Finite and finitely presented modules over a finite ring coincide: a finite presentation
has finite source, while a finite module and its finite relation module have finite generators.
Finite-type schemes over the field are Noetherian and qcqs.
2. Apply FiniteLevelComparison.proper_adjunction_comparison, open_adjunction_comparison,
proper_projection_comparison and open_projection_comparison. The normalized tensorators identify the
counit transpose defining the proper arrow and the unit transpose defining the open
arrow, including their units and counits. Composing operation comparisons identifies
Rp_*D(j_!) for this very factorization via FiniteLevelComparison.compactificationIso.
3. openExtension_constructible_finiteTor preserves the bounded constant-model condition
and each Tor interval. Transport back using the exact finite coefficient equivalence and
finiteCoefficientModelComparison to obtain the intrinsic conclusion for j_!C.
4. openTensorNormalization identifies the canonical forward open comparison and says
its inverse is precisely the displayed unit transpose, so the open factor is invertible
and has the stated inverse. This step also holds for arbitrary unbounded inputs.
5. finiteRing_constructibleDerived_origin supplies bounded constructible etale origins
E0 and B0 for j_!C and B. finiteTorComparisonNoetherian reflects the Tor interval of E0.
Exact etale inverse image and homologyConcentratedIn_tensor_of_torAmplitudeIn_left show
E0 tensor p_0^*B0 is bounded, hence bounded below, without any Tor condition over Z/l^n.
6. Apply the proper torsion etale projection formula, Tag 0F0G. The ring is torsion by
its l-power annihilation. projection_comparison_etale_proetale identifies its specified
counit projection with the pro-etale counit projection through the normalized direct-image
comparison mate. The mate is invertible on the bounded-below objects checked in step 5;
all remaining factors are tensor/pullback comparisons, hence isomorphisms.
7. Tensor and the specified adjunction bijections are natural, so both projection maps
are natural in C and B, as already expressed by their bifunctor transformation types.
Their inverses are natural. The normalized operation comparisons from step 2 identify
these very arrows and their compactification composite. No closure or finiteness of k
has entered any step. -/
theorem finite_level_projection_factors
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : A) = 0)
    {X Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Z) [IsOpenImmersion j.left] (p₀ : Z ⟶ Y) [IsProper p₀.left]
    (C : DerivedCategory (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)))
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} A)))
    (_hCc : DerivedCategory.TStructure.t.bounded C ∧ ∀ i : ℤ,
      Scheme.IsConstructibleProEtaleFixedModuleSheaf X.left A
        ((DerivedCategory.homologyFunctor _ i).obj C))
    (_hCt : ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude X.left A C a b)
    (_hBc : DerivedCategory.TStructure.t.bounded B ∧ ∀ i : ℤ,
      Scheme.IsConstructibleProEtaleFixedModuleSheaf Y.left A
        ((DerivedCategory.homologyFunctor _ i).obj B))
    (_hBt : ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Y.left A B a b) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p₀.left).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.left).mapDerivedCategory.obj C)).app B) ∧
    IsIso (((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j.left).app C).app
      ((upperStar (ModuleCat.{u + 1} A) p₀.left).leftDerivedFunctor.obj B)) ∧
    inv (((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j.left).app C).app
      ((upperStar (ModuleCat.{u + 1} A) p₀.left).leftDerivedFunctor.obj B)) =
      (derivedTensorOpenImmersionLowerShriekIso (ModuleCat.{u + 1} A) j.left C
        ((upperStar (ModuleCat.{u + 1} A) p₀.left).leftDerivedFunctor.obj B)).hom ∧
    (DerivedCategory.TStructure.t.bounded
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.left).mapDerivedCategory.obj C) ∧
      ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf Z.left A
        ((DerivedCategory.homologyFunctor _ i).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.left).mapDerivedCategory.obj C))) ∧
    (∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Z.left A
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.left).mapDerivedCategory.obj C) a b) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have hC := (intrinsic_constructible_iff A X.left C).mp _hCc
  have hB := (intrinsic_constructible_iff A Y.left B).mp _hBc
  obtain ⟨a, b, hab, hCt⟩ := _hCt
  have hctf : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X.left C :=
    ⟨hC, a, b, hCt⟩
  have hext := constructibleFiniteTor_mapDerivedCategory_openImmersionLowerShriek A j.left hctf
  obtain ⟨B₀, hB₀, ⟨eB⟩⟩ := hB
  have hproper := isIso_rightDerivedLowerStarProjectionMap_app_app_of_bounded A p₀.left
    j.left hctf hB₀.1
  have hproper' : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      p₀.left).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j.left).mapDerivedCategory.obj C)).app
          B) := (NatTrans.isIso_app_iff_of_iso _ eB).mp hproper
  refine ⟨hproper', inferInstance, ?_,
    (intrinsic_constructible_iff A Z.left _).mpr hext.1,
    a, b, hab, torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek j.left hCt⟩
  apply IsIso.inv_eq_of_hom_inv_id
  exact (derivedTensorOpenImmersionLowerShriekIso (ModuleCat.{u + 1} A) j.left C
    ((upperStar (ModuleCat.{u + 1} A) p₀.left).leftDerivedFunctor.obj B)).inv_hom_id

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Points
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport

/-!
# The supported exterior product

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer,
`def-pur-supported-exterior-product`, pulling back supported sections and tensoring them
(blueprint: def-pur-supported-exterior-product).

Supported coefficients are closed direct images of constant modules. The ordinary
adjunction is normalized by the quotient from constant coefficients. Its derived
adjunction and the coefficient tensor comparison specify the supported pairing.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- Cache the weak sheafification consequence of the existing exact sheafification.
Source: the small-etale sheafification API (blueprint: def-pur-supported-exterior-product). -/
theorem supportedHasWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

/-- Use the existing preadditive tensor structure without reopening sheafification
instance search under each tensor-complex binder.
Source: blueprint `def-pur-supported-exterior-product`, tensor construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_monoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Sheaf.monoidalPreadditive

/-- The cochain tensor is the signed total tensor complex.
Source: Mathlib cochain monoidal structure (blueprint: def-pur-supported-exterior-product). -/
theorem supportedComplexTensor_eq
    {D : Type*} [Category.{w} D] [Abelian D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    (P Q : CochainComplex D ℤ) : P ⊗ Q = HomologicalComplex.tensorObj P Q := by
  rfl

section TensorWrappers

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The existing monoidal sheafification property, with generic coefficients.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_isMonoidalGeneric (X : Scheme.{u}) :
    (X.smallEtaleTopology.W (A := C)).IsMonoidal := GrothendieckTopology.W.monoidal

/-- The existing preadditive tensor structure, with generic coefficients.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_monoidalPreadditiveGeneric (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology C) := Sheaf.monoidalPreadditive

/-- The existing sheaf tensor bifunctor at a variable scheme.
Source: blueprint constant tensor pairing (blueprint: def-pur-supported-exterior-product). -/
@[implicit_reducible]
noncomputable def supportedSheafTensorGeneric (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C :=
      curriedTensor _

/-- The signed complex tensor at a variable scheme, using the upstream structure.
Source: blueprint signed tensor pairing (blueprint: def-pur-supported-exterior-product). -/
@[implicit_reducible]
noncomputable def supportedComplexTensorGeneric (X : Scheme.{u}) :
    CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
      CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
        CochainComplex (Sheaf X.smallEtaleTopology C) ℤ := curriedTensor _

/-- The signed total tensor object, using the existing total complex construction.
Source: blueprint signed tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedTotalTensorGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :=
  HomologicalComplex.tensorObj (C := Sheaf X.smallEtaleTopology C) (c := .up ℤ) P Q

/-- Tensor two sheaf morphisms using the upstream bifunctor.
Source: blueprint constant tensor pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSheafTensorMapGeneric (X : Scheme.{u})
    {M M' N N' : Sheaf X.smallEtaleTopology C} (a : M ⟶ M') (b : N ⟶ N') :
    ((supportedSheafTensorGeneric C X).obj M).obj N ⟶
      ((supportedSheafTensorGeneric C X).obj M').obj N' :=
  ((supportedSheafTensorGeneric C X).map a).app N ≫
    ((supportedSheafTensorGeneric C X).obj M').map b

/-- Sheaf tensor with the specified coefficient ring.
Source: blueprint tensor convention (blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSheafTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) := supportedSheafTensorGeneric (ModuleCat.{u + 1} A) X

end TensorWrappers

/-- Closed supported constant coefficients. Source: blueprint
`def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficients (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i

/-- The quotient from constant coefficients to closed supported coefficients.
Source: blueprint `def-pur-supported-exterior-product`, open-closed coefficient sequence
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientQuotient (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportedCoefficients A i).obj M :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app M)

/-- Additivity of closed supported coefficients. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_additive
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (supportedCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i).Additive)

/-- Exactness of closed supported coefficients.
Source: blueprint `def-pur-supported-exterior-product`, closed-support construction
(blueprint: def-pur-supported-exterior-product).
Proof: at a geometric point the closed direct image of a constant module has stalk
that module on the closed subset and zero outside. Both functors on modules are exact.
Exact and conservative geometric stalks detect finite limits and finite colimits.
The same argument handles the empty closed subscheme. -/
theorem supportedCoefficients_exact (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) ∧
      PreservesFiniteColimits (supportedCoefficients A i) := by
  constructor <;> unfold supportedCoefficients <;> infer_instance

/-- The finite-limit instance from closed-support exactness. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_preservesFiniteLimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).1

/-- The finite-colimit instance from closed-support exactness. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_preservesFiniteColimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).2

section OrdinaryAdjunctionProof

set_option backward.isDefEq.respectTransparency false

private theorem adjunctionNormalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {LZ : C ⥤ E} {RZ : E ⥤ C}
    {I : E ⥤ D} {J : D ⥤ E} {S : D ⥤ C}
    (ax : L ⊣ R) (az : LZ ⊣ RZ) (b : I ⊣ J)
    (γ : I ⋙ R ≅ RZ) (ε : J ⋙ RZ ≅ S) (δ : S ⟶ R)
    (M : C) (F : D) (q : L.obj M ⟶ I.obj (LZ.obj M))
    (hq : ax.unit.app M ≫ R.map q ≫ γ.hom.app (LZ.obj M) = az.unit.app M)
    (hc : ε.hom.app F ≫ δ.app F = γ.inv.app (J.obj F) ≫ R.map (b.counit.app F))
    (f : M ⟶ S.obj F) :
    q ≫ (((az.comp b).ofNatIsoRight ε).homEquiv M F).symm f =
      (ax.homEquiv M F).symm (f ≫ δ.app F) := by
  have hq' : ax.unit.app M ≫ R.map q =
      az.unit.app M ≫ γ.inv.app (LZ.obj M) := by
    erw [← hq]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  apply (ax.homEquiv M F).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_counit]
  erw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hq', Category.assoc,
    ← γ.inv.naturality_assoc]
  erw [← Category.assoc, ← Adjunction.homEquiv_apply, Equiv.apply_symm_apply]
  erw [Category.assoc, ← hc, Iso.inv_hom_id_app_assoc]

private lemma constantUnit_terminal
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafAdj X.smallEtaleTopology C
      terminalIsTerminal).unit.app M ≫
      ((sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale))).map (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompSheafSectionsTerminalIso C i).hom.app _ =
    (constantSheafAdj Z.smallEtaleTopology C
      terminalIsTerminal).unit.app M := by
  let ax := constantSheafAdj X.smallEtaleTopology C terminalIsTerminal
  let az := constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal
  let p := upperStarLowerStarAdjunction C i
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ax.comp p).ofNatIsoRight e) az M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  change (ax.comp p).unit.app M ≫ e.hom.app _ ≫
    ((sheafSections Z.smallEtaleTopology C).obj
      (op (⊤_ Z.Etale))).map ((Scheme.upperStarConstantSheafIso
        C i).hom.app M) = az.unit.app M at h
  rw [← h]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← e.hom.naturality]
  rfl

private lemma constantUnit_global
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafΓAdj X.smallEtaleTopology C).unit.app M ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompGlobalSectionsIso C i).hom.app _ =
    (constantSheafΓAdj Z.smallEtaleTopology C).unit.app M := by
  let nx : Sheaf.Γ X.smallEtaleTopology C ≅
      (sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale)) := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology C terminalIsTerminal
  let nz : Sheaf.Γ Z.smallEtaleTopology C ≅
      (sheafSections Z.smallEtaleTopology C).obj
        (op (⊤_ Z.Etale)) := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology C terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have hx := (constantSheafΓAdj X.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj X.smallEtaleTopology C terminalIsTerminal) M
  have hz := (constantSheafΓAdj Z.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal) M
  have hinj : Function.Injective
      (fun f : M ⟶ (Sheaf.Γ Z.smallEtaleTopology C).obj
        ((constantSheaf Z.smallEtaleTopology C).obj M) ↦
        f ≫ nz.hom.app ((constantSheaf Z.smallEtaleTopology C).obj M)) :=
    fun f g h ↦ (cancel_mono _).1 h
  apply hinj
  simp only [nz, lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc]
  erw [nx.hom.naturality_assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]
  rw [← Category.assoc]
  erw [hx, hz]
  exact constantUnit_terminal C i M

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
private lemma aux_isIso_of_isIso_left {V W : X.Etale} (f : V ⟶ W)
    (hf : IsIso f.left) : IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
private theorem aux_isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map
      ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j))) := by
  refine aux_isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map
    ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

section Restriction

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local instance] aux_isIso_overPullback_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
private theorem aux_isIso_lowerStar_obj_map_isTerminalMkId_from (G : Sheaf U.smallEtaleTopology C) :
    IsIso (((j)_*[C].obj G).obj.map ((Scheme.Etale.isTerminalMkId X).from
      (Scheme.Etale.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
private theorem aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf X.smallEtaleTopology C) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
      (op (Scheme.Etale.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app (Scheme.Etale.mk j)).op ≫ 𝟙 _))

attribute [local instance] aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
private lemma aux_ΓRes_eq (M : Sheaf X.smallEtaleTopology C) :
    M.ΓRes (op (Scheme.Etale.mk j)) =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)).op :=
  (M.ΓRes_map _).symm

private theorem aux_isIso_ΓRes_terminal (M : Sheaf X.smallEtaleTopology C) :
    IsIso (M.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op

attribute [local instance] aux_isIso_ΓRes_terminal
end Restriction

section Sections

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from
  aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
  aux_isIso_ΓRes_terminal
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [HasSmallSiteSheafify C] in
/-- For a sheaf `G` on `U`, the restriction `Γ(X, j_* G) ⟶ (j_* G)(U)` is an isomorphism. -/
private theorem normalization_isIso_ΓRes_lowerStar_obj (G : Sheaf U.smallEtaleTopology C) :
    IsIso (((j)_*[C].obj G).ΓRes (op (Scheme.Etale.mk j))) := by
  rw [aux_ΓRes_eq]
  infer_instance

attribute [local instance] normalization_isIso_ΓRes_lowerStar_obj

omit [HasSmallSiteSheafify C] in
/-- The sections over `U` of the inclusion `𝒢_Z M ⟶ M` of the supported sections vanish, so the
global sections of the inclusion restrict to zero on `U`. -/
@[reassoc]
private lemma normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes
    (M : Sheaf X.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).map ((sectionsWithSupportι C j).app M) ≫
      M.ΓRes (op (Scheme.Etale.mk j)) = 0 := by
  erw [Sheaf.ΓRes_naturality]
  have : IsZero (((sectionsWithSupport C j).obj M).obj.obj (op (Scheme.Etale.mk j))) :=
    isZero_obj_of_isZero_upperStar (isZero_upperStar_sectionsWithSupport C j M) _
      subset_rfl
  rw [this.eq_of_tgt (Sheaf.ΓRes _ _) 0, zero_comp]

omit [HasSmallSiteSheafify C] in
/-- The global sections of the unit `M ⟶ j_* j^* M` are the restriction `Γ(X, M) ⟶ M(U)`
followed by the identification `M(U) ≅ (j_* j^* M)(U) ≅ Γ(X, j_* j^* M)`. -/
private lemma normalization_ΓMap_unit_app_eq (M : Sheaf X.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).map ((upperStarLowerStarAdjunction C j).unit.app M) =
      M.ΓRes (op (Scheme.Etale.mk j)) ≫
        ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
          (op (Scheme.Etale.mk j)) ≫
        inv (((j)_*[C].obj ((openImmersionRestriction C j).obj M)).ΓRes
          (op (Scheme.Etale.mk j))) ≫
        (Sheaf.Γ X.smallEtaleTopology C).map ((j)_*[C].map
          (((upperStarLowerStarAdjunction C j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction C j)).inv.app M)) := by
  have h₁ := Sheaf.ΓRes_naturality ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M)
    (op (Scheme.Etale.mk j))
  rw [← reassoc_of% h₁, IsIso.hom_inv_id_assoc, ← Functor.map_comp]
  congr 1
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction C j)
    (openImmersionRestrictionLowerStarAdjunction C j), assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp

/-- The global sections of the inclusion `𝒢_Z M ⟶ M` of the sections supported on the closed
complement `Z` of `j` form a kernel of the restriction `Γ(X, M) ⟶ M(U)`: `Γ` preserves the kernel
`𝒢_Z M` of `M ⟶ j_* j^* M`, and `Γ(X, M) ⟶ Γ(X, j_* j^* M)` is the restriction `Γ(X, M) ⟶ M(U)`
followed by an isomorphism (`AlgebraicGeometry.Etale.normalization_ΓMap_unit_app_eq`). -/
private noncomputable def normalization_isLimitΓMapSectionsWithSupportι
    (M : Sheaf X.smallEtaleTopology C) :
    IsLimit (KernelFork.ofι _ (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)) :=
  isKernelOfComp _ _ (KernelFork.mapIsLimit _
    (kernelIsKernel ((upperStarLowerStarAdjunction C j).unit.app M))
      (Sheaf.Γ X.smallEtaleTopology C))
    (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)
    (normalization_ΓMap_unit_app_eq C j M).symm

end Sections

section SupportCohomology
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The sections with support `Γ_Z(X, M) ⟶ Γ(X, M)` form a kernel of the restriction
`Γ(X, M) ⟶ M(U)`. -/
private noncomputable def normalization_isLimitSectionsWithSupport
    (M : Sheaf X.smallEtaleTopology C) :
    IsLimit (KernelFork.ofι _ (Sheaf.ΓSupportι_app_comp_ΓRes X.smallEtaleTopology C
      (op (Scheme.Etale.mk i.openComplement.ι)) M)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes X.smallEtaleTopology C
    (op (Scheme.Etale.mk i.openComplement.ι)))) ((evaluation _ C).obj M)

/-- The sections with support in `Z` are the global sections of the subsheaf of sections
supported on `Z`: `Γ(X, 𝒢_Z M) ≅ Γ_Z(X, M)`, compatibly with the inclusions into `Γ(X, M)`. -/
private noncomputable def normalization_sectionsWithSupportCompΓIso :
    sectionsWithSupport C i.openComplement.ι ⋙ Sheaf.Γ X.smallEtaleTopology C ≅
      kernel (Sheaf.natTransΓRes X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))) :=
  NatIso.ofComponents
    (fun M ↦
      (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι M).conePointUniqueUpToIso
      (normalization_isLimitSectionsWithSupport C i M))
    (fun {M N} f ↦ by
      rw [← cancel_mono ((Sheaf.ΓSupportι X.smallEtaleTopology C _).app N)]
      have h₁ := (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι
        M).conePointUniqueUpToIso_hom_comp (normalization_isLimitSectionsWithSupport C i M) .zero
      have h₂ := (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι
        N).conePointUniqueUpToIso_hom_comp (normalization_isLimitSectionsWithSupport C i N) .zero
      simp only [KernelFork.ofι, Fork.ofι_π_app] at h₁ h₂
      simp only [Functor.comp_map, assoc, h₂]
      erw [(Sheaf.ΓSupportι X.smallEtaleTopology C _).naturality f, reassoc_of% h₁]
      erw [← Functor.map_comp, ← Functor.map_comp,
        ← (sectionsWithSupportι C i.openComplement.ι).naturality f])

omit [HasSmallSiteSheafify C] in
@[reassoc (attr := simp)]
private lemma normalization_sectionsWithSupportCompΓIso_hom_app_comp
    (M : Sheaf X.smallEtaleTopology C) :
    (normalization_sectionsWithSupportCompΓIso C i).hom.app M ≫
        (Sheaf.ΓSupportι X.smallEtaleTopology C _).app M =
      (Sheaf.Γ X.smallEtaleTopology C).map ((sectionsWithSupportι C _).app M) := by
  let e := normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι M
  have h := e.conePointUniqueUpToIso_hom_comp
    (normalization_isLimitSectionsWithSupport C i M) WalkingParallelPair.zero
  simp only [KernelFork.ofι, Fork.ofι_π_app] at h
  exact h

/-- `Γ_Z(X, M) ≅ Γ(Z, i^! M)`: the sections with support in `Z` are the global sections of the
exceptional inverse image `i^! M` (`AlgebraicGeometry.Etale.closedUpperShriek`), through
`Γ(Z, i^! M) ≅ Γ(X, i_* i^! M) ≅ Γ(X, 𝒢_Z M)`. -/
private noncomputable def normalization_closedUpperShriekCompΓIso :
    closedUpperShriek C i i.openComplement.ι ⋙ Sheaf.Γ Z.smallEtaleTopology C ≅
      kernel (Sheaf.natTransΓRes X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))) :=
  Functor.isoWhiskerLeft _ (lowerStarCompGlobalSectionsIso C i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (closedUpperShriekCompLowerStarIso C i _
      i.range_eq_compl_range_openComplement_ι) _ ≪≫
    normalization_sectionsWithSupportCompΓIso C i

omit [HasSmallSiteSheafify C] in
private lemma normalization_closedUpperShriekCompΓIso_hom_comp
    (F : Sheaf X.smallEtaleTopology C) :
    (normalization_closedUpperShriekCompΓIso C i).hom.app F ≫
      (Sheaf.ΓSupportι X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))).app F =
      (lowerStarCompGlobalSectionsIso C i).inv.app
        ((closedUpperShriek C i i.openComplement.ι).obj F) ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        ((lowerStarClosedUpperShriekAdjunction C i i.openComplement.ι
          i.range_eq_compl_range_openComplement_ι).counit.app F) := by
  simp only [normalization_closedUpperShriekCompΓIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc,
    normalization_sectionsWithSupportCompΓIso_hom_app_comp,
    lowerStarClosedUpperShriekAdjunction_counit_app, Functor.map_comp]

end SupportCohomology

private theorem closedUnit_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app G) := by
  let C := ModuleCat.{u + 1} A
  let adj := upperStarLowerStarAdjunction C i
  let j := i.openComplement.ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp [j, Scheme.Hom.coe_openComplement]
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar (j := j) i hij ?_ ?_)
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C j) (adj.unit.app G))
    refine IsZero.of_epi (cokernel.π _) ?_
    exact isZero_upperStar_lowerStar_of_disjoint_range C j i
      (by rw [hij]; exact disjoint_compl_right) _
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C i) (adj.unit.app G))
    have : IsIso ((upperStar C i).map (adj.unit.app G)) := by
      have : IsIso ((upperStar C i).map (adj.unit.app G) ≫ adj.counit.app _) := by
        rw [adj.left_triangle_components G]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    exact isZero_cokernel_of_epi _

private theorem coefficientQuotient_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : ModuleCat.{u + 1} A) :
    Epi (supportedCoefficientQuotient A i M) := by
  change Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app M))
  have := closedUnit_epi A i
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
  infer_instance

private theorem ordinaryAdjunctionExists
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F) := by
  let C := ModuleCat.{u + 1} A
  let b := lowerStarClosedUpperShriekAdjunction C i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι
  let e := normalization_closedUpperShriekCompΓIso C i
  let a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement :=
    ((constantSheafΓAdj Z.smallEtaleTopology C).comp b).ofNatIsoRight e
  refine ⟨a, ?_⟩
  intro M F f
  exact adjunctionNormalization (constantSheafΓAdj X.smallEtaleTopology C)
    (constantSheafΓAdj Z.smallEtaleTopology C) b (lowerStarCompGlobalSectionsIso C i)
    e (supportedEtaleSectionsι A X i.openComplement) M F
    (supportedCoefficientQuotient A i M) (constantUnit_global C i M)
    (normalization_closedUpperShriekCompΓIso_hom_comp C i F) f
end OrdinaryAdjunctionProof

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary adjunction, uniquely normalized by inclusion of the support kernel.
Source: blueprint `def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product).
Proof: apply Hom into F to the open-closed sequence of constant M. The kernel of
restriction is Hom from M into the kernel defining supported sections. The quotient
is epic, so precomposition determines the Hom equivalence uniquely. Naturality of
restriction gives naturality in both variables and hence the adjunction. -/
theorem exists_unique_supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F) := by
  obtain ⟨a, ha⟩ := ordinaryAdjunctionExists A i
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Adjunction.ext_counit
  apply NatTrans.ext
  funext F
  let M := (supportedEtaleSections A X i.openComplement).obj F
  have := coefficientQuotient_epi A i M
  have h := (cancel_epi (supportedCoefficientQuotient A i M)).1
    ((ha' M F (𝟙 _)).trans (ha M F (𝟙 _)).symm)
  simp only [Adjunction.homEquiv_symm_apply] at h
  erw [(supportedCoefficients A i).map_id M, Category.id_comp] at h
  exact h

/-- Canonical ordinary supported-coefficient adjunction, selected from its unique
normalization. Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement :=
  (exists_unique_supportedCoefficientAdjunction A i).choose

/-- The unbounded support functor, extending the bounded-below injective construction.
Source: blueprint `def-pur-supported-exterior-product`, derived support resolutions
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSectionsDerived
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportedEtaleSections A X i.openComplement).rightDerivedFunctor

/-- Derive the normalized ordinary adjunction with its exact left adjoint.
Source: blueprint `def-pur-supported-exterior-product`, K-flat and injective derivation
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientDerivedAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (supportedCoefficients A i).mapDerivedCategory ⊣ supportedSectionsDerived A i :=
  (supportedCoefficientAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

/-- The closed immersion of the product of the two supports.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedProductImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    pullback (i ≫ f) (j ≫ g) ⟶ pullback f g :=
  pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 B) (by simp) (by simp)

/-- Closedness of the product support. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product).
Proof: the product map is the composite of the two base changes of the closed
immersions. Closed immersions are stable under base change and composition. -/
@[instance]
theorem supportedProductImmersion_isClosedImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (supportedProductImmersion f g i j) := by
  set_option backward.isDefEq.respectTransparency false in
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstanceAs (IsClosedImmersion i))
      (inferInstanceAs (IsClosedImmersion j)) rfl rfl

/-- The pointwise constant-presheaf tensor comparison.
Source: blueprint `def-pur-supported-exterior-product`, constant section tensor
(blueprint: def-pur-supported-exterior-product). -/
def constantPresheafTensor (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (Functor.const T.Etaleᵒᵖ).obj (M ⊗ N) ⟶
      (Functor.const T.Etaleᵒᵖ).obj M ⊗ (Functor.const T.Etaleᵒᵖ).obj N where
  app _ := 𝟙 _
  naturality _ _ _ := by simp

/-- Constant coefficient tensor comparison before pulling back either factor.
Source: blueprint constant section pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedConstantTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A X).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N) :=
  (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
      (constantPresheafTensor A X M N) ≫
    (Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      ((Functor.const _).obj M) ((Functor.const _).obj N)).inv

/-- Tensor comparison for constant coefficients and the two projection pullbacks.
Source: blueprint `def-pur-supported-exterior-product`, constant section pairing
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def constantExteriorTensor (A : Type (u + 1)) [CommRing A]
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A (pullback f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)) :=
  supportedConstantTensor A (pullback f g) M N ≫
    supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv.app M)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv.app N)

/-- Supported coefficients pulled back along the first projection.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedFirstCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y Z : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) :=
  supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)

/-- Supported coefficients pulled back along the second projection.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSecondCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) :=
  supportedCoefficients A j ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)

private theorem coefficientQuotient_naturality
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {M M' : ModuleCat.{u + 1} A} (f : M ⟶ M') :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map f ≫
        supportedCoefficientQuotient A i M' =
      supportedCoefficientQuotient A i M ≫ (supportedCoefficients A i).map f := by
  let η := Functor.whiskerLeft
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit
  let ν := Functor.whiskerRight
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom
    (lowerStar (ModuleCat.{u + 1} A) i)
  exact (η ≫ ν).naturality f

private theorem zero_of_open_cover
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology C)
    {I : Type*} {V : I → Scheme.{u}} (a : ∀ k, V k ⟶ T)
    [∀ k, IsOpenImmersion (a k)]
    (ha : ⋃ k, Set.range (a k).base = Set.univ)
    (hF : ∀ k, IsZero ((upperStar C (a k)).obj F)) : IsZero F := by
  have h : IsIso (0 : F ⟶ 0) := by
    apply isIso_of_isIso_localizationRestriction C (0 : F ⟶ 0) a ha
    intro k
    have hz := (hF k).of_iso
      ((upperStarIsoLocalizationRestriction C (a k) inferInstance).app F).symm
    exact hz.isIso ((localizationRestriction C (a k) inferInstance).map_isZero
      (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private theorem coefficient_zero_on_complement
    (A : Type (u + 1)) [CommRing A] {Z X T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (a : T ⟶ X)
    (ha : Set.range a.base ⊆ (i.openComplement : Set X))
    (M : ModuleCat.{u + 1} A) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) a).obj
      ((supportedCoefficients A i).obj M)) := by
  let C := ModuleCat.{u + 1} A
  let v := i.openComplement.ι
  have hav : Set.range a.base ⊆ Set.range v.base := by
    simpa only [v, Scheme.Opens.range_ι] using ha
  let l := IsOpenImmersion.lift v a hav
  have hz : IsZero ((upperStar C v).obj ((supportedCoefficients A i).obj M)) := by
    apply isZero_upperStar_lowerStar_of_disjoint_range C v i
    rw [show Set.range v.base = (Set.range i.base)ᶜ by
      simp [v, Scheme.Hom.coe_openComplement]]
    exact disjoint_compl_left
  exact ((upperStar C l).map_isZero hz).of_iso
    ((upperStarComp C l v a (IsOpenImmersion.lift_fac v a hav).symm).app _)

private theorem tensor_zero_on_union
    (A : Type (u + 1)) [CommRing A] {T X Y Z W : Scheme.{u}}
    (p : T ⟶ X) (q : T ⟶ Y) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (V : T.Opens) (hV : V = p ⁻¹ᵁ i.openComplement ⊔ q ⁻¹ᵁ j.openComplement)
    (M N : ModuleCat.{u + 1} A) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) V.ι).obj
      (((upperStar (ModuleCat.{u + 1} A) p).obj ((supportedCoefficients A i).obj M)) ⊗
        ((upperStar (ModuleCat.{u + 1} A) q).obj ((supportedCoefficients A j).obj N)))) := by
  let C := ModuleCat.{u + 1} A
  let F := (upperStar C p).obj ((supportedCoefficients A i).obj M)
  let G := (upperStar C q).obj ((supportedCoefficients A j).obj N)
  let O : Bool → V.toScheme.Opens := fun b ↦
    if b then V.ι ⁻¹ᵁ (p ⁻¹ᵁ i.openComplement) else V.ι ⁻¹ᵁ (q ⁻¹ᵁ j.openComplement)
  have hcov : ⋃ b, Set.range (O b).ι.base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : V.ι.base x ∈ (p ⁻¹ᵁ i.openComplement : Set T) ∪
        (q ⁻¹ᵁ j.openComplement : Set T) := by
      change V.ι.base x ∈ ((p ⁻¹ᵁ i.openComplement ⊔ q ⁻¹ᵁ j.openComplement) : T.Opens)
      rw [← hV]
      exact x.2
    rcases hx with hx | hx
    · apply Set.mem_iUnion.2
      refine ⟨true, ?_⟩
      rw [Scheme.Opens.range_ι]
      exact hx
    · apply Set.mem_iUnion.2
      refine ⟨false, ?_⟩
      rw [Scheme.Opens.range_ι]
      exact hx
  apply zero_of_open_cover C _ (fun b ↦ (O b).ι) hcov
  intro b
  let a := (O b).ι ≫ V.ι
  have hz : IsZero ((upperStar C a).obj (F ⊗ G)) := by
    cases b
    · have hq : Set.range (a ≫ q).base ⊆ (j.openComplement : Set Y) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      have h₀ := coefficient_zero_on_complement A j (a ≫ q) hq N
      have hG : IsZero ((upperStar C a).obj G) :=
        h₀.of_iso ((upperStarComp C a q).app _).symm
      exact ((tensorLeft ((upperStar C a).obj F)).map_isZero hG).of_iso
        (Functor.Monoidal.μIso (upperStar C a) F G).symm
    · have hp : Set.range (a ≫ p).base ⊆ (i.openComplement : Set X) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      have h₀ := coefficient_zero_on_complement A i (a ≫ p) hp M
      have hF : IsZero ((upperStar C a).obj F) :=
        h₀.of_iso ((upperStarComp C a p).app _).symm
      exact ((tensorRight ((upperStar C a).obj G)).map_isZero hF).of_iso
        (Functor.Monoidal.μIso (upperStar C a) F G).symm
  exact hz.of_iso ((upperStarComp C (O b).ι V.ι).app (F ⊗ G)).symm

private theorem coefficient_factorization
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : ModuleCat.{u + 1} A)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : IsZero ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).obj F))
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶ F) :
    ∃! t : (supportedCoefficients A i).obj M ⟶ F,
      supportedCoefficientQuotient A i M ≫ t = α := by
  let C := ModuleCat.{u + 1} A
  let a := upperStarLowerStarAdjunction C i
  let b := Scheme.upperStarConstantSheafIso C i
  have : IsIso (a.unit.app F) :=
    isIso_upperStarLowerStarAdjunction_unit_app_of_isZero C i i.openComplement.ι
      (by simp) hF
  let t : (supportedCoefficients A i).obj M ⟶ F :=
    (lowerStar C i).map (b.inv.app M) ≫
      (lowerStar C i).map ((upperStar C i).map α) ≫ inv (a.unit.app F)
  have ht : supportedCoefficientQuotient A i M ≫ t = α := by
    exact adjunction_factorization_equation a (b.app M) α
  have := coefficientQuotient_epi A i M
  exact ⟨t, ht, fun t' ht' ↦ (cancel_epi (supportedCoefficientQuotient A i M)).1
    (ht'.trans ht.symm)⟩

/-- The supported coefficient tensor comparison is uniquely fixed by the quotient
of constant sections. Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product).
Proof: the target is zero off the intersection of the two inverse-image supports,
so the constant section pairing factors through the open-closed coefficient quotient.
That quotient is epic, giving uniqueness. On the intersection all maps are the
identity on M tensor N; elsewhere both supported coefficients are zero. Geometric
stalks detect that the resulting comparison is an isomorphism. -/
theorem exists_unique_supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (M N : ModuleCat.{u + 1} A) :
    ∃! t : (supportedCoefficients A (supportedProductImmersion f g i j)).obj (M ⊗ N) ⟶
        ((supportedSheafTensor A (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).obj M)).obj
          ((supportedSecondCoefficients A f g j).obj N),
      supportedCoefficientQuotient A (supportedProductImmersion f g i j) (M ⊗ N) ≫ t =
        constantExteriorTensor A f g M N ≫
          supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
            ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).map
              (supportedCoefficientQuotient A i M))
            ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).map
              (supportedCoefficientQuotient A j N)) := by
  have hc : (supportedProductImmersion f g i j).openComplement =
      pullback.fst f g ⁻¹ᵁ i.openComplement ⊔ pullback.snd f g ⁻¹ᵁ j.openComplement := by
    apply TopologicalSpace.Opens.ext
    simp [Scheme.Hom.coe_openComplement, supportedProductImmersion,
      Scheme.Pullback.range_map, Set.compl_inter, Set.preimage_compl]
  exact coefficient_factorization A (supportedProductImmersion f g i j) (M ⊗ N) _
    (tensor_zero_on_union A (pullback.fst f g) (pullback.snd f g) i j _ hc M N) _

/-- The uniquely normalized supported coefficient tensor comparison.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (M N : ModuleCat.{u + 1} A) :=
  (exists_unique_supportedCoefficientTensor A f g i j M N).choose

private theorem constantTensor_natural
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' N N' : ModuleCat.{u + 1} A} (a : M ⟶ M') (b : N ⟶ N') :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map (a ⊗ₘ b) ≫
        supportedConstantTensor A X M' N' =
      supportedConstantTensor A X M N ≫
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map a ⊗ₘ
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map b) := by
  exact (Functor.OplaxMonoidal.δ_natural
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) a b).symm

private noncomputable def coefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      supportedCoefficients A i where
  app := supportedCoefficientQuotient A i
  naturality _ _ f := coefficientQuotient_naturality A i f

private noncomputable def firstCoefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] {B X Y Z : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) [IsClosedImmersion i] :
    constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      supportedFirstCoefficients A f g i :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv ≫
    Functor.whiskerRight (coefficientQuotientNat A i)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))

private noncomputable def secondCoefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] {B X Y W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) [IsClosedImmersion j] :
    constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      supportedSecondCoefficients A f g j :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv ≫
    Functor.whiskerRight (coefficientQuotientNat A j)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))

private theorem coefficientTensor_spec
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (M N : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A (supportedProductImmersion f g i j) (M ⊗ N) ≫
        supportedCoefficientTensor A f g i j M N =
      supportedConstantTensor A (pullback f g) M N ≫
        ((firstCoefficientQuotientNat A f g i).app M ⊗ₘ
          (secondCoefficientQuotientNat A f g j).app N) := by
  have h := (exists_unique_supportedCoefficientTensor A f g i j M N).choose_spec.1
  change supportedCoefficientQuotient A (supportedProductImmersion f g i j) (M ⊗ N) ≫
    supportedCoefficientTensor A f g i j M N = _ at h
  rw [h]
  change (_ ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _ ≫ ((_ ≫ _) ⊗ₘ (_ ≫ _))
  rw [Category.assoc, tensorHom_comp_tensorHom]
  rfl

private theorem coefficientTensor_natural
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    {M M' N N' : ModuleCat.{u + 1} A} (a : M ⟶ M') (b : N ⟶ N') :
    (supportedCoefficients A (supportedProductImmersion f g i j)).map (a ⊗ₘ b) ≫
        supportedCoefficientTensor A f g i j M' N' =
      supportedCoefficientTensor A f g i j M N ≫
        ((supportedFirstCoefficients A f g i).map a ⊗ₘ
          (supportedSecondCoefficients A f g j).map b) := by
  have := coefficientQuotient_epi A (supportedProductImmersion f g i j) (M ⊗ N)
  apply (cancel_epi (supportedCoefficientQuotient A
    (supportedProductImmersion f g i j) (M ⊗ N))).1
  rw [← Category.assoc, ← coefficientQuotient_naturality, Category.assoc,
    coefficientTensor_spec, ← Category.assoc, constantTensor_natural, Category.assoc,
    tensorHom_comp_tensorHom, (firstCoefficientQuotientNat A f g i).naturality,
    (secondCoefficientQuotientNat A f g j).naturality, ← tensorHom_comp_tensorHom,
    ← Category.assoc, ← coefficientTensor_spec, Category.assoc]

/-- The natural bifunctor comparison for closed supported coefficients.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorNatTrans
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (Functor.postcompose₂.obj (supportedCoefficients A (supportedProductImmersion f g i j))).obj
        (curriedTensor (ModuleCat.{u + 1} A)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (supportedFirstCoefficients A f g i)).obj
        (supportedSecondCoefficients A f g j)).obj
          (supportedSheafTensor A (pullback f g)) where
  app M :=
    { app N := supportedCoefficientTensor A f g i j M N
      naturality N N' b := by
        change (supportedCoefficients A (supportedProductImmersion f g i j)).map (M ◁ b) ≫
          supportedCoefficientTensor A f g i j M N' =
            supportedCoefficientTensor A f g i j M N ≫
              ((supportedFirstCoefficients A f g i).obj M ◁
                (supportedSecondCoefficients A f g j).map b)
        simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using
          coefficientTensor_natural A f g i j (𝟙 M) b }
  naturality M M' a := by
    apply NatTrans.ext
    funext N
    change (supportedCoefficients A (supportedProductImmersion f g i j)).map (a ▷ N) ≫
      supportedCoefficientTensor A f g i j M' N =
        supportedCoefficientTensor A f g i j M N ≫
          ((supportedFirstCoefficients A f g i).map a ▷
            (supportedSecondCoefficients A f g j).obj N)
    simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using
      coefficientTensor_natural A f g i j a (𝟙 N)

attribute [local irreducible] HomologicalComplex₂.total

section CoefficientTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

open scoped ZeroObject in
end CoefficientTensorProof

section ComplexTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end ComplexTensorProof

/-- Morphisms from the image of a tensor complex to the tensor of the two images.
Source: blueprint total tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedComplexComparisonHom
    {D : Type*} [Category.{w} D] {E : Type*} [Category.{w} E]
    [Preadditive D] [Preadditive E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    (G G₁ G₂ : D ⥤ E) [G.Additive] [G₁.Additive] [G₂.Additive]
    (P Q : CochainComplex D ℤ) : Type _ :=
     (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ⟶
        HomologicalComplex.tensorObj
          ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((G₂.mapHomologicalComplex (.up ℤ)).obj Q)

/-- Normalization on all bidegree summands of a tensor-complex comparison.
Source: blueprint signed total tensor construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedComplexComparisonCondition
    {D : Type*} [Category.{w} D] {E : Type*} [Category.{w} E]
    [Preadditive D] [Preadditive E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    (G G₁ G₂ : D ⥤ E) [G.Additive] [G₁.Additive] [G₂.Additive]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ E).obj G₁).obj G₂).obj (curriedTensor E))
    (P Q : CochainComplex D ℤ)
    (t : supportedComplexComparisonHom G G₁ G₂ P Q) : Prop :=
      ∀ (r s n : ℤ) (h : r + s = n),
        G.map (HomologicalComplex.ιTensorObj P Q r s n h) ≫ t.f n =
          (τ.app (P.X r)).app (Q.X s) ≫ HomologicalComplex.ιTensorObj
            ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((G₂.mapHomologicalComplex (.up ℤ)).obj Q) r s n h

section AbstractDerivedTensor

variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

/-- The natural transformation of signed tensor complexes induced by a coefficient pairing.
Source: blueprint signed tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedComplexComparisonNatTrans
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesColimitsOfSize.{0, 0} G]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D)) :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _) :=
  HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)

/-- A signed tensor comparison, constructed through the totalization bifunctor.
Source: blueprint signed tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedComplexComparison
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesColimitsOfSize.{0, 0} G]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (P Q : CochainComplex C ℤ) : supportedComplexComparisonHom G F₁ F₂ P Q :=
  ((supportedComplexComparisonNatTrans G F₁ F₂ τ).app P).app Q

private theorem tensorLocalization_isIso (P Q : CochainComplex D ℤ)
    (hQ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient D (.up ℤ)).obj P)
      ((HomotopyCategory.quotient D (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

/-- Families of morphisms between the derived tensor images.
Source: blueprint derived tensor comparison (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedComparisonHom
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] : Type _ :=
  ∀ M N : DerivedCategory C,
      G.mapDerivedCategory.obj (M ⊗ N) ⟶
        F₁.mapDerivedCategory.obj M ⊗ F₂.mapDerivedCategory.obj N

private theorem tensorLocalization_model_eq (P Q : CochainComplex D ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
        DerivedCategory.Q.map (eqToHom (supportedComplexTensor_eq P Q)) =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q := by
  have h : eqToHom (supportedComplexTensor_eq P Q) = 𝟙 (P ⊗ Q) := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Naturality and normalization on all complex models, retaining the signed total tensor.
Source: blueprint derived tensor comparison (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedComparisonCondition
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : supportedDerivedComparisonHom G F₁ F₂) : Prop :=
  (∀ (M M' N N' : DerivedCategory C) (a : M ⟶ M') (b : N ⟶ N'),
        G.mapDerivedCategory.map (a ⊗ₘ b) ≫ t M' N' =
          t M N ≫ (F₁.mapDerivedCategory.map a ⊗ₘ F₂.mapDerivedCategory.map b)) ∧
      (∀ P Q : CochainComplex C ℤ,
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map ((τ.app P).app Q) =
        t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ
            F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          (Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) ≫
            DerivedCategory.Q.map (eqToHom (supportedComplexTensor_eq
              ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
              ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)))))

/-- Evaluate a derived comparison without expanding the total-complex implementation.
Source: blueprint derived tensor comparison (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedComparisonApply
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (t : supportedDerivedComparisonHom G F₁ F₂) (M N : DerivedCategory C) :
    G.mapDerivedCategory.obj (M ⊗ N) ⟶
      F₁.mapDerivedCategory.obj M ⊗ F₂.mapDerivedCategory.obj N := t M N

private theorem derivedComparison_unique
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _)) :
    ∃! t : supportedDerivedComparisonHom G F₁ F₂,
      supportedDerivedComparisonCondition G F₁ F₂ τ t := by
  unfold supportedDerivedComparisonHom supportedDerivedComparisonCondition
  simp only [tensorLocalization_model_eq]
  let U := (Functor.postcompose₂.obj G.mapDerivedCategory).obj
    (curriedTensor (DerivedCategory C))
  let V := (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
    F₂.mapDerivedCategory).obj (curriedTensor (DerivedCategory D))
  let α := mixedTensorCounit F₁ F₂
  have : V.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) := mixedTensor_isLeftDerived F₁ F₂
  let β := (Functor.postcompose₂.obj G.mapDerivedCategory).map
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q) ≫
    (Functor.postcompose₂.map G.mapDerivedCategoryFactors.hom).app
      (curriedTensor (CochainComplex C ℤ)) ≫
    Functor.postcompose₂MapWhiskeringLeft₂ τ DerivedCategory.Q
  let γ : U ⟶ V := V.leftDerived₂Lift α
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)) U β
  have hγ (P Q : CochainComplex C ℤ) :=
    V.leftDerived₂_fac_app_app α (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) U β P Q
  have hα (P Q : CochainComplex C ℤ) : (α.app P).app Q =
      (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ
        F₂.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) := by
    simp only [α, mixedTensorCounit, NatTrans.comp_app,
      MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  have hβ (P Q : CochainComplex C ℤ) : (β.app P).app Q =
      G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map ((τ.app P).app Q) := by rfl
  refine ⟨fun M N ↦ (γ.app M).app N, ⟨?_, ?_⟩, ?_⟩
  · intro M M' N N' a b
    have ha := congr_app (γ.naturality a) N
    have hb := (γ.app M').naturality b
    change G.mapDerivedCategory.map (a ▷ N) ≫ (γ.app M').app N =
      (γ.app M).app N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N) at ha
    change G.mapDerivedCategory.map (M' ◁ b) ≫ (γ.app M').app N' =
      (γ.app M').app N ≫ (F₁.mapDerivedCategory.obj M' ◁ F₂.mapDerivedCategory.map b) at hb
    rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc, hb,
      ← Category.assoc, ha, Category.assoc, ← MonoidalCategory.tensorHom_def]
  · intro P Q
    have h := hγ P Q
    rw [hα, hβ] at h
    exact h.symm
  · intro t ht
    let δ : U ⟶ V :=
      { app M :=
          { app N := t M N
            naturality N N' b := by
              change G.mapDerivedCategory.map (M ◁ b) ≫ t M N' =
                t M N ≫ (F₁.mapDerivedCategory.obj M ◁ F₂.mapDerivedCategory.map b)
              simpa only [id_tensorHom, CategoryTheory.Functor.map_id] using
                ht.1 M M N N' (𝟙 M) b }
        naturality M M' a := by
          apply NatTrans.ext
          funext N
          change G.mapDerivedCategory.map (a ▷ N) ≫ t M' N =
            t M N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N)
          simpa only [tensorHom_id, CategoryTheory.Functor.map_id] using
            ht.1 M M' N N a (𝟙 N) }
    have he : δ = γ := by
      apply V.leftDerived₂_ext α (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)) U
      apply NatTrans.ext
      funext P
      apply NatTrans.ext
      funext Q
      change t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫ (α.app P).app Q = _
      rw [hα]
      have h := hγ P Q
      rw [hβ] at h
      exact (ht.2 P Q).symm.trans h.symm
    exact congrArg (fun η : U ⟶ V ↦ fun M N ↦ (η.app M).app N) he

/-- Derived comparison families at a variable scheme.
Source: blueprint derived tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSchemeDerivedHom : Type _ :=
  supportedDerivedComparisonHom G F₁ F₂

/-- Model normalization for the derived coefficient comparison at a variable scheme.
Source: blueprint K-flat derivation (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSchemeDerivedCondition
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (supportedSheafTensorGeneric C T))
    (t : supportedSchemeDerivedHom C T G F₁ F₂) : Prop :=
  supportedDerivedComparisonCondition G F₁ F₂
    (supportedComplexComparisonNatTrans G F₁ F₂ τ) t

private theorem supportedSchemeDerived_unique [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (supportedSheafTensorGeneric C T)) :
    ∃! t : supportedSchemeDerivedHom C T G F₁ F₂,
      supportedSchemeDerivedCondition C T G F₁ F₂ τ t :=
  derivedComparison_unique G F₁ F₂ (supportedComplexComparisonNatTrans G F₁ F₂ τ)

/-- Evaluate the derived coefficient family with the canonical sheaf tensor structure.
Source: blueprint derived tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSchemeDerivedApply
    (t : supportedSchemeDerivedHom C T G F₁ F₂) (M N : DerivedCategory C) :
    G.mapDerivedCategory.obj (M ⊗ N) ⟶
      ((derivedTensor C T).obj (F₁.mapDerivedCategory.obj M)).obj
        (F₂.mapDerivedCategory.obj N) :=
  supportedDerivedComparisonApply G F₁ F₂ t M N

/-- Tensor morphisms through the existing derived bifunctor at a variable scheme.
Source: blueprint supported pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedTensorMap (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').obj N' :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).map a).app N ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').map b

/-- The morphism type for the signed derived coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerivedHom
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : Type (u + 2) :=
  supportedSchemeDerivedHom (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)

/-- The complete normalization of the signed derived coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerivedCondition
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (t : supportedCoefficientTensorDerivedHom A f g i j) : Prop :=
  supportedSchemeDerivedCondition (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorNatTrans A f g i j) t

private theorem closedPushforward_flat
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} A) i).obj M) := by
  let C := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  let F := (lowerStar C i).obj M
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp [j, Scheme.Hom.coe_openComplement, Scheme.Opens.range_ι]
  have hj : ObjectProperty.flat ((upperStar C j).obj F) :=
    ObjectProperty.flat_of_isZero
      (isZero_upperStar_lowerStar_of_disjoint_range C j i
        (disjoint_range_of_range_eq_compl j i hij) M)
  have hi : ObjectProperty.flat ((upperStar C i).obj F) :=
    ObjectProperty.prop_of_iso ObjectProperty.flat
      (asIso ((upperStarLowerStarAdjunction C i).counit.app M)).symm hM
  apply (flat_iff_forall_flat_sheafFiber_obj F).2
  intro Ω _ _ s
  obtain ⟨t, ht, -⟩ | ⟨t, ht, -⟩ :=
    existsUnique_fac_or_fac_of_range_eq_compl j i hij s
  · subst ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      ((upperStarCompUliftSheafFiberIso C j t).app F)
        ((flat_iff_forall_flat_sheafFiber_obj _).1 hj t)
  · subst ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      ((upperStarCompUliftSheafFiberIso C i t).app F)
        ((flat_iff_forall_flat_sheafFiber_obj _).1 hi t)

private theorem coefficients_preserveFlat
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : (supportedCoefficients A i).PreservesFlat := by
  constructor
  intro M hM
  exact closedPushforward_flat A i _
    (GrothendieckTopology.flat_presheafToSheaf_obj
      (ModuleCat.{u + 1} A) Z.smallEtaleTopology _ (fun _ ↦ hM))

/-- The coefficient comparison after localization, with its full complex-model
normalization and naturality, rather than an unspecified isomorphism.
Source: blueprint `def-pur-supported-exterior-product`, K-flat tensor derivation
(blueprint: def-pur-supported-exterior-product).
Proof: choose K-flat module complexes with flat terms. Closed supported coefficients
and their projection inverse images preserve these properties: on a stalk their
coefficient sheaves are A or zero, and tensor with each is exact. The signed total
comparison above is an isomorphism on each stalk. Localize it and use the K-flat
localization equivalence to descend it naturally in both variables. Its compatibility
with the tensor localization counits is the displayed equation, also for other
complexes by naturality. Every derived object is isomorphic to the localization of
a K-flat model, and the localization tensor counits are isomorphisms on such models;
therefore that equation and naturality determine the family uniquely. -/
theorem exists_unique_supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! t : supportedCoefficientTensorDerivedHom A f g i j,
      supportedCoefficientTensorDerivedCondition A f g i j t  := by
  have : (supportedCoefficients A j).PreservesFlat := coefficients_preserveFlat A j
  have : (supportedSecondCoefficients A f g j).IsLeftAdjoint :=
    inferInstanceAs ((supportedCoefficients A j) ⋙
      upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).IsLeftAdjoint
  have : (supportedSecondCoefficients A f g j).PreservesFlat :=
    ⟨fun h ↦ Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A)
      (pullback.snd f g)) (Functor.PreservesFlat.flat_obj h)⟩
  exact supportedSchemeDerived_unique (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorNatTrans A f g i j)

/-- The derived coefficient comparison with its uniquely specified model normalization.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
      (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) :=
  supportedSchemeDerivedApply (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose M N

/-- Pull back the supported evaluation counit along the first projection, retaining
all exact-functor and total-derived pullback comparisons.
Source: blueprint `def-pur-supported-exterior-product`, evaluation construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedFirstEvaluation
    (A : Type (u + 1)) [CommRing A] {B X Y Z : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))).hom.app
        ((supportedSectionsDerived A i).obj K) ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.map
      ((supportedCoefficientDerivedAdjunction A i).counit.app K) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).inv.app K

/-- Pull back the supported evaluation counit along the second projection.
Source: blueprint `def-pur-supported-exterior-product`, evaluation construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSecondEvaluation
    (A : Type (u + 1)) [CommRing A] {B X Y W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) [IsClosedImmersion j]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A j)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))).hom.app
        ((supportedSectionsDerived A j).obj L) ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.map
      ((supportedCoefficientDerivedAdjunction A j).counit.app L) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).inv.app L

/-- The supported exterior product: the adjoint of the coefficient tensor comparison
followed by the tensor of the two supported evaluation counits.
Source: blueprint `def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product). The comparison is normalized on every
cochain bidegree, so this is the actual supported section pairing. In the bounded-below
case the total support functor agrees with injective support resolutions. -/
noncomputable def supportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportedSectionsDerived A i).obj K ⊗ (supportedSectionsDerived A j).obj L ⟶
      (supportedSectionsDerived A (supportedProductImmersion f g i j)).obj
        (externalProduct (ModuleCat.{u + 1} A) f g K L) :=
  (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g i j)).homEquiv _ _
    (supportedCoefficientTensorDerived A f g i j
        ((supportedSectionsDerived A i).obj K) ((supportedSectionsDerived A j).obj L) ≫
      supportedDerivedTensorMap A (pullback f g)
        (supportedFirstEvaluation A f g i K) (supportedSecondEvaluation A f g j L))

end AbstractDerivedTensor

attribute [local irreducible] supportedDerivedComparisonHom
  supportedDerivedComparisonCondition supportedComplexComparisonHom
  supportedComplexComparisonCondition

section SchemeComparisons

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] (T : Scheme.{u})
  (G F₁ F₂ : C ⥤ Sheaf T.smallEtaleTopology C)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

variable [G.IsLeftAdjoint]

section ComparisonSpec

attribute [local semireducible] supportedComplexComparisonHom

omit [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] in
end ComparisonSpec

end SchemeComparisons

section DerivedTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end DerivedTensorProof

end AlgebraicGeometry.Etale

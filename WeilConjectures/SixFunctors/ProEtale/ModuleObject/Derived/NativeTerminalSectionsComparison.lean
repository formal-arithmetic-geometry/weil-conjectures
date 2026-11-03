/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars

/-! # Actual terminal evaluation and regular-module sections
Source: the tensor-unit and free-module universal properties
(blueprint: lem-sf-native-terminal-sections-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.InternalAbelianSheafModule CategoryTheory.MonObj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    {A : Type (u + 1)} [CommRing A] (s : A →+* MonObj.Γ O)
    (U : C) (hU : IsTerminal U)

/-- Regular-module sections with the specified scalar action.
Source: free-module universal property
(blueprint: lem-sf-native-terminal-sections-comparison). -/
abbrev regularSections := coyonedaSections ((Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp s))

/-- Underlying abelian-sheaf evaluation at the specified terminal object.
Source: terminal sections (blueprint: lem-sf-native-terminal-sections-comparison). -/
abbrev site_eval :=
  sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation Cᵒᵖ Ab.{u + 1}).obj (op U)

private instance evaluation_monoidal :
    ((evaluation Cᵒᵖ Ab.{u + 1}).obj (op U)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

/-- Evaluation retains pointwise tensor products and the tensor unit.
Source: pointwise tensor structure
(blueprint: lem-sf-native-terminal-sections-comparison). -/
instance evaluation_monoidal :
    ((evaluation Cᵒᵖ Ab.{u + 1}).obj (op U)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

/-- A regular-module morphism evaluated at the unit section 1.
Source: free-module universal property
(blueprint: lem-sf-native-terminal-sections-comparison). -/
def terminal_eval (M : Mod (Sheaf J Ab.{u + 1}) O) :
    (regularSections J O s).obj M →
      (Evaluation.sections J O U ⋙ ModuleCat.restrictScalars
        ((sectionGlobalEval J O U).comp s)).obj M :=
  fun f ↦ ((Functor.LaxMonoidal.ε (site_eval J U) ≫
    (site_eval J U).map (η[O] ≫ f.hom)).hom) (ULift.up 1)

/-- Evaluation at 1 is bijective on regular-module sections.
Source: tensor-unit/free-module universal properties
(blueprint: lem-sf-native-terminal-sections-comparison).

Proof: the regular-module adjunction identifies a module morphism with its
composite with the ring unit. The constant-sheaf adjunction then identifies the
latter with a terminal section, evaluated at the free abelian generator 1.
The two bijections compose to the displayed evaluation map. -/
theorem terminal_eval_bijective (M : Mod (Sheaf J Ab.{u + 1}) O) :
    Function.Bijective (terminal_eval J O s U M) := by
  let e : (Mod.regular O ⟶ M) ≃ (𝟙_ (Sheaf J Ab.{u + 1}) ⟶ M.X) :=
    { toFun f := η[O] ≫ f.hom
      invFun f := Mod.regularLift M f
      left_inv f := Mod.regular_hom_ext (Mod.one_comp_regularLift _ _)
      right_inv f := Mod.one_comp_regularLift _ _ }
  let q := ((constantSheafAdj J Ab.{u + 1} hU).homEquiv (𝟙_ Ab.{u + 1}) M.X).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv (M.X.obj.obj (op U))).toEquiv
  exact (q.bijective.comp e.bijective)

include hU in
/-- The evaluation-at-one map with its specified scalar linearity.
Source: regular multiplication acts sectionwise
(blueprint: lem-sf-native-terminal-sections-comparison). -/
def terminal_linear (M : Mod (Sheaf J Ab.{u + 1}) O) :
    (regularSections J O s).obj M →ₗ[A]
      (Evaluation.sections J O U ⋙ ModuleCat.restrictScalars
        ((sectionGlobalEval J O U).comp s)).obj M where
  toFun := terminal_eval J O s U M
  map_add' f g := by
    simp only [terminal_eval]
    rfl
  map_smul' a f := by
    change ((Functor.LaxMonoidal.ε (site_eval J U) ≫ (site_eval J U).map
      (η[O] ≫ (Mod.regularLift (Mod.regular O) (s a).hom ≫ f).hom)).hom)
      (ULift.up 1) = _
    rw [Mod.one_comp_regularLift_comp_hom]
    let F := site_eval J U
    have h := Mod.globalSmul_mapMod F (s a).hom M
    rw [Functor.map_comp, ← h]
    let _ := F.monObjObj O
    change (Mod.act ((F.mapMod O).obj M).X).hom
      (((Functor.LaxMonoidal.ε F ≫ F.map (s a).hom).hom) (ULift.up 1) ⊗ₜ[ℤ]
        ((Functor.LaxMonoidal.ε F ≫ F.map (η[O] ≫ f.hom)).hom) (ULift.up 1)) = _
    rfl

/-- The explicit terminal-sections comparison, normalized by evaluation at 1.
This exposes the very data used by `native_terminalSectionsIso`, so callers needing
its specified normalization do not have to choose an unspecified natural isomorphism.
Source: tensor-unit/free-module universal properties
(blueprint: lem-sf-native-terminal-sections-comparison). -/
def native_terminalSectionsComparison :
    coyonedaSections ((Mod.regularEndRingHom.op).comp
        ((RingEquiv.toOpposite _).toRingHom.comp s)) ≅ Evaluation.sections J O U ⋙
      ModuleCat.restrictScalars ((sectionGlobalEval J O U).comp s) := by
  exact NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (terminal_linear J O s U M)
      (terminal_eval_bijective J O s U hU M))) (by
        intro M N f
        ext g
        rfl)

include hU in
/-- Evaluation at 1 identifies regular-module sections, with any specified scalar
map, with actual terminal evaluation restricted through the evaluated scalar map.
Source: tensor-unit/free-module universal properties
(blueprint: lem-sf-native-terminal-sections-comparison).

Proof: a module morphism from the regular module is determined by its value at 1.
Tensor-unit sections of an abelian sheaf equal its terminal sections by the constant
sheaf adjunction and the free abelian generator. These two bijections compose to
the displayed evaluation map. Evaluation is additive, and precomposition by
multiplication by a global scalar becomes its sectionwise module action. Thus this
bijection is linear for the specified scalar map. Postcomposition proves naturality.
The argument includes zero rings and zero modules. -/
theorem native_terminalSectionsIso :
    Nonempty (coyonedaSections ((Mod.regularEndRingHom.op).comp
        ((RingEquiv.toOpposite _).toRingHom.comp s)) ≅ Evaluation.sections J O U ⋙
      ModuleCat.restrictScalars ((sectionGlobalEval J O U).comp s)) := by
  exact ⟨native_terminalSectionsComparison J O s U hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing

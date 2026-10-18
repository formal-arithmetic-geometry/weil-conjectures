/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! # Canonical coefficient and module size transport

Source: Stacks, Modules on Sites, 03DA and 03EK, using the invariance of
sheaf conditions and balanced tensors under sectionwise isomorphism
(blueprint: def-pur-cochain-coefficient-universe-transport).

All carriers below are explicitly ULift, all restrictions apply the original
restriction to ULift.down, and all scalars act through ULift.down. In particular
this construction does not equate site, ring, or module universes.
-/

@[expose] public section
universe uC vC r m w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CochainUniverseTransport
set_option autoImplicit false
set_option linter.checkUnivs false

/-- Ring-universe transport is the usual sectionwise ULift ring functor.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
def ringFunctor : CommRingCat.{r} ⥤ CommRingCat.{max r m w} where
  obj A := CommRingCat.of (ULift.{max m w} A)
  map f := CommRingCat.ofHom f.hom.ulift

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

/-- Sectionwise ring lifting preserves the sheaf condition.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: matching families lift and descend componentwise through ULift.up/down.
Apply the original unique gluing axiom and lift the resulting section. The ring
operations are transported by the same bijections. -/
@[instance]
theorem ringFunctor_hasSheafCompose : J.HasSheafCompose (ringFunctor.{r, m, w}) := sorry

/-- The genuinely constructed coefficient ring in the common ambient universe.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
abbrev ring (R : Sheaf J CommRingCat.{r}) : Sheaf J CommRingCat.{max r m w} :=
  (sheafCompose J (ringFunctor.{r, m, w})).obj R

/-- Forgetting a lifted commutative ring to a ring preserves sheaves.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: the forgetful functor creates limits, so it preserves the matching-family
limit expressing the sheaf condition. -/
@[instance]
theorem liftedRingForgetHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z}) := sorry

variable (R : Sheaf J CommRingCat.{r})

/-- Original module sheaves, retaining their independent carrier universe m.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
abbrev OriginalModules := ringedSiteModules.{m}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The lifted scalar acts by its down-map on the lifted module carrier.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable instance moduleAction (M : OriginalModules.{uC, vC, r, m} R) (U : Cᵒᵖ) :
    Module ((ring.{uC, vC, r, m, w} R).obj.obj U)
      (ULift.{max r w} (M.val.obj U)) :=
  letI : Module (R.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule
  inferInstanceAs (Module (ULift.{max m w} (R.obj.obj U))
    (ULift.{max r w} (M.val.obj U)))

/-- Lift a local restriction, applying the original map to the descended section.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleMap (M : OriginalModules.{uC, vC, r, m} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U) (ULift.{max r w} (M.val.obj U)) ⟶
      (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).obj
        (ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj V) (ULift.{max r w} (M.val.obj V))) :=
  ModuleCat.ofHom
    (X := ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U)
      (ULift.{max r w} (M.val.obj U)))
    (Y := (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).obj
      (ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj V)
        (ULift.{max r w} (M.val.obj V))))
    { toFun := fun x ↦ ULift.up (M.val.map f x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (M.val.map f).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (M.val.map_smul f a.down x.down) }

/-- Functoriality of lifted restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: evaluate on ULift.up(x), descend, and use the original identity and
composition equations. ULift.up/down are inverse functions. -/
theorem moduleMap_laws (M : OriginalModules.{uC, vC, r, m} R) :
    (∀ U : Cᵒᵖ, moduleMap.{uC, vC, r, m, w} R M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ring.{uC, vC, r, m, w} R).obj ⋙
        forget₂ CommRingCat RingCat).map (𝟙 U)).hom
          (congrArg RingCat.Hom.hom (((ring.{uC, vC, r, m, w} R).obj ⋙
            forget₂ CommRingCat RingCat).map_id U))).inv.app _) ∧
    (∀ {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
      moduleMap.{uC, vC, r, m, w} R M (f ≫ g) = moduleMap.{uC, vC, r, m, w} R M f ≫
        (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).map
          (moduleMap.{uC, vC, r, m, w} R M g) ≫
        (ModuleCat.restrictScalarsComp' ((ring.{uC, vC, r, m, w} R).obj.map f).hom
          ((ring.{uC, vC, r, m, w} R).obj.map g).hom ((ring.{uC, vC, r, m, w} R).obj.map (f ≫
            g)).hom
          (congrArg RingCat.Hom.hom (((ring.{uC, vC, r, m, w} R).obj ⋙
            forget₂ CommRingCat RingCat).map_comp f g))).inv.app _) := sorry

/-- The lifted module presheaf, with explicit ULift carriers and restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def modulePresheaf (M : OriginalModules.{uC, vC, r, m} R) :
    PresheafOfModules.{max r m w}
      (((ring.{uC, vC, r, m, w} R).obj ⋙ forget₂ CommRingCat RingCat)) where
  obj U := ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U) (ULift.{max r w} (M.val.obj U))
  map := moduleMap.{uC, vC, r, m, w} R M
  map_id := (moduleMap_laws.{uC, vC, r, m, w} R M).1
  map_comp := (moduleMap_laws.{uC, vC, r, m, w} R M).2

/-- The explicitly lifted abelian presheaf is a sheaf.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: forget the transported action. The presheaf is the original abelian
presheaf followed by ULift. Unique gluing transports through ULift.up/down. -/
theorem modulePresheaf_isSheaf (M : OriginalModules.{uC, vC, r, m} R) :
    Presheaf.IsSheaf J (modulePresheaf.{uC, vC, r, m, w} R M).presheaf := sorry

/-- The genuinely constructed module sheaf in the common ambient universe.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def module (M : OriginalModules.{uC, vC, r, m} R) :
    ringedSiteModules.{max r m w}
      ((sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj (ring.{uC, vC,
        r, m, w} R)) :=
  ⟨modulePresheaf.{uC, vC, r, m, w} R M, modulePresheaf_isSheaf.{uC, vC, r, m, w} R M⟩

/-- Lift a module homomorphism by its explicit sectionwise ULift formula.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleHomComponent {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N) (U :
  Cᵒᵖ) :
    (module.{uC, vC, r, m, w} R M).val.obj U ⟶ (module.{uC, vC, r, m, w} R N).val.obj U :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up (h.val.app U x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (h.val.app U).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (map_smul (h.val.app U).hom a.down x.down) }

/-- Lifted homomorphisms commute with restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: descend a section and use the original morphism's naturality, then lift. -/
theorem moduleHomComponent_naturality {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (module.{uC, vC, r, m, w} R M).val.map f ≫
        (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).map
          (moduleHomComponent.{uC, vC, r, m, w} R h V) =
      moduleHomComponent.{uC, vC, r, m, w} R h U ≫ (module.{uC, vC, r, m, w} R N).val.map f := sorry

/-- The explicitly lifted morphism of module sheaves.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleHom {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N) :
    module.{uC, vC, r, m, w} R M ⟶ module.{uC, vC, r, m, w} R N :=
  ⟨{ app := moduleHomComponent.{uC, vC, r, m, w} R h, naturality :=
    moduleHomComponent_naturality.{uC, vC, r, m, w} R h }⟩

/-- The sectionwise lift is functorial on module homomorphisms.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: identities and compositions act on ULift.up(x) by the corresponding
original maps. Extensionality of module sheaf maps gives the equations. -/
theorem moduleHom_laws :
    (∀ M : OriginalModules.{uC, vC, r, m} R, moduleHom.{uC, vC, r, m, w} R (𝟙 M) = 𝟙 _) ∧
      (∀ (M N H : OriginalModules.{uC, vC, r, m} R) (f : M ⟶ N) (g : N ⟶ H),
        moduleHom.{uC, vC, r, m, w} R (f ≫ g) = moduleHom.{uC, vC, r, m, w} R f ≫ moduleHom.{uC,
          vC, r, m, w} R g) := sorry

/-- Canonical common-universe embedding; every carrier and every map is explicit.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def functor : OriginalModules.{uC, vC, r, m} R ⥤ ringedSiteModules.{max r m w}
    ((sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj (ring.{uC, vC, r,
      m, w} R)) where
  obj := module.{uC, vC, r, m, w} R
  map := moduleHom.{uC, vC, r, m, w} R
  map_id := (moduleHom_laws.{uC, vC, r, m, w} R).1
  map_comp := (moduleHom_laws.{uC, vC, r, m, w} R).2 _ _ _

/-- Common-universe transport is fully faithful and additive.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: descend and lift all section maps; the same operations preserve addition,
scalar multiplication and naturality. They are inverse on every hom set. -/
theorem functor_fullyFaithful_additive :
    (∀ M N : OriginalModules.{uC, vC, r, m} R,
      Function.Bijective (fun h : M ⟶ N ↦ (functor.{uC, vC, r, m, w} R).map h)) ∧
      (functor.{uC, vC, r, m, w} R).Additive := sorry

/-- Additivity of the constructed embedding permits termwise transport of complexes.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable instance functorAdditive : (functor.{uC, vC, r, m, w} R).Additive :=
  (functor_fullyFaithful_additive.{uC, vC, r, m, w} R).2

/-- Transport preserves the existing tensor, with a uniquely specified pure-tensor formula.
Source: Stacks 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: ULift transports bilinear maps bijectively, sending x tensor y to
ULift.up(x) tensor ULift.up(y). The tensor universal property gives inverse maps;
the matching-family construction of sheafification commutes with this bijection.
Pure tensors and the sheafification universal property give uniqueness. These
normalizations also preserve scalar extension, associators, symmetry, action
unitors, and all coproduct summand maps, so the same transport applies degreewise
to the signed total tensor of arbitrary complexes. -/
theorem tensor_existsUnique
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    ∃! b : (functor.{uC, vC, r, m, w} R).obj ((siteSheafTensorRight N).obj M) ≅
        (functor.{uC, vC, r, m, w} R).obj M ⊗ (functor.{uC, vC, r, m, w} R).obj N,
      ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        b.hom.val.app U (ULift.up (siteSheafTensorTmul M N U x y)) =
          (tensorObjIsoSheafification
            ((functor.{uC, vC, r, m, w} R).obj M)
            ((functor.{uC, vC, r, m, w} R).obj N)).inv.val.app U
              (((PresheafOfModules.sheafificationAdjunction.{max r m w}
                (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj
                  (ring.{uC, vC, r, m, w} R)).obj)).unit.app
                (((functor.{uC, vC, r, m, w} R).obj M).val ⊗
                  ((functor.{uC, vC, r, m, w} R).obj N).val)).app U
                    (ULift.up x ⊗ₜ[(ring.{uC, vC, r, m, w} R).obj.obj U] ULift.up y)) := sorry

/-- The explicit universe lift preserves the small coproducts used in cochain totals.
Source: Stacks 03DA, 03EK and 07A4
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: ULift commutes with the underlying sectionwise coproduct construction;
the module relations are unchanged by up/down. Sheafification commutes with this
transport by its universal property. Hence the coproduct comparison is invertible,
including for the infinite diagonals p+q=n. -/
theorem functor_preservesSmallColimits
    [EssentiallySmall.{m} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}] :
    PreservesColimitsOfSize.{0, 0} (functor.{uC, vC, r, m, w} R) := sorry

end SheafOfModules.CochainUniverseTransport

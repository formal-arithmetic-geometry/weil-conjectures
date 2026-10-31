/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Constant internal modules under the sectionwise equivalence

Source: latest blueprint, sec-proetale-coefficients, sk-prop-sf-open-closed-triangle,
prop-sfb-bounded-constructible-triangulated.proof.md, kernel paragraph, finite discrete case.
(blueprint: lem-sfb-internal-constant-module-sectionwise).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

/-- The existing sheafified constant ring object, with its transported monoid structure.
Source: latest blueprint, kernel paragraph of prop-sfb-bounded-constructible-triangulated;
ring-object construction, clause 2 (blueprint: lem-sfb-internal-constant-module-sectionwise).
-/
abbrev sfbInternalConstantRing : Sheaf J AddCommGrpCat.{max u v} :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).obj (Presheaf.constRingObj.{max u v, v, u} (C := C) B)

/-- The prescribed ring structure is the image of the constant presheaf ring structure.
Source: ring-object construction, clause 2
(blueprint: lem-sfb-internal-constant-module-sectionwise). -/
instance sfbInternalConstantRing_monObj : MonObj (sfbInternalConstantRing.{u, v} J B) :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).monObjObj
    (Presheaf.constRingObj.{max u v, v, u} (C := C) B)

/-- Commutativity is transported by the braided sheafification functor.
Source: ring-object construction, clause 2
(blueprint: lem-sfb-internal-constant-module-sectionwise). -/
instance sfbInternalConstantRing_isCommMonObj : IsCommMonObj (sfbInternalConstantRing.{u, v} J B) :=
  Functor.isCommMonObj_obj (F := presheafToSheaf J AddCommGrpCat.{max u v})
    (M := Presheaf.constRingObj.{max u v, v, u} (C := C) B)

/-- Apply the existing monoidal sheafification to the constant presheaf module object.
Its action is the tensorator followed by sheafification of the constant scalar action.
Source: latest blueprint, kernel paragraph of prop-sfb-bounded-constructible-triangulated
(blueprint: lem-sfb-internal-constant-module-sectionwise). -/
def sfbInternalConstantModule (P : ModuleCat.{max u v} B) :
    Mod (Sheaf J AddCommGrpCat.{max u v}) (sfbInternalConstantRing.{u, v} J B) :=
  ((presheafToSheaf J AddCommGrpCat.{max u v}).mapMod
    (Presheaf.constRingObj.{max u v, v, u} (C := C) B)).obj
      (Presheaf.toMod B ((Functor.const Cᵒᵖ).obj P))

/-- Specialize the recorded section-ring construction using the existing sheafification
existence theorem at the precise coefficient universe. This avoids a successor-universe
instance without changing the site or its coefficients.
Source: the fixed-equivalence clause of the item
(blueprint: lem-sfb-internal-constant-module-sectionwise). -/
abbrev sfbInternalConstantSectionRing : Sheaf J CommRingCat.{max u v} :=
  @InternalAbelianSheafModule.sectionRingSheaf.{max u v, u, v} C inferInstance J
    (inferInstance : UnivLE.{max u v, max u v})
    (sfbSectionAction_hasSheafify.{u, v, max u v} J)
    (sfbSectionAction_isMonoidal.{u, v, max u v} J)
    (sfbInternalConstantRing.{u, v} J B)
    (sfbInternalConstantRing_monObj J B) (sfbInternalConstantRing_isCommMonObj J B)

/-- The recorded fixed equivalence, with its sheafification existence argument supplied
at the actual coefficient universe. This is an application of that equivalence itself.
Source: the fixed-equivalence clause of the item
(blueprint: lem-sfb-internal-constant-module-sectionwise). -/
abbrev sfbInternalConstantSectionEquivalence :
    Mod (Sheaf J AddCommGrpCat.{max u v}) (sfbInternalConstantRing.{u, v} J B) ≌
      SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
          (sfbInternalConstantSectionRing J B)) :=
  @InternalAbelianSheafModule.sectionModuleEquivalence.{max u v, u, v} C inferInstance J
    (inferInstance : UnivLE.{max u v, max u v})
    (sfbSectionAction_hasSheafify.{u, v, max u v} J)
    (sfbSectionAction_isMonoidal.{u, v, max u v} J)
    (sfbInternalConstantRing.{u, v} J B)
    (sfbInternalConstantRing_monObj J B) (sfbInternalConstantRing_isCommMonObj J B)

private def constantSectionMap :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (sfbInternalConstantSectionRing J B).obj where
  app U := ConcreteCategory.ofHom (C := CommRingCat)
    (X := CommRingCat.of B) (Y := (sfbInternalConstantSectionRing J B).obj.obj U)
    { ((toSheafify J (Presheaf.constRingObj (C := C) B)).app U).hom with
      map_one' := by
        have h := IsMonHom.one_hom
          ((sheafificationAdjunction J AddCommGrpCat.{max u v}).unitAlgHom
            (Presheaf.constRingObj (C := C) B))
        have h' := ConcreteCategory.congr_hom (congr_app h U) (ULift.up (1 : ℤ))
        change (toSheafify J (Presheaf.constRingObj (C := C) B)).app U
          ((1 : ℤ) : B) = (1 : (sfbInternalConstantSectionRing J B).obj.obj U) at h'
        change (toSheafify J (Presheaf.constRingObj (C := C) B)).app U (1 : B) = _
        rw [Int.cast_one] at h'
        exact h'
      map_mul' := by
        intro a b
        have h := IsMonHom.mul_hom
          ((sheafificationAdjunction J AddCommGrpCat.{max u v}).unitAlgHom
            (Presheaf.constRingObj (C := C) B))
        exact ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b) }
  naturality U V f := by
    ext b
    exact ConcreteCategory.congr_hom
      ((toSheafify J (Presheaf.constRingObj (C := C) B)).naturality f) b

private instance constantSectionMap_injective :
    Presheaf.IsLocallyInjective J (constantSectionMap J B) where
  equalizerSieve_mem x y h := by
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J (Presheaf.constRingObj (C := C) B)) x y h

private instance constantSectionMap_surjective :
    Presheaf.IsLocallySurjective J (constantSectionMap J B) where
  imageSieve_mem x := by
    exact Presheaf.imageSieve_mem J
      (toSheafify J (Presheaf.constRingObj (C := C) B)) x

private def constantRingLift :
    (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of B) ⟶
      sfbInternalConstantSectionRing J B :=
  ⟨sheafifyLift J (constantSectionMap J B) (sfbInternalConstantSectionRing J B).property⟩

private instance constantRingLift_isIso : IsIso (constantRingLift J B) := by
  rw [← J.W_sheafToPresheaf_map_iff_isIso]
  apply (J.W (A := CommRingCat.{max u v})).of_precomp
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))) _ (J.W_toSheafify _)
  change J.W (toSheafify J _ ≫ sheafifyLift J _ _)
  rw [toSheafify_sheafifyLift]
  exact J.W_of_isLocallyBijective (constantSectionMap J B)

private abbrev constantRingComparison := (asIso (constantRingLift J B)).symm

private theorem constantRingComparison_unit :
    constantSectionMap J B ≫ (constantRingComparison J B).hom.hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) := by
  rw [← toSheafify_sheafifyLift J (constantSectionMap J B)
    (sfbInternalConstantSectionRing J B).property, Category.assoc]
  have h := congrArg (fun f ↦ f.hom) (asIso (constantRingLift J B)).hom_inv_id
  change (constantRingLift J B).hom ≫ (constantRingComparison J B).hom.hom = 𝟙 _ at h
  change _ ≫ (constantRingLift J B).hom ≫ _ = _
  rw [h, Category.comp_id]

private abbrev internalSections (P : ModuleCat.{max u v} B) :=
  (sfbInternalConstantSectionEquivalence J B).functor.obj (sfbInternalConstantModule J B P)

private theorem internalUnit_smul (P : ModuleCat.{max u v} B) (U : Cᵒᵖ) (b : B) (x : P) :
    (constantSectionMap J B).app U b •
      (show (internalSections J B P).val.obj U from (constantModuleHomUnit J B P).app U x) =
        (constantModuleHomUnit J B P).app U (b • x) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{max u v}
  let M := Presheaf.toMod B ((Functor.const Cᵒᵖ).obj P)
  let f := (adj.mapModAdjunction (Presheaf.constRingObj (C := C) B)).unit.app M
  have h := Mod.act_hom f
  rw [show f.hom = toSheafify J M.X from adj.mapModAdjunction_unit_app_hom _ M] at h
  have h' := ConcreteCategory.congr_hom (congr_app h U) (b ⊗ₜ[ℤ] x)
  change (constantModuleHomUnit J B P).app U (b • x) =
    (constantSectionMap J B).app U b •
      (show (internalSections J B P).val.obj U from
        (constantModuleHomUnit J B P).app U x) at h'
  exact h'.symm

private instance constantUnit_surjective (P : ModuleCat.{max u v} B) :
    Presheaf.IsLocallySurjective J (constantModuleHomUnit J B P) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) B).obj P).presheaf))

private abbrev transportedSections (P : ModuleCat.{max u v} B) :=
  (SheafOfModules.pushforward (F := 𝟭 C)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (constantRingComparison J B).hom)).obj ((constantModuleHomFunctor J B).obj P)

private theorem constantUnit_smul (P : ModuleCat.{max u v} B)
    (U : Cᵒᵖ) (b : B) (x : P) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b •
      @id (((constantModuleHomFunctor J B).obj P).val.obj U)
        ((constantModuleHomUnit J B P).app U x) =
      (constantModuleHomUnit J B P).app U (b • x) := by
  let : J.PreservesSheafification
      (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
    GrothendieckTopology.instPreservesSheafification J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      (FD := fun A B : CommRingCat.{max u v} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u v} ↦ A)
      (FE := fun A B : RingCat.{max u v} ↦ A →+* B)
      (CE := fun A : RingCat.{max u v} ↦ A)
  have hf := sheafComposeIso_inv_fac J (forget₂ CommRingCat RingCat)
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))
  have hf' : (constantModuleHomRingIso J B).inv.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U b :=
    congrArg (fun t ↦ t.app U b) hf
  change (constantModuleHomRingIso J B).inv.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b) •
      (show ((siteConstantModuleFunctorGeneral J B).obj P).val.obj U from
        (constantModuleHomUnit J B P).app U x) = _
  rw [hf']
  exact (((PresheafOfModules.sheafificationAdjunction
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)))).unit.app
      ((siteConstantModulePresheafGeneral (C := C) B).obj P)).app U).hom.map_smul b x |>.symm

private def moduleComparison (P : ModuleCat.{max u v} B)
    (hc : ∀ (U : Cᵒᵖ) (b : B) (x : P),
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b •
        @id (((constantModuleHomFunctor J B).obj P).val.obj U)
          ((constantModuleHomUnit J B P).app U x) =
        (constantModuleHomUnit J B P).app U (b • x)) :
    internalSections J B P ≅ transportedSections J B P := by
  let M := internalSections J B P
  let N := transportedSections J B P
  have h : ∀ (U : Cᵒᵖ) (r : (sfbInternalConstantSectionRing J B).obj.obj U)
      (x : M.val.obj U),
      @id (N.val.obj U) (r • x) = r • @id (N.val.obj U) x := by
    intro U r x
    apply N.isSheaf.isSeparated _ _ (J.intersection_covering
      (Presheaf.imageSieve_mem J (constantSectionMap J B) r)
      (Presheaf.imageSieve_mem J (constantModuleHomUnit J B P) x))
    rintro V f ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    change @id (N.val.obj (Opposite.op V)) (M.val.map f.op (r • x)) =
      N.val.map f.op (r • @id (N.val.obj U) x)
    rw [M.val.map_smul, N.val.map_smul]
    change (constantSectionMap J B).app (Opposite.op V) b =
      (sfbInternalConstantSectionRing J B).obj.map f.op r at hb
    change @id (N.val.obj (Opposite.op V))
        ((sfbInternalConstantSectionRing J B).obj.map f.op r • M.val.map f.op x) =
      (sfbInternalConstantSectionRing J B).obj.map f.op r •
        @id (N.val.obj (Opposite.op V)) (M.val.map f.op x)
    change (constantModuleHomUnit J B P).app (Opposite.op V) y = M.val.map f.op x at hy
    rw [← hb, ← hy]
    change (constantSectionMap J B).app (Opposite.op V) b •
        (show M.val.obj (Opposite.op V) from
          (constantModuleHomUnit J B P).app (Opposite.op V) y) =
      (constantRingComparison J B).hom.hom.app (Opposite.op V)
        ((constantSectionMap J B).app (Opposite.op V) b) •
        @id (((constantModuleHomFunctor J B).obj P).val.obj (Opposite.op V))
          ((constantModuleHomUnit J B P).app (Opposite.op V) y)
    rw [internalUnit_smul]
    have hψ := congrArg (fun t ↦ t.app (Opposite.op V) b)
      (constantRingComparison_unit J B)
    change (constantRingComparison J B).hom.hom.app (Opposite.op V)
      ((constantSectionMap J B).app (Opposite.op V) b) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app
        (Opposite.op V) b at hψ
    change (constantModuleHomUnit J B P).app (Opposite.op V) (@SMul.smul B P inferInstance b y) =
      (constantRingComparison J B).hom.hom.app (Opposite.op V)
        ((constantSectionMap J B).app (Opposite.op V) b) •
        @id (((constantModuleHomFunctor J B).obj P).val.obj (Opposite.op V))
          ((constantModuleHomUnit J B P).app (Opposite.op V) y)
    rw [hψ]
    exact (hc (Opposite.op V) b y).symm
  exact
    { hom := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) h⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 N.val.presheaf) (fun U r x ↦ (h U r x).symm)⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }

private def regularComparison :
    (sfbInternalConstantSectionEquivalence J B).functor.obj
      (Mod.regular (sfbInternalConstantRing J B)) ≅
    (SheafOfModules.pushforward (F := 𝟭 C)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (constantRingComparison J B).hom)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of B)))) := by
  let ψ := constantRingComparison J B
  let M := (sfbInternalConstantSectionEquivalence J B).functor.obj
    (Mod.regular (sfbInternalConstantRing J B))
  let N := (SheafOfModules.pushforward (F := 𝟭 C)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map ψ.hom)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of B))))
  let f : M ⟶ N := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight ψ.hom.hom (forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
      forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})) (by
      intro U r x
      change ψ.hom.hom.app U
        ((show (sfbInternalConstantSectionRing J B).obj.obj U from r) *
          (show (sfbInternalConstantSectionRing J B).obj.obj U from x)) =
        ψ.hom.hom.app U r * ψ.hom.hom.app U x
      exact (ψ.hom.hom.app U).hom.map_mul r x)⟩
  let g : N ⟶ M := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight ψ.inv.hom (forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
      forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})) (by
      intro U r x
      change ψ.inv.hom.app U (ψ.hom.hom.app U r *
        (show ((constantSheaf J CommRingCat.{max u v}).obj
          (CommRingCat.of B)).obj.obj U from x)) =
        (show (sfbInternalConstantSectionRing J B).obj.obj U from r) * ψ.inv.hom.app U x
      have hi : ψ.inv.hom.app U (ψ.hom.hom.app U r) = r :=
        ConcreteCategory.congr_hom (C := CommRingCat.{max u v})
          (congr_app (congrArg (fun f ↦ f.hom) ψ.hom_inv_id) U) r
      calc
        _ = ψ.inv.hom.app U (ψ.hom.hom.app U r) * ψ.inv.hom.app U x :=
          (ψ.inv.hom.app U).hom.map_mul _ _
        _ = _ := congrArg (fun t ↦ t * ψ.inv.hom.app U x) hi)⟩
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (C := CommRingCat.{max u v})
          (congr_app (congrArg (fun f ↦ f.hom) ψ.hom_inv_id) U) x
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (C := CommRingCat.{max u v})
          (congr_app (congrArg (fun f ↦ f.hom) ψ.inv_hom_id) U) x }

/-- The fixed equivalence identifies the sheafified constant ring and its regular module,
and every sheafified constant internal module, with their sectionwise constant versions.
The ring comparison is normalized on constant sections. The module comparison is the
identity on every underlying section group; its naturality therefore preserves all
restriction maps. Linearity of the module isomorphism identifies the internal action
with the sectionwise action, whose constant-section formula is displayed at the end.

Source: latest blueprint, kernel paragraph (finite discrete case) of
prop-sfb-bounded-constructible-triangulated.proof.md.
(blueprint: lem-sfb-internal-constant-module-sectionwise).

Proof: (1) The monoidal sheafification unit preserves unit and multiplication. It is
therefore a locally bijective commutative-ring presheaf map to the reconstructed section
ring. Its sheafification is an isomorphism; use its inverse as the normalized comparison.
The underlying additive maps of this isomorphism and its inverse give the regular-module
comparison, with linearity following from multiplicativity.
(2) The module-adjunction unit preserves the internal constant scalar action. The unit of
sectionwise module sheafification is linear over the ring sheafification unit. The canonical
coefficient comparison intertwines that ring unit with the commutative-ring unit, giving
the displayed scalar identity after coefficient transport.
(3) Both module constructions have the same underlying additive sheaf. Every coefficient
and module section is locally a constant section, by local surjectivity of the two units.
Intersect their image covering sieves. On each restriction the identities from (2), and the
normalization from (1), identify the two actions. Sheaf separation gives equality on all
sections. Thus the identity additive map and its inverse are linear and define the required
module isomorphism, preserving every section and restriction map.
-/
theorem sfbInternalConstantModule_sectionwise :
    ∃ ψ : sfbInternalConstantSectionRing J B ≅
        (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of.{max u v} B),
      (∀ (U : Cᵒᵖ) (b : B),
        ψ.hom.hom.app U
            ((toSheafify J (D := AddCommGrpCat.{max u v})
              (Presheaf.constRingObj.{max u v, v, u} (C := C) B)).app U b) =
          (toSheafify J (D := CommRingCat.{max u v})
              ((Functor.const Cᵒᵖ).obj (CommRingCat.of.{max u v} B))).app U b) ∧
      (∃ eR : (sfbInternalConstantSectionEquivalence J B).functor.obj
            (Mod.regular (sfbInternalConstantRing.{u, v} J B)) ≅
          (SheafOfModules.pushforward.{max u v} (F := 𝟭 C)
            ((sheafCompose J
              (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map ψ.hom)).obj
              (SheafOfModules.unit.{v, u, max u v} ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
                ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of.{max u v} B)))),
        ∀ (U : Cᵒᵖ) (x : (sfbInternalConstantRing.{u, v} J B).obj.obj U),
          eR.hom.val.app U x = ψ.hom.hom.app U x) ∧
      (∀ P : ModuleCat.{max u v} B,
        ∃ eP : (sfbInternalConstantSectionEquivalence J B).functor.obj
              (sfbInternalConstantModule.{u, v} J B P) ≅
            (SheafOfModules.pushforward.{max u v} (F := 𝟭 C)
              ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map ψ.hom)).obj
                ((constantModuleHomFunctor J B).obj P),
          (∀ (U : Cᵒᵖ) (x : ((sfbInternalConstantModule.{u, v} J B P).X.obj.obj U)),
            eP.hom.val.app U x = x) ∧
          (∀ (U : Cᵒᵖ) (b : B) (x : P),
            (toSheafify J (D := CommRingCat.{max u v})
              ((Functor.const Cᵒᵖ).obj (CommRingCat.of.{max u v} B))).app U b •
                @id (((constantModuleHomFunctor J B).obj P).val.obj U)
                  ((constantModuleHomUnit J B P).app U x) =
              (constantModuleHomUnit J B P).app U (b • x))) := by
  classical
  refine ⟨constantRingComparison J B, ?_, ?_, ?_⟩
  · intro U b
    exact congrArg (fun t ↦ t.app U b) (constantRingComparison_unit J B)
  · exact ⟨regularComparison J B, by intros; rfl⟩
  · intro P
    exact ⟨moduleComparison J B P (constantUnit_smul J B P),
      (by intros; rfl), constantUnit_smul J B P⟩

end CategoryTheory

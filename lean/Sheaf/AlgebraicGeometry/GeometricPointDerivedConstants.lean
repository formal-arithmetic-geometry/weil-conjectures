/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Sheaf.CategoryTheory.ExactMonoidalEquivalenceDerived

/-!
# Normalized constant and stalk equivalence at a geometric point

Source: Stacks Project, Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-derived-constants).

We encode abelian groups as modules over `ULift ℤ`. Restriction along `ULift.ringEquiv`
and `ModuleCat.forget₂AddCommGroupIsEquivalence` identify these with `AddCommGrpCat`.
The lift only places the fixed ring of integers in the coefficient universe. This retains the
ordinary integer tensor product, including its unbounded derived tensor and Koszul symmetry.
All functors below are specializations of the recorded stalk and constant-sheaf constructions.
The data structure packages the clauses of the theorem, with their canonical normalizations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The constant-sheaf functor at `Spec Ω`, in the integer-module encoding of abelian groups.
Source: Stacks Tags 04JQ, 0F0F (blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointConstants (Ω : Type u) [Field Ω] :=
  constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))

/-- The actual stalk at the identity geometric point, not an arbitrary equivalent functor.
Source: Stacks Tag 04JQ (blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointStalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :=
  ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))

/-- The canonical constant-germ unit. It is inverse to the existing constant-stalk isomorphism,
whose construction is the sheafification unit followed by the germ map.
Source: Stacks Tags 04JQ, 03PT, 040R
(blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointConstantGerm (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    𝟭 (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ≅ geometricPointConstants Ω ⋙ geometricPointStalk Ω :=
  (((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).constantSheafCompSheafFiberIso
    (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).symm

/-- The canonical derived Koszul symmetry for ordinary integer complexes.
Source: Stacks Tags 03EK, 0F0F (blueprint: lem-kun-geometric-point-derived-constants).
This specializes the existing derived braiding; it chooses no additional structure. -/
noncomputable def geometricPointIntegerDerivedSymmetry
    (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding'
    (DerivedCategory.Qh (C := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (HomotopyCategory.quasiIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (.up ℤ)) K L


/-- All clauses of the normalized point equivalence. The underlying functors are fixed;
monoidality of the localization factorizations fixes the derived tensorators on K-flat
representatives. The derived adjunction is the termwise descent of the displayed adjunction.
Source: Stacks Tags 04JQ, 03EK, 010N, 05RU, 06YS, 0DEN, 0F0F
(blueprint: lem-kun-geometric-point-derived-constants). -/
structure GeometricPointDerivedConstantsData (Ω : Type u) [Field Ω] [IsAlgClosed Ω] where
  /-- The stalk is additive. -/
  [stalkAdditive : (geometricPointStalk Ω).Additive]
  /-- Equivalence of the actual stalk functor. -/
  [stalkEquivalence : (geometricPointStalk Ω).IsEquivalence]
  /-- Equivalence of the actual constant-sheaf functor. -/
  [constantEquivalence : (geometricPointConstants Ω).IsEquivalence]
  /-- The adjunction has the specified constant and stalk functors. -/
  adjunction : geometricPointConstants Ω ⊣ geometricPointStalk Ω
  /-- Its unit is the canonical constant-germ map. -/
  unit_eq : adjunction.unit = (geometricPointConstantGerm Ω).hom
  /-- The counit is invertible. -/
  [counitIsIso : IsIso adjunction.counit]
  /-- The counit is the unique map with the prescribed stalk. -/
  counit_unique (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
      (f : (geometricPointConstants Ω).obj ((geometricPointStalk Ω).obj G) ⟶ G) :
    (geometricPointStalk Ω).map f =
      (geometricPointConstantGerm Ω).inv.app ((geometricPointStalk Ω).obj G) ↔
        f = adjunction.counit.app G
  /-- The constant tensor comparison is strong and respects symmetry. -/
  [constantMonoidal : (geometricPointConstants Ω).Braided]
  /-- The unit is monoidal for the canonical stalk tensor comparison. -/
  unit_monoidal : NatTrans.IsMonoidal adjunction.unit
  /-- The specified counit is monoidal. -/
  counit_monoidal : NatTrans.IsMonoidal adjunction.counit
  /-- The derived integer symmetry is fixed by `integer_symmetry_eq`. -/
  [integerDerivedSymmetric :
    SymmetricCategory (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))]
  /-- The sheaf symmetry is uniquely fixed by `constant_symmetry`, since the derived
  constant functor is an equivalence with invertible tensorators. -/
  [sheafDerivedSymmetric : SymmetricCategory (DerivedCategory
    (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))]
  /-- The coefficient symmetry is the existing canonical derived Koszul symmetry. -/
  integer_symmetry_eq
      (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (β_ K L) = geometricPointIntegerDerivedSymmetry K L
  /-- The descended constant functor is strong monoidal for ordinary derived tensor. -/
  [derivedConstantMonoidal : (geometricPointConstants Ω).mapDerivedCategory.Monoidal]
  /-- The descended stalk functor is strong monoidal for ordinary derived tensor. -/
  [derivedStalkMonoidal : (geometricPointStalk Ω).mapDerivedCategory.Monoidal]
  /-- The derived constant tensor comparison is the termwise canonical comparison. -/
  constant_factors_monoidal :
    NatTrans.IsMonoidal (geometricPointConstants Ω).mapDerivedCategoryFactors.hom
  /-- The derived germ tensor comparison is the termwise canonical comparison. -/
  stalk_factors_monoidal :
    NatTrans.IsMonoidal (geometricPointStalk Ω).mapDerivedCategoryFactors.hom
  /-- The constant comparison respects the canonical derived Koszul symmetry. -/
  constant_symmetry
      (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    Functor.LaxMonoidal.μ (geometricPointConstants Ω).mapDerivedCategory K L ≫
        (geometricPointConstants Ω).mapDerivedCategory.map
          (β_ K L).hom =
      (β_ ((geometricPointConstants Ω).mapDerivedCategory.obj K)
        ((geometricPointConstants Ω).mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ (geometricPointConstants Ω).mapDerivedCategory L K
  /-- The germ comparison respects the canonical derived Koszul symmetry. -/
  stalk_symmetry
      (K L : DerivedCategory
        (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    Functor.LaxMonoidal.μ (geometricPointStalk Ω).mapDerivedCategory K L ≫
        (geometricPointStalk Ω).mapDerivedCategory.map
          (β_ K L).hom =
      (β_ ((geometricPointStalk Ω).mapDerivedCategory.obj K)
        ((geometricPointStalk Ω).mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ (geometricPointStalk Ω).mapDerivedCategory L K
  /-- The descended unit is monoidal. -/
  derived_unit_monoidal : NatTrans.IsMonoidal adjunction.mapDerivedCategoryAdjunction.unit
  /-- The descended counit is monoidal. -/
  derived_counit_monoidal : NatTrans.IsMonoidal adjunction.mapDerivedCategoryAdjunction.counit
  /-- The derived adjunction unit is invertible. -/
  [derivedUnitIsIso : IsIso adjunction.mapDerivedCategoryAdjunction.unit]
  /-- The derived adjunction counit is invertible. -/
  [derivedCounitIsIso : IsIso adjunction.mapDerivedCategoryAdjunction.counit]
  /-- Every cohomological lower bound is preserved by the constant functor. -/
  constant_isGE (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (a : ℤ) :
    DerivedCategory.IsGE K a →
      DerivedCategory.IsGE ((geometricPointConstants Ω).mapDerivedCategory.obj K) a
  /-- Every cohomological lower bound is preserved by the stalk functor. -/
  stalk_isGE
      (K : DerivedCategory
        (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
      (a : ℤ) :
    DerivedCategory.IsGE K a →
      DerivedCategory.IsGE ((geometricPointStalk Ω).mapDerivedCategory.obj K) a

section
variable {C A : Type*} [Category C] [Category A] [MonoidalCategory A] [BraidedCategory A]

@[instance_reducible]
private noncomputable def constantFunctorBraided : (Functor.const (C := A) C).Braided where
  toMonoidal := Functor.Monoidal.const C A
  braided M N := by
    apply NatTrans.ext
    funext U
    change 𝟙 _ ≫ (β_ M N).hom = (β_ M N).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

@[instance_reducible]
private noncomputable def constantSheafBraided (J : GrothendieckTopology C)
    [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] :
    (constantSheaf J A).Braided := by
  letI := constantFunctorBraided (C := Cᵒᵖ) (A := A)
  exact inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Braided
end

section ConstantFiber

universe v w vA uA uC

variable {C : Type uC} [Category.{v} C] {J : GrothendieckTopology C}
    (Φ : J.Point.{w}) {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    [HasColimitsOfSize.{w, w} A] [LocallySmall.{w} C]
    [∀ X : A, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
    [∀ X : A, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

private noncomputable def constantPresheafFiberIso :
    Functor.const Cᵒᵖ ⋙ Φ.presheafFiber (A := A) ≅ 𝟭 A :=
  NatIso.ofComponents Φ.presheafFiberConstIso Φ.presheafFiberConstIso_hom_naturality

set_option backward.isDefEq.respectTransparency false in
private theorem constantPresheafFiberIso_monoidal :
    NatTrans.IsMonoidal (constantPresheafFiberIso Φ (A := A)).hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.id_ε, Category.assoc]
    change Functor.LaxMonoidal.ε Φ.presheafFiber ≫
      Φ.presheafFiber.map (𝟙 _) ≫ (Φ.presheafFiberConstIso (𝟙_ A)).hom = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← cancel_epi (Functor.OplaxMonoidal.η Φ.presheafFiber)]
    simp only [Functor.Monoidal.η_ε_assoc, Category.comp_id]
    apply Φ.presheafFiber_hom_ext
    intro X x
    erw [Φ.toPresheafFiber_presheafFiberConstIso_hom]
  tensor M N := by
    simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.id_μ,
      Category.comp_id]
    rw [← cancel_epi (Functor.OplaxMonoidal.δ Φ.presheafFiber _ _)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc]
    apply Φ.presheafFiber_hom_ext
    intro X x
    simp only [constantPresheafFiberIso, NatIso.ofComponents_hom_app,
      Φ.toPresheafFiber_naturality_assoc, Φ.toPresheafFiber_δ_assoc]
    change (𝟙 (M ⊗ N)) ≫ Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj (M ⊗ N)) ≫
        (Φ.presheafFiberConstIso (M ⊗ N)).hom =
      (Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj M) ⊗ₘ
        Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj N)) ≫
          ((Φ.presheafFiberConstIso M).hom ⊗ₘ (Φ.presheafFiberConstIso N).hom)
    erw [Category.id_comp, Φ.toPresheafFiber_presheafFiberConstIso_hom,
      tensorHom_comp_tensorHom,
      Φ.toPresheafFiber_presheafFiberConstIso_hom,
      Φ.toPresheafFiber_presheafFiberConstIso_hom, tensorHom_id, id_whiskerRight]
    rfl


attribute [local instance] Sheaf.monoidalCategory

variable [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasProducts.{w} A]
  {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)]

set_option backward.isDefEq.respectTransparency false in
private theorem constantSheafFiberIso_monoidal :
    NatTrans.IsMonoidal (Φ.constantSheafCompSheafFiberIso J A).hom := by
  have := constantPresheafFiberIso_monoidal Φ (A := A)
  let e : constantSheaf J A ⋙ Φ.sheafFiber ≅ 𝟭 A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (Φ.presheafToSheafCompSheafFiberIso A) ≪≫
        constantPresheafFiberIso Φ
  have he : e = Φ.constantSheafCompSheafFiberIso J A := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change 𝟙 _ ≫ (Φ.presheafToSheafCompSheafFiberIso A).hom.app _ ≫
      (Φ.presheafFiberConstIso M).hom = _
    simp only [Category.id_comp]
    rfl
  rw [← he]
  dsimp only [e, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

end ConstantFiber

section
universe v uSym
variable {C : Type uSym} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]

private local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
private theorem cochain_symmetry (K L : CochainComplex C ℤ) :
    (β_ K L).hom ≫ (β_ L K).hom = 𝟙 _ := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_braiding_hom_assoc,
    Preadditive.zsmul_comp, Category.assoc,
    CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.comp_zsmul, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, smul_smul, mul_comm p q]
  simp only [curriedTensor_obj_obj, Int.units_coe_mul_self, one_smul,
    HomologicalComplex.id_f]
  erw [Category.comp_id]

@[instance_reducible]
private noncomputable def homotopySymmetric :
    SymmetricCategory (HomotopyCategory C (.up ℤ)) where
  symmetry X Y := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    exact ((HomotopyCategory.quotient C (.up ℤ)).map_comp _ _).symm.trans
      (((HomotopyCategory.quotient C (.up ℤ)).congr_map (cochain_symmetry X Y)).trans
        ((HomotopyCategory.quotient C (.up ℤ)).map_id _))

section
variable {E D : Type*} [Category E] [Category D] [MonoidalCategory E]
  [SymmetricCategory E] (L : E ⥤ D) (W : MorphismProperty E)
  [L.IsLocalization W] [W.ContainsIdentities] [L.HasDerivedMonoidalCategory W]

private theorem derived_braiding_symmetry (X Y : DerivedMonoidal L W) :
    (DerivedMonoidal.braiding' L W X Y).hom ≫
      (DerivedMonoidal.braiding' L W Y X).hom = 𝟙 _ := by
  have h : DerivedMonoidal.braidingCounit L W = DerivedMonoidal.braidingInvCounit L W := by
    ext U V
    change ((DerivedMonoidal.counit L W).app V).app U ≫
        (toDerivedMonoidal L W).map (β_ V U).hom =
      ((DerivedMonoidal.counit L W).app V).app U ≫
        (toDerivedMonoidal L W).map (β_ U V).inv
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  have h' : DerivedMonoidal.braidingNatTrans L W =
      DerivedMonoidal.braidingInvNatTrans L W :=
    congrArg ((DerivedMonoidal.bifunctor L W).leftDerived₂Lift
      (DerivedMonoidal.counit L W) W W _) h
  change ((DerivedMonoidal.braidingNatTrans L W).app Y).app X ≫
    ((DerivedMonoidal.braidingNatTrans L W).app X).app Y = 𝟙 _
  nth_rw 1 [h']
  exact (DerivedMonoidal.braiding' L W Y X).inv_hom_id
end

@[instance_reducible]
private noncomputable def derivedSymmetric : SymmetricCategory (DerivedCategory C) := by
  letI := homotopySymmetric (C := C)
  exact { DerivedCategory.braidedCategory' C with
    symmetry := derived_braiding_symmetry (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) }

private theorem derivedSymmetric_braiding (K L : DerivedCategory C) :
    letI := derivedSymmetric (C := C)
    (β_ K L) = DerivedMonoidal.braiding' (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) K L := rfl

end

section
open CategoryTheory.Category Functor.LaxMonoidal Functor.OplaxMonoidal
variable {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Monoidal] [G.LaxMonoidal] (adj : F ⊣ G)
  [NatTrans.IsMonoidal adj.unit]

private theorem adjunction_monoidal_of_unit : adj.IsMonoidal where
  leftAdjoint_ε := by
    have h := NatTrans.IsMonoidal.unit (τ := adj.unit)
    simp only [Functor.LaxMonoidal.id_ε, Functor.LaxMonoidal.comp_ε, id_comp] at h
    rw [h, assoc, ← G.map_comp, Functor.Monoidal.ε_η, CategoryTheory.Functor.map_id,
      comp_id]
  leftAdjoint_μ X Y := by
    have h := NatTrans.IsMonoidal.tensor (τ := adj.unit) (G.obj X) (G.obj Y)
    simp only [Functor.LaxMonoidal.id_μ, Functor.LaxMonoidal.comp_μ, id_comp] at h
    rw [h, assoc, assoc, ← G.map_comp, Functor.Monoidal.μ_δ_assoc]
    rw [← Functor.LaxMonoidal.μ_natural, ← assoc, tensorHom_comp_tensorHom]
    simp only [adj.right_triangle_components]
    erw [tensorHom_id, id_whiskerRight, id_comp]
    rfl

end

open Functor.LaxMonoidal

section
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] [SymmetricCategory D] (G : C ⥤ D) [G.Monoidal] [G.Full] [G.Faithful]
private theorem pullback_braided (X Y : C) :
    letI := SymmetricCategory.ofFullyFaithful G
    μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X := by
  change μ G X Y ≫ G.map (G.preimage
    ((Functor.Monoidal.μIso G X Y).inv ≫ (β_ (G.obj X) (G.obj Y)).hom ≫
      (Functor.Monoidal.μIso G Y X).hom)) = _
  rw [G.map_preimage]
  change (Functor.Monoidal.μIso G X Y).hom ≫
    ((Functor.Monoidal.μIso G X Y).inv ≫ _ ≫ _) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

end
section
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
  (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.Braided] [G.Faithful]
  (i : 𝟭 C ≅ F ⋙ G) (hi : NatTrans.IsMonoidal i.hom)
include G i hi in
private theorem inverse_braided (X Y : C) :
    μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  have := hi
  let : (F ⋙ G).LaxBraided := Functor.LaxBraided.ofNatIso i
  apply G.map_injective
  apply (cancel_epi (μ G (F.obj X) (F.obj Y))).1
  simp only [Functor.map_comp, ← Category.assoc]
  have h := Functor.LaxBraided.braided (F := F ⋙ G) X Y
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Category.assoc] at h
  rw [Category.assoc, h]
  rw [Functor.LaxBraided.braided, Category.assoc]
  rfl
end

/-- Source: Stacks Tags 04JQ and 0F0F.
(blueprint: lem-kun-geometric-point-derived-constants).

The constant sheaf equivalence and canonical germ isomorphism identify the actual stalk
with its inverse. Full faithfulness constructs the uniquely normalized counit, and naturality
proves the triangle identities. The germ comparison is monoidal on constant sections, so the
adjunction is monoidal. Apply coherent K-flat descent for exact monoidal equivalences, with
its canonical localization factors. The symmetric Koszul braiding on integer complexes
passes to the derived category; transfer it along the fully faithful derived stalk. The
monoidal unit identifies the composite with the identity, proving constant symmetry as well.
Finally exact functors preserve every cohomological lower bound. -/
theorem nonempty_geometricPointDerivedConstantsData (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Nonempty (GeometricPointDerivedConstantsData Ω) := by
  let : (geometricPointStalk Ω).Additive :=
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber_additive
  let : (geometricPointConstants Ω).IsEquivalence := inferInstance
  let e := (geometricPointConstants Ω).asEquivalence
  let i : geometricPointStalk Ω ≅ e.inverse :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.inverse (geometricPointConstantGerm Ω).symm ≪≫
      Functor.rightUnitor _
  let : (geometricPointStalk Ω).IsEquivalence :=
    Functor.isEquivalence_of_iso i.symm
  let adj : geometricPointConstants Ω ⊣ geometricPointStalk Ω :=
    Adjunction.mkOfUnitCounit
      { unit := (geometricPointConstantGerm Ω).hom
        counit :=
          { app := fun G ↦ (geometricPointStalk Ω).preimage
              ((geometricPointConstantGerm Ω).inv.app ((geometricPointStalk Ω).obj G))
            naturality := by
              intro G H f
              apply (geometricPointStalk Ω).map_injective
              simp only [Functor.map_comp, Functor.map_preimage]
              exact (geometricPointConstantGerm Ω).inv.naturality
                ((geometricPointStalk Ω).map f) }
        left_triangle := by
          apply NatTrans.ext
          funext N
          apply (geometricPointStalk Ω).map_injective
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.whiskerRight_app, Functor.map_comp, Functor.map_preimage,
            Functor.associator_hom_app, Category.id_comp]
          change (geometricPointStalk Ω).map
              ((geometricPointConstants Ω).map ((geometricPointConstantGerm Ω).hom.app N)) ≫
                (geometricPointConstantGerm Ω).inv.app
                  ((geometricPointStalk Ω).obj ((geometricPointConstants Ω).obj N)) =
            (geometricPointStalk Ω).map (𝟙 _)
          have h := (geometricPointConstantGerm Ω).hom.naturality
            ((geometricPointConstantGerm Ω).hom.app N)
          simp only [Functor.id_map, Functor.comp_map] at h
          have h' := (cancel_epi ((geometricPointConstantGerm Ω).hom.app N)).1 h
          rw [← h']
          exact ((geometricPointConstantGerm Ω).hom_inv_id_app _).trans
            ((geometricPointStalk Ω).map_id _).symm
        right_triangle := by
          apply NatTrans.ext
          funext G
          simp }
  have hu : adj.unit = (geometricPointConstantGerm Ω).hom := rfl
  have : IsIso adj.unit := by rw [hu]; infer_instance
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let : (geometricPointConstants Ω).Braided := constantSheafBraided _
  have hg : NatTrans.IsMonoidal (geometricPointConstantGerm Ω).symm.hom :=
    constantSheafFiberIso_monoidal _
  have hm : NatTrans.IsMonoidal adj.unit := by
    rw [hu]
    exact inferInstanceAs (NatTrans.IsMonoidal (geometricPointConstantGerm Ω).symm.inv)
  have ha : adj.IsMonoidal := adjunction_monoidal_of_unit adj
  have hc : NatTrans.IsMonoidal adj.counit := inferInstance
  obtain ⟨d⟩ := ExactMonoidalEquivalenceDerived.nonempty_data adj
  let : (geometricPointConstants Ω).mapDerivedCategory.Monoidal := d.leftMonoidal
  let : (geometricPointStalk Ω).mapDerivedCategory.Monoidal := d.rightMonoidal
  let : SymmetricCategory (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
    derivedSymmetric
  let : SymmetricCategory (DerivedCategory
      (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :=
    SymmetricCategory.ofFullyFaithful (geometricPointStalk Ω).mapDerivedCategory
  let : (geometricPointStalk Ω).mapDerivedCategory.Braided :=
    { braided := pullback_braided (geometricPointStalk Ω).mapDerivedCategory }
  have hdu := d.unit
  refine ⟨{
    stalkAdditive := inferInstance
    stalkEquivalence := inferInstance
    constantEquivalence := inferInstance
    adjunction := adj
    unit_eq := hu
    counitIsIso := inferInstance
    counit_unique := ?_
    constantMonoidal := inferInstance
    unit_monoidal := hm
    counit_monoidal := hc
    integerDerivedSymmetric := inferInstance
    sheafDerivedSymmetric := inferInstance
    integer_symmetry_eq := derivedSymmetric_braiding
    derivedConstantMonoidal := inferInstance
    derivedStalkMonoidal := inferInstance
    constant_factors_monoidal := d.leftFactors
    stalk_factors_monoidal := d.rightFactors
    constant_symmetry := inverse_braided _ _ (asIso adj.mapDerivedCategoryAdjunction.unit)
      d.unit
    stalk_symmetry := Functor.LaxBraided.braided
    derived_unit_monoidal := d.unit
    derived_counit_monoidal := d.counit
    derivedUnitIsIso := inferInstance
    derivedCounitIsIso := inferInstance
    constant_isGE := fun K a h ↦ by
      have := h
      exact (geometricPointConstants Ω).isGE_mapDerivedCategory_obj K a
    stalk_isGE := fun K a h ↦ by
      have := h
      exact (geometricPointStalk Ω).isGE_mapDerivedCategory_obj K a }⟩
  · intro G f
    have he : (geometricPointStalk Ω).map (adj.counit.app G) =
        (geometricPointConstantGerm Ω).inv.app ((geometricPointStalk Ω).obj G) := by
      rw [← cancel_epi ((geometricPointConstantGerm Ω).hom.app _)]
      change adj.unit.app _ ≫ _ = _
      rw [adj.right_triangle_components, Iso.hom_inv_id_app]
      rfl
    rw [← he]
    constructor
    · intro h
      exact (geometricPointStalk Ω).map_injective h
    · rintro rfl
      rfl


end AlgebraicGeometry.Etale

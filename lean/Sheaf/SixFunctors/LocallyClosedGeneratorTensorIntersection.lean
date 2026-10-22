/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

import all WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Sheaf.AlgebraicGeometry.ProEtaleSupportedReconstruction
import all Sheaf.Paper.FiniteEtaleLocallyFreeModels
import all Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

import Sheaf.Paper.CondensedFiniteFreeTensorExact
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates

/-! # Tensor of locally closed lisse generators

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field/
sk-thm-sf-pf-field-tensor.proof.md,
Proof (1) (blueprint: lem-sfb-locally-closed-generator-tensor-intersection).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Both orders of open/closed factorization, using Mathlib's factorization data without a new
factorization notion. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
abbrev GeneratorFactorization {S X : Scheme.{u}} (a : S ⟶ X) :=
  MorphismProperty.MapFactorizationData @IsClosedImmersion @IsOpenImmersion a ⊕
    MorphismProperty.MapFactorizationData @IsOpenImmersion @IsClosedImmersion a

/-- The actual module extension `j_! i_*`, or `i_* j_!`, for the given factorization.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p

/-- Restriction normalization: inverse open unit and closed counit in factorization order,
with the canonical inverse-image composition. Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) :
    generatorExtension Λ A ⋙ upperStar Λ a ⟶ 𝟭 _ :=
  match A with
  | .inl A =>
    letI : IsOpenImmersion A.p := A.hp
    (Functor.associator (lowerStar Λ A.i) (openImmersionLowerShriek Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (lowerStar Λ A.i)
        (Functor.whiskerLeft (openImmersionLowerShriek Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.p).unit).inv
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (upperStarLowerStarAdjunction Λ A.i).counit
  | .inr A =>
    letI : IsOpenImmersion A.i := A.hi
    (Functor.associator (openImmersionLowerShriek Λ A.i) (lowerStar Λ A.p)
      (upperStar Λ a)).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek Λ A.i)
        (Functor.whiskerLeft (lowerStar Λ A.p)
          ((eqToIso (congrArg (upperStar Λ) A.fac.symm) ≪≫
            upperStarComp Λ A.i A.p).hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (upperStarLowerStarAdjunction Λ A.p).counit
            (upperStar Λ A.i) ≫
          (Functor.leftUnitor _).hom) ≫
      (asIso (openImmersionLowerShriekUpperStarAdjunction Λ A.i).unit).inv

/-- Source bifunctor on the full categories of lisse modules, in degree zero.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorSource
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} {a : S ⟶ X} {b : T ⟶ X}
    (A : GeneratorFactorization a) (B : GeneratorFactorization b) :=
  (((Functor.whiskeringLeft₂ _).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S))) ⋙
      generatorExtension Λ A ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T))) ⋙
      generatorExtension Λ B ⋙ DerivedCategory.singleFunctor _ 0)).obj (derivedTensor Λ X)

/-- Ordinary relative tensor after the two actual fibre-product projections.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorIntersectionModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X) :=
  (((Functor.whiskeringLeft₂ _).obj (upperStar Λ (pullback.fst a b))).obj
    (upperStar Λ (pullback.snd a b))).obj (MonoidalCategory.curriedTensor _)

/-- Target bifunctor: extend the underived relative tensor from the actual fibre product.
Source: blueprint tensor proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection). -/
noncomputable def generatorTensorTarget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}} (a : S ⟶ X) (b : T ⟶ X)
    (C : GeneratorFactorization (pullback.fst a b ≫ a)) :=
  (Functor.postcompose₂.obj (generatorExtension Λ C ⋙ DerivedCategory.singleFunctor _ 0)).obj
    ((((Functor.whiskeringLeft₂ _).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj
      (generatorIntersectionModule Λ a b))

section GeneratorTensorProof

private theorem generatorExtension_inl_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S V X : Scheme.{u}} {a : S ⟶ X}
    (i : S ⟶ V) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hc : i ≫ j = a) :
    generatorExtension Λ (.inl ⟨V, i, j, hc, inferInstance, inferInstance⟩) =
      lowerStar Λ i ⋙ openImmersionLowerShriek Λ j := rfl

section FiniteFreeTensor
universe uBip vBip
variable {C : Type uBip} [Category.{vBip} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

private noncomputable def finiteUnitBiproductTensorIso (m n : ℕ) :
    (⨁ fun _ : Fin m ↦ 𝟙_ C) ⊗ (⨁ fun _ : Fin n ↦ 𝟙_ C) ≅
      ⨁ fun _ : Fin (m * n) ↦ 𝟙_ C := by
  classical
  open MonoidalCategory in
    exact rightDistributor _ _ ≪≫
      biproduct.mapIso (fun _ ↦ leftDistributor _ _ ≪≫
        biproduct.mapIso (fun _ ↦ λ_ _)) ≪≫
      biproductBiproductIso (fun _ : Fin m ↦ Fin n) (fun _ _ ↦ 𝟙_ _) ≪≫
      biproduct.whiskerEquiv
        (f := fun _ : Σ _ : Fin m, Fin n ↦ 𝟙_ _)
        (g := fun _ : Fin (m * n) ↦ 𝟙_ _)
        ((Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv)
        (fun _ ↦ Iso.refl _)

end FiniteFreeTensor

private noncomputable def finiteFreeTensorIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (m n : ℕ) :
    MonoidalCategory.tensorObj (Mod.finiteFree (condensedRingObj Λ X) m)
      (Mod.finiteFree (condensedRingObj Λ X) n) ≅
      Mod.finiteFree (condensedRingObj Λ X) (m * n) := by
  exact finiteUnitBiproductTensorIso m n

attribute [local irreducible] upperStar upperStarComp upperStarCongr
  Mod.monoidalCategoryStruct

private theorem commonCoverProperty
    {W : Scheme.{u}}
    (P Q : ∀ Y : Scheme.{u}, (Y ⟶ W) → Prop)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage W, ∀ k, P (U.X k) (U.f k))
    (hQ : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage W, ∀ k, Q (U.X k) (U.f k))
    (rP : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ W) (f : Z ⟶ Y), P Y g → P Z (f ≫ g))
    (rQ : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ W) (f : Z ⟶ Y), Q Y g → Q Z (f ≫ g)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage W,
      ∀ k, P (U.X k) (U.f k) ∧ Q (U.X k) (U.f k) := by
  obtain ⟨C, hC⟩ := hP
  obtain ⟨D, hD⟩ := hQ
  let U := C.bind (fun k ↦ D.pullback₁ (C.f k))
  refine ⟨U, ?_⟩
  rintro ⟨i, j⟩
  constructor
  · exact rP (C.f i) (pullback.fst (C.f i) (D.f j)) (hC i)
  · change Q _ (pullback.fst (C.f i) (D.f j) ≫ C.f i)
    rw [pullback.condition]
    exact rQ (D.f j) (pullback.snd (C.f i) (D.f j)) (hD j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_commonCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W : Scheme.{u}}
    (P Q : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hP : IsLisseCoefficientModule Λ P) (hQ : IsLisseCoefficientModule Λ Q) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage W,
      ∀ k, Mod.IsFree (condensedRingObj Λ (U.X k)) ((upperStar Λ (U.f k)).obj P) ∧
        Mod.IsFree (condensedRingObj Λ (U.X k)) ((upperStar Λ (U.f k)).obj Q) := by
  exact commonCoverProperty
    (fun Y f ↦ Mod.IsFree (condensedRingObj Λ Y) ((upperStar Λ f).obj P))
    (fun Y f ↦ Mod.IsFree (condensedRingObj Λ Y) ((upperStar Λ f).obj Q))
    hP hQ (fun g f ↦ free_standard_refine Λ g f P)
    (fun g f ↦ free_standard_refine Λ g f Q)

private theorem intersection_commonCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S T : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
    (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (pullback a b),
      ∃ m n : U.I₀ → ℕ, ∀ k : U.I₀,
        Nonempty ((upperStar Λ (U.f k ≫ pullback.fst a b)).obj L.obj ≅
          Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k)) ∧
        Nonempty ((upperStar Λ (U.f k ≫ pullback.snd a b)).obj M.obj ≅
          Mod.finiteFree (condensedRingObj Λ (U.X k)) (n k)) ∧
        Nonempty ((upperStar Λ (U.f k)).obj
          (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj) ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k * n k)) := by
  classical
  obtain ⟨U, hU⟩ := normalized_commonCover Λ
    ((upperStar Λ (pullback.fst a b)).obj L.obj)
    ((upperStar Λ (pullback.snd a b)).obj M.obj)
    (locFree_pullback Λ (pullback.fst a b) L.obj L.property)
    (locFree_pullback Λ (pullback.snd a b) M.obj M.property)
  choose m hm using fun k ↦ (hU k).1
  choose n hn using fun k ↦ (hU k).2
  refine ⟨U, m, n, fun k ↦ ⟨?_, ?_, ?_⟩⟩
  · exact ⟨(upperStarComp Λ (U.f k) (pullback.fst a b)).app L.obj ≪≫ (hm k).some⟩
  · exact ⟨(upperStarComp Λ (U.f k) (pullback.snd a b)).app M.obj ≪≫ (hn k).some⟩
  · exact ⟨(Functor.Monoidal.μIso (upperStar Λ (U.f k)) _ _).symm ≪≫
      MonoidalCategory.tensorIso (hm k).some (hn k).some ≪≫
      finiteFreeTensorIso Λ (U.X k) (m k) (n k)⟩

private theorem immersion_noetherian {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] (a : S ⟶ X) [IsImmersion a] :
    IsLocallyNoetherian S ∧ CompactSpace S := by
  let : IsNoetherian X := ⟨⟩
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian a, inferInstance⟩

attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorRestriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : IsIso (generatorRestriction Λ A) := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    let : IsClosedImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.i (ProEtale.abelian_closed_counit A.i)
    dsimp only [generatorRestriction]
    infer_instance
  · let : IsClosedImmersion A.p := A.hp
    let : IsOpenImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.p (ProEtale.abelian_closed_counit A.p)
    dsimp only [generatorRestriction]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedPullback_zero_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X)
    (hg : Disjoint (Set.range g) (Set.range i))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ g).obj ((lowerStar Λ i).obj M)) := by
  let V := Scheme.openComplementOfIsClosedImmersion i
  have hV : Set.range V.ι = (Set.range i)ᶜ := by
    simp [V, Scheme.openComplementOfIsClosedImmersion]
  have h := openRestrictionPushforwardZero Λ i V.ι hV M
  have hgV : Set.range g ⊆ Set.range V.ι := by
    rw [hV]
    exact hg.subset_compl_right
  let f := IsOpenImmersion.lift V.ι g hgV
  have hf : f ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ hgV
  exact ((upperStar Λ f).map_isZero h).of_iso
    ((upperStarCongr Λ hf.symm).app _ ≪≫ (upperStarComp Λ f V.ι).app _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedOpenExtension_zero_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S V X Y : Scheme.{u}}
    (i : S ⟶ V) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ X) (hg : Disjoint (Set.range g) (Set.range (i ≫ j)))
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    IsZero ((upperStar Λ g).obj
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P))) := by
  have hdis : Disjoint (Set.range (pullback.snd g j)) (Set.range i) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp hg
      (show j (pullback.snd g j y) ∈ Set.range g from
        ⟨pullback.fst g j y, by
          exact congrArg (fun f : pullback g j ⟶ X ↦ f y) pullback.condition⟩)
    exact ⟨z, congrArg j hz⟩
  have hz := closedPullback_zero_of_disjoint Λ i (pullback.snd g j) hdis P
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} (pullback.snd g j)).obj
      ((lowerStar Λ i).obj P).X) :=
    ((Mod.forget _).map_isZero hz).of_iso
      (upperStarObjXIso Λ (pullback.snd g j) _).symm
  have e := (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
    (IsPullback.of_hasPullback g j).flip).app ((lowerStar Λ i).obj P).X
  apply isZero_of_isZero_X Λ
  exact ((ProEtale.openImmersionLowerShriek Ab.{u + 1} (pullback.fst g j)).map_isZero
    hz').of_iso (upperStarObjXIso Λ g _ ≪≫ e.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedBaseChange_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (h : IsZero ((upperStar Λ (pullback.snd g i)).obj P)) :
    IsZero ((upperStar Λ g).obj ((lowerStar Λ i).obj P)) := by
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hU : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  obtain ⟨hu, hz, delta, gamma, hd, hg, alpha, beta, ha, hb⟩ :=
    ProEtale.ringSheaf_baseChange_mates i U.ι hU (condensedRingObj Λ X) g
  let := hu
  let := hz
  let P' := (Mod.comap (condensedPullbackHom Λ i)).obj P
  have e := (Mod.forget _).mapIso (beta.app P')
  have h' : IsZero ((ProEtale.upperStar Ab.{u + 1} (pullback.snd g i)).obj P.X) :=
    ((Mod.forget _).map_isZero h).of_iso
      (upperStarObjXIso Λ (pullback.snd g i) P).symm
  apply isZero_of_isZero_X Λ
  exact ((ProEtale.lowerStar Ab.{u + 1} (pullback.fst g i)).map_isZero h').of_iso
    (upperStarObjXIso Λ g _ ≪≫ e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {a : S ⟶ X} (A : GeneratorFactorization a) (g : Y ⟶ X)
    (hg : Disjoint (Set.range g) (Set.range a))
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    IsZero ((upperStar Λ g).obj ((generatorExtension Λ A).obj P)) := by
  rcases A with A | A
  · let : IsClosedImmersion A.i := A.hi
    let : IsOpenImmersion A.p := A.hp
    have hgp : Disjoint (Set.range g) (Set.range (A.i ≫ A.p)) := by
      rw [A.fac]
      exact hg
    exact closedOpenExtension_zero_of_disjoint Λ A.i A.p g hgp P
  · let : IsClosedImmersion A.p := A.hp
    let : IsOpenImmersion A.i := A.hi
    apply closedBaseChange_zero Λ A.p g
    apply isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ A.i
    rw [disjoint_comm, Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp hg
      (show A.p (pullback.snd g A.p y) ∈ Set.range g from
        ⟨pullback.fst g A.p y, by
          exact congrArg (fun f : pullback g A.p ⟶ X ↦ f y) pullback.condition⟩)
    refine ⟨z, ?_⟩
    have hf := congrArg (fun f : S ⟶ X ↦ f z) A.fac
    exact hf.symm.trans (congrArg A.p hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleOpenSupportedCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hij : Set.range j = (Set.range i)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsZero ((upperStar Λ i).obj N)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) := by
  have hzero : IsZero ((ProEtale.upperStar Ab.{u + 1} i).obj N.X) :=
    ((Mod.forget _).map_isZero hi).of_iso (upperStarObjXIso Λ i N).symm
  have hc := ProEtale.abelian_open_supported_counit i j hij N.X hzero
  apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
  apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j
  exact (Adjunction.isIso_counit_app_iff_mem_essImage _).1 hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleClosedSupportedUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hij : Set.range j = (Set.range i)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hj : IsZero ((upperStar Λ j).obj N)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app N) := by
  have hzero : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) :=
    ((Mod.forget _).map_isZero hj).of_iso (upperStarObjXIso Λ j N).symm
  exact moduleUnitOfAbelian Λ i N ((ProEtale.abelian_closed_support i j hij).2 N.X hzero)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem intersection_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S T : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
    (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))) :
    IsLisseCoefficientModule Λ (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj) := by
  obtain ⟨U, m, n, h⟩ := intersection_commonCover Λ a b L M
  exact ⟨U, fun k ↦ ⟨m k * n k, (h k).2.2⟩⟩

private instance generatorExtension_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : (generatorExtension Λ A).Additive := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    dsimp only [generatorExtension]
    infer_instance
  · let : IsOpenImmersion A.i := A.hi
    dsimp only [generatorExtension]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def generatorExtension_fullyFaithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} {a : S ⟶ X}
    (A : GeneratorFactorization a) : (generatorExtension Λ A).FullyFaithful := by
  rcases A with A | A
  · let : IsOpenImmersion A.p := A.hp
    let : IsClosedImmersion A.i := A.hi
    have := moduleCounitOfAbelian Λ A.i (ProEtale.abelian_closed_counit A.i)
    change (lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p).FullyFaithful
    exact (upperStarLowerStarAdjunction Λ A.i).fullyFaithfulROfIsIsoCounit.comp
      (fullyFaithfulOpenImmersionLowerShriek Λ A.p)
  · let : IsOpenImmersion A.i := A.hi
    let : IsClosedImmersion A.p := A.hp
    have := moduleCounitOfAbelian Λ A.p (ProEtale.abelian_closed_counit A.p)
    change (openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p).FullyFaithful
    exact (fullyFaithfulOpenImmersionLowerShriek Λ A.i).comp
      (upperStarLowerStarAdjunction Λ A.p).fullyFaithfulROfIsIsoCounit

universe uC uD vC vD₀

private theorem faithful_restriction_on_image
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD₀} D]
    (E : C ⥤ D) (R : D ⥤ C) (ff : E.FullyFaithful) (η : E ⋙ R ≅ 𝟭 C)
    (P Q : C) {f g : E.obj P ⟶ E.obj Q} (h : R.map f = R.map g) : f = g := by
  have he (k : E.obj P ⟶ E.obj Q) :
      R.map k = η.hom.app P ≫ ff.preimage k ≫ η.inv.app Q := by
    have hn := η.hom.naturality (ff.preimage k)
    dsimp at hn
    rw [ff.map_preimage] at hn
    apply (cancel_mono (η.hom.app Q)).1
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.id_obj] using hn
  have hpre : ff.preimage f = ff.preimage g := by
    rw [he f, he g] at h
    exact (cancel_mono (η.inv.app Q)).1 ((cancel_epi (η.hom.app P)).1 h)
  simpa only [ff.map_preimage] using congrArg E.map hpre

private theorem normalized_comparison_of_essImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD₀} D]
    (E : C ⥤ D) (R : D ⥤ C) (_ff : E.FullyFaithful) (η : E ⋙ R ≅ 𝟭 C)
    (N : D) (P : C) (hN : ∃ Q, Nonempty (N ≅ E.obj Q))
    (σ : R.obj N ≅ P) :
    ∃ e : N ≅ E.obj P, R.map e.hom ≫ η.hom.app P = σ.hom := by
  obtain ⟨Q, ⟨eQ⟩⟩ := hN
  let d : Q ≅ P := (η.app Q).symm ≪≫ (R.mapIso eQ).symm ≪≫ σ
  refine ⟨eQ ≪≫ E.mapIso d, ?_⟩
  have hn := η.hom.naturality d.hom
  dsimp at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv]
  simp only [← Category.assoc, Iso.hom_inv_id_app,
    ← R.map_comp, Iso.hom_inv_id, R.map_id, Category.id_comp, Functor.comp_obj]

private theorem restrict_hom_injective_of_iso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD₀} D]
    (E : C ⥤ D) (R : D ⥤ C) (ff : E.FullyFaithful) (η : E ⋙ R ≅ 𝟭 C)
    {N N' : D} {P P' : C} (e : N ≅ E.obj P) (e' : N' ≅ E.obj P')
    {f g : N ⟶ N'} (h : R.map f = R.map g) : f = g := by
  have he : e.inv ≫ f ≫ e'.hom = e.inv ≫ g ≫ e'.hom :=
    faithful_restriction_on_image E R ff η P P' (by simp only [R.map_comp, h])
  exact (cancel_epi e.inv).1 ((cancel_mono e'.hom).1
    (by simpa only [← Category.assoc] using he))

private theorem disjoint_comp_immersion
    {S T V X : Scheme.{u}} (i : S ⟶ V) (g : T ⟶ V) (j : V ⟶ X)
    [IsImmersion j] (h : Disjoint (Set.range g) (Set.range i)) :
    Disjoint (Set.range (g ≫ j)) (Set.range (i ≫ j)) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ ⟨z, hz⟩
  exact Set.disjoint_left.mp h ⟨y, rfl⟩ ⟨z, j.isEmbedding.injective hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_reconstruct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    {a : S ⟶ X} (A : GeneratorFactorization a)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hs : ∀ {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
      (g : Y ⟶ X), Disjoint (Set.range g) (Set.range a) →
        IsZero ((upperStar Λ g).obj N)) :
    Nonempty (N ≅ (generatorExtension Λ A).obj ((upperStar Λ a).obj N)) := by
  rcases A with A | A
  · let : IsClosedImmersion A.i := A.hi
    let : IsOpenImmersion A.p := A.hp
    obtain ⟨hV, hVc⟩ := immersion_noetherian A.p
    let := hV
    let := hVc
    let : IsNoetherian A.Z := ⟨⟩
    obtain ⟨hB, hBc⟩ := immersion_noetherian A.p.closedComplement
    let := hB
    let := hBc
    have houter : Disjoint (Set.range A.p.closedComplement) (Set.range a) := by
      simp only [A.p.range_closedComplement, ← A.fac]
      exact (disjoint_compl_left (a := Set.range A.p)).mono_right
        (Set.range_comp_subset_range A.i A.p)
    have ho := moduleOpenSupportedCounit Λ A.p.closedComplement A.p
      (by rw [A.p.range_closedComplement, compl_compl]) N
      (hs A.p.closedComplement houter)
    let U := Scheme.openComplementOfIsClosedImmersion A.i
    have hU : Set.range U.ι = (Set.range A.i)ᶜ := by
      simp [U, Scheme.openComplementOfIsClosedImmersion]
    obtain ⟨hU₁, hU₂⟩ := immersion_noetherian U.ι
    let := hU₁
    let := hU₂
    have hd : Disjoint (Set.range (U.ι ≫ A.p)) (Set.range a) := by
      simpa only [A.fac] using disjoint_comp_immersion A.i U.ι A.p
        (by rw [hU]; exact disjoint_compl_left)
    have hz := (hs (U.ι ≫ A.p) hd).of_iso
      ((upperStarComp Λ U.ι A.p).app N).symm
    have hi := moduleClosedSupportedUnit Λ A.i U.ι hU
      ((upperStar Λ A.p).obj N) hz
    have hF : generatorExtension Λ (.inl A) =
        lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p := rfl
    have hobj := (Functor.congr_obj hF ((upperStar Λ a).obj N)).trans
      (Functor.comp_obj (lowerStar Λ A.i) (openImmersionLowerShriek Λ A.p)
        ((upperStar Λ a).obj N))
    refine ⟨(asIso ((openImmersionLowerShriekUpperStarAdjunction Λ A.p).counit.app N)).symm
      ≪≫ (openImmersionLowerShriek Λ A.p).mapIso
        (asIso ((upperStarLowerStarAdjunction Λ A.i).unit.app
          ((upperStar Λ A.p).obj N))) ≪≫ ?_ ≪≫ eqToIso hobj.symm⟩
    exact (openImmersionLowerShriek Λ A.p).mapIso ((lowerStar Λ A.i).mapIso
      (((upperStarComp Λ A.i A.p).symm ≪≫ upperStarCongr Λ A.fac).app N))
  · let : IsOpenImmersion A.i := A.hi
    let : IsClosedImmersion A.p := A.hp
    obtain ⟨hV, hVc⟩ := immersion_noetherian A.p
    let := hV
    let := hVc
    let : IsNoetherian A.Z := ⟨⟩
    let U := Scheme.openComplementOfIsClosedImmersion A.p
    have hU : Set.range U.ι = (Set.range A.p)ᶜ := by
      simp [U, Scheme.openComplementOfIsClosedImmersion]
    obtain ⟨hU₁, hU₂⟩ := immersion_noetherian U.ι
    let := hU₁
    let := hU₂
    have houter : Disjoint (Set.range U.ι) (Set.range a) := by
      simp only [hU, ← A.fac]
      exact (disjoint_compl_left (a := Set.range A.p)).mono_right
        (Set.range_comp_subset_range A.i A.p)
    have ho := moduleClosedSupportedUnit Λ A.p U.ι hU N (hs U.ι houter)
    obtain ⟨hB, hBc⟩ := immersion_noetherian A.i.closedComplement
    let := hB
    let := hBc
    have hd : Disjoint (Set.range (A.i.closedComplement ≫ A.p)) (Set.range a) := by
      simpa only [A.fac] using disjoint_comp_immersion A.i A.i.closedComplement A.p
        (by rw [A.i.range_closedComplement]; exact disjoint_compl_left)
    have hz := (hs (A.i.closedComplement ≫ A.p) hd).of_iso
      ((upperStarComp Λ A.i.closedComplement A.p).app N).symm
    have hi := moduleOpenSupportedCounit Λ A.i.closedComplement A.i
      (by rw [A.i.range_closedComplement, compl_compl]) ((upperStar Λ A.p).obj N) hz
    have hF : generatorExtension Λ (.inr A) =
        openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p := rfl
    have hobj := (Functor.congr_obj hF ((upperStar Λ a).obj N)).trans
      (Functor.comp_obj (openImmersionLowerShriek Λ A.i) (lowerStar Λ A.p)
        ((upperStar Λ a).obj N))
    refine ⟨asIso ((upperStarLowerStarAdjunction Λ A.p).unit.app N) ≪≫
      (lowerStar Λ A.p).mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ A.i).counit.app
          ((upperStar Λ A.p).obj N))).symm ≪≫ ?_ ≪≫ eqToIso hobj.symm⟩
    exact (lowerStar Λ A.p).mapIso ((openImmersionLowerShriek Λ A.i).mapIso
      (((upperStarComp Λ A.i A.p).symm ≪≫ upperStarCongr Λ A.fac).app N))

attribute [local irreducible] generatorExtension generatorRestriction
  generatorIntersectionModule generatorTensorSource generatorTensorTarget
  derivedTensor DerivedCategory.singleFunctors DerivedCategory.homologyFunctor

section TensorAlgebra
universe uA uB vA vB
variable {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
  [MonoidalCategory C] [MonoidalCategory D]

omit [MonoidalCategory C] [MonoidalCategory D] in
private theorem isoTransport_natural
    {F G : C ⥤ D} (e : F ≅ G) {P Q : C} {L M : D} (f : P ⟶ Q)
    (r : G.obj P ≅ L) (s : G.obj Q ≅ M) (g : L ⟶ M)
    (h : G.map f ≫ s.hom = r.hom ≫ g) :
    F.map f ≫ (e.app Q ≪≫ s).hom = (e.app P ≪≫ r).hom ≫ g := by
  dsimp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, e.hom.naturality, Category.assoc, h, Category.assoc]

omit [MonoidalCategory C] [MonoidalCategory D] in
private theorem isoTransport_compatible
    {F G : C ⥤ D} (e : F ≅ G) {P Q : C} {L : D} (f : P ⟶ Q)
    (r : G.obj P ≅ L) (s : G.obj Q ≅ L)
    (h : G.map f ≫ s.hom = r.hom) :
    F.map f ≫ (e.app Q ≪≫ s).hom = (e.app P ≪≫ r).hom := by
  have h' := isoTransport_natural e f r s (𝟙 L)
    (by simpa only [Category.comp_id] using h)
  simpa only [Category.comp_id] using h'

private noncomputable def tensorRestrictionIso (F : C ⥤ D) [F.Monoidal]
    {P Q : C} {L M : D} (e : F.obj P ≅ L) (e' : F.obj Q ≅ M) :
    F.obj (P ⊗ Q) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso F P Q).symm ≪≫ tensorIso e e'

private theorem tensorRestrictionIso_natural (F : C ⥤ D) [F.Monoidal]
    {P Q P' Q' : C} {L M L' M' : D}
    (e : F.obj P ≅ L) (e' : F.obj Q ≅ M)
    (d : F.obj P' ≅ L') (d' : F.obj Q' ≅ M')
    (f : P ⟶ P') (g : Q ⟶ Q') (l : L ⟶ L') (m : M ⟶ M')
    (hl : F.map f ≫ d.hom = e.hom ≫ l)
    (hm : F.map g ≫ d'.hom = e'.hom ≫ m) :
    F.map (f ⊗ₘ g) ≫ (tensorRestrictionIso F d d').hom =
      (tensorRestrictionIso F e e').hom ≫ (l ⊗ₘ m) := by
  simp only [tensorRestrictionIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_inv]
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
    tensorHom_comp_tensorHom, hl, hm, ← tensorHom_comp_tensorHom, Category.assoc]

private theorem tensorRestrictionIso_compatible (F : C ⥤ D) [F.Monoidal]
    {P Q P' Q' : C} {L M : D}
    (e : F.obj P ≅ L) (e' : F.obj Q ≅ M)
    (d : F.obj P' ≅ L) (d' : F.obj Q' ≅ M)
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hl : F.map f ≫ d.hom = e.hom) (hm : F.map g ≫ d'.hom = e'.hom) :
    F.map (f ⊗ₘ g) ≫ (tensorRestrictionIso F d d').hom =
      (tensorRestrictionIso F e e').hom := by
  have h := tensorRestrictionIso_natural F e e' d d' f g (𝟙 L) (𝟙 M)
    (by simpa only [Category.comp_id] using hl)
    (by simpa only [Category.comp_id] using hm)
  simpa only [id_tensorHom_id, Category.comp_id] using h

private theorem pullTensor_zero_right [Preadditive D] [HasZeroObject D]
    [MonoidalPreadditive D] (F : C ⥤ D) [F.Monoidal]
    (P Q : C) (h : IsZero (F.obj Q)) : IsZero (F.obj (P ⊗ Q)) :=
  ((tensorLeft (F.obj P)).map_isZero h).of_iso (Functor.Monoidal.μIso F P Q).symm

private theorem pullTensor_zero_left [Preadditive D] [HasZeroObject D]
    [MonoidalPreadditive D] (F : C ⥤ D) [F.Monoidal]
    (P Q : C) (h : IsZero (F.obj P)) : IsZero (F.obj (P ⊗ Q)) :=
  ((tensorRight (F.obj Q)).map_isZero h).of_iso (Functor.Monoidal.μIso F P Q).symm
private theorem mono_map_whiskerLeft (F : C ⥤ D) [F.Monoidal]
    (P : C) {Q Q' : C} (f : Q ⟶ Q') (hm : Mono (F.obj P ◁ F.map f)) :
    Mono (F.map (P ◁ f)) := by
  let := hm
  rw [Functor.Monoidal.map_whiskerLeft]
  infer_instance

private theorem flat_of_kernel_detection [Abelian C] [Abelian D]
    [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
    (F : C ⥤ D) [F.Monoidal] [F.Additive] [PreservesFiniteLimits F]
    (P : C) (hP : ObjectProperty.flat (F.obj P))
    (hker : ∀ {Q Q' : C} (f : Q ⟶ Q'),
      IsZero (F.obj (kernel (P ◁ f))) → IsZero (kernel (P ◁ f))) :
    ObjectProperty.flat P := by
  apply (ObjectProperty.flat_iff_preservesFiniteLimits P).mpr
  have : (MonoidalCategory.tensorLeft P).PreservesMonomorphisms := by
    constructor
    intro Q Q' f hf
    let := hf
    have : PreservesFiniteLimits (MonoidalCategory.tensorLeft (F.obj P)) :=
      hP.tensorLeft.preservesFiniteLimits
    have : Mono (F.map f) := F.map_mono f
    have : Mono (F.map (P ◁ f)) := mono_map_whiskerLeft F P f
      ((MonoidalCategory.tensorLeft (F.obj P)).map_mono (F.map f))
    apply Preadditive.mono_of_isZero_kernel
    apply hker f
    exact (isZero_kernel_of_mono (F.map (P ◁ f))).of_iso
      (PreservesKernel.iso F (P ◁ f))
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels
    (MonoidalCategory.tensorLeft P)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end TensorAlgebra

attribute [local irreducible] tensorRestrictionIso ObjectProperty.flat

private def universallySupported
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (a : S ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∀ {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (g : Y ⟶ X), Disjoint (Set.range g) (Set.range a) → IsZero ((upperStar Λ g).obj N)

private theorem supported_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) [IsImmersion a]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : universallySupported Λ a N) (ha : IsZero ((upperStar Λ a).obj N)) : IsZero N := by
  obtain ⟨V, i, j, hi, hj, hc⟩ := IsImmersion.isImmersion_iff_exists.mp
    (inferInstance : IsImmersion a)
  let A : GeneratorFactorization a := .inl ⟨V, i, j, hc, hi, hj⟩
  obtain ⟨e⟩ := generatorExtension_reconstruct Λ A N hN
  exact ((generatorExtension Λ A).map_isZero ha).of_iso e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_tensor_left
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (a : S ⟶ X)
    (P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) :
    universallySupported Λ a (MonoidalCategory.tensorObj P Q) := by
  intro Y _ _ g hg
  exact pullTensor_zero_left (upperStar Λ g) P Q (hP g hg)

private theorem disjoint_pullback_iff
    {S X Y Z : Scheme.{u}} (a : S ⟶ X) (g : Y ⟶ X) (d : Z ⟶ Y) :
    Disjoint (Set.range d) (Set.range (pullback.fst g a)) ↔
      Disjoint (Set.range (d ≫ g)) (Set.range a) := by
  rw [Scheme.Pullback.range_fst, Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h x ⟨z, hz⟩ hx
    exact h ⟨z, rfl⟩ (show g (d z) ∈ Set.range a from hz.symm ▸ hx)
  · intro h x ⟨z, hz⟩ hx
    exact h ⟨z, congrArg g hz⟩ hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X Y : Scheme.{u}}
    (a : S ⟶ X) (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) :
    universallySupported Λ (pullback.fst g a) ((upperStar Λ g).obj P) := by
  intro Z _ _ d hd
  exact (hP (d ≫ g) ((disjoint_pullback_iff a g d).mp hd)).of_iso
    ((upperStarComp Λ d g).app P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_tensor_intersection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a]
    (P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) (hQ : universallySupported Λ b Q) :
    universallySupported Λ (pullback.fst a b ≫ a) (MonoidalCategory.tensorObj P Q) := by
  intro Y _ _ g hg
  obtain ⟨hW, hWc⟩ := immersion_noetherian (pullback.fst g a)
  let := hW
  let := hWc
  apply supported_zero Λ (pullback.fst g a)
  · exact supported_pullback Λ a g _ (supported_tensor_left Λ a P Q hP)
  · let d := pullback.fst g a
    have hd : Disjoint (Set.range (d ≫ g)) (Set.range b) := by
      rw [Set.disjoint_left]
      rintro x ⟨z, rfl⟩ hx
      apply Set.disjoint_left.mp hg ⟨d z, rfl⟩
      rw [Scheme.Pullback.range_fst_comp]
      refine ⟨?_, hx⟩
      exact ⟨pullback.snd g a z,
        congrArg (fun f : pullback g a ⟶ X ↦ f z) pullback.condition.symm⟩
    have hz : IsZero ((upperStar Λ d).obj ((upperStar Λ g).obj Q)) :=
      (hQ (d ≫ g) hd).of_iso ((upperStarComp Λ d g).app Q).symm
    exact pullTensor_zero_right (upperStar Λ g ⋙ upperStar Λ d) P Q hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_kernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    (a : S ⟶ X)
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : P ⟶ Q) (hP : universallySupported Λ a P) :
    universallySupported Λ a (kernel f) := by
  intro Y _ _ g hg
  have hm := (hP g hg).mono ((upperStar Λ g).map f)
  exact (isZero_kernel_of_mono ((upperStar Λ g).map f)).of_iso
    (PreservesKernel.iso (upperStar Λ g) f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supported_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) [IsImmersion a]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : universallySupported Λ a P) (ha : ObjectProperty.flat ((upperStar Λ a).obj P)) :
    ObjectProperty.flat P := by
  apply flat_of_kernel_detection (upperStar Λ a) P ha
  intro Q Q' f hK
  exact supported_zero Λ a _
    (supported_kernel Λ a (P ◁ f) (supported_tensor_left Λ a P Q hP)) hK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lisse_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hP : IsLisseCoefficientModule Λ P) : ObjectProperty.flat P := by
  obtain ⟨U, hU⟩ := hP
  have hraw := ProEtale.condensed_locally_free_tensor_preservesFiniteLimits
    (condensedRingObj Λ W) P
    ⟨U, fun k ↦ (freeAt_iff_standard Λ (U.f k) P).mpr (hU k)⟩
  apply (ObjectProperty.flat_iff_preservesFiniteLimits P).mpr
  exact preservesFiniteLimits_of_natIso
    (Mod.relativeTensorRightIso P ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight P).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorExtension_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] {a : S ⟶ X} [IsImmersion a]
    (A : GeneratorFactorization a)
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hP : IsLisseCoefficientModule Λ P) : ObjectProperty.flat ((generatorExtension Λ A).obj P) := by
  apply supported_flat Λ a _ (fun g hg ↦ generatorExtension_support Λ A g hg P)
  have hr := generatorRestriction_isIso Λ A
  exact ObjectProperty.prop_of_iso ObjectProperty.flat
    ((asIso (generatorRestriction Λ A)).app P).symm (lisse_flat Λ P hP)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionAlong
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S W X : Scheme.{u}}
    {a : S ⟶ X} (A : GeneratorFactorization a) (r : W ⟶ S)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (upperStar Λ (r ≫ a)).obj ((generatorExtension Λ A).obj L) ≅
      (upperStar Λ r).obj L := by
  have hA := generatorRestriction_isIso Λ A
  exact (upperStarComp Λ r a).app _ ≪≫
    (upperStar Λ r).mapIso ((asIso (generatorRestriction Λ A)).app L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionAlong_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S W X : Scheme.{u}}
    {a : S ⟶ X} (A A' : GeneratorFactorization a) (r : W ⟶ S)
    (α : generatorExtension Λ A ⟶ generatorExtension Λ A')
    (ha : Functor.whiskerRight α (upperStar Λ a) ≫ generatorRestriction Λ A' =
      generatorRestriction Λ A)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (upperStar Λ (r ≫ a)).map (α.app L) ≫ (restrictionAlong Λ A' r L).hom =
      (restrictionAlong Λ A r L).hom := by
  have ha' := congrArg (fun t ↦ t.app L) ha
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at ha'
  have hn := (upperStarComp Λ r a).hom.naturality (α.app L)
  dsimp only [Functor.comp_map] at hn
  dsimp only [restrictionAlong, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ha']

section RestrictionNaturality
universe uNat vNat
variable {C D E : Type uNat} [Category.{vNat} C] [Category.{vNat} D]
  [Category.{vNat} E]

private theorem compositeRestriction_natural
    (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ E) (K : D ⥤ E)
    (c : K ≅ G ⋙ H) (r : F ⋙ G ≅ 𝟭 C) {X Y : C} (f : X ⟶ Y) :
    K.map (F.map f) ≫ (c.app (F.obj Y) ≪≫ H.mapIso (r.app Y)).hom =
      (c.app (F.obj X) ≪≫ H.mapIso (r.app X)).hom ≫ H.map f := by
  have hn := c.hom.naturality (F.map f)
  have hr := r.hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn hr
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hr,
    Functor.map_comp, Category.assoc]

end RestrictionNaturality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionAlong_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S W X : Scheme.{u}}
    {a : S ⟶ X} (A : GeneratorFactorization a) (r : W ⟶ S)
    {L L' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    (f : L ⟶ L') :
    (upperStar Λ (r ≫ a)).map ((generatorExtension Λ A).map f) ≫
      (restrictionAlong Λ A r L').hom =
      (restrictionAlong Λ A r L).hom ≫ (upperStar Λ r).map f := by
  have hA := generatorRestriction_isIso Λ A
  exact compositeRestriction_natural (generatorExtension Λ A) (upperStar Λ a)
    (upperStar Λ r) (upperStar Λ (r ≫ a)) (upperStarComp Λ r a)
    (asIso (generatorRestriction Λ A)) f

private noncomputable def intersectionRestrictionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStar Λ (pullback.fst a b ≫ a)).obj
      ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) ≅
      ((upperStar Λ (pullback.fst a b)).obj L ⊗
        (upperStar Λ (pullback.snd a b)).obj M) := by
  exact tensorRestrictionIso (upperStar Λ (pullback.fst a b ≫ a))
    (restrictionAlong Λ A (pullback.fst a b) L)
    ((upperStarCongr Λ (pullback.condition (f := a) (g := b))).app
      ((generatorExtension Λ B).obj M) ≪≫ restrictionAlong Λ B (pullback.snd a b) M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem intersectionRestrictionIso_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    {L L' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {M M' : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (f : L ⟶ L') (g : M ⟶ M') :
    (upperStar Λ (pullback.fst a b ≫ a)).map
      ((generatorExtension Λ A).map f ⊗ₘ (generatorExtension Λ B).map g) ≫
        (intersectionRestrictionIso Λ a b A B L' M').hom =
      (intersectionRestrictionIso Λ a b A B L M).hom ≫
        ((upperStar Λ (pullback.fst a b)).map f ⊗ₘ
          (upperStar Λ (pullback.snd a b)).map g) := by
  have hA := restrictionAlong_natural Λ A (pullback.fst a b) f
  have hB := restrictionAlong_natural Λ B (pullback.snd a b) g
  have hB' := isoTransport_natural
    (upperStarCongr Λ (pullback.condition (f := a) (g := b)))
    ((generatorExtension Λ B).map g)
    (restrictionAlong Λ B (pullback.snd a b) M)
    (restrictionAlong Λ B (pullback.snd a b) M')
    ((upperStar Λ (pullback.snd a b)).map g) hB
  dsimp only [intersectionRestrictionIso]
  exact tensorRestrictionIso_natural (upperStar Λ (pullback.fst a b ≫ a))
    (restrictionAlong Λ A (pullback.fst a b) L) _
    (restrictionAlong Λ A (pullback.fst a b) L') _
    ((generatorExtension Λ A).map f) ((generatorExtension Λ B).map g)
    ((upperStar Λ (pullback.fst a b)).map f) ((upperStar Λ (pullback.snd a b)).map g)
    hA hB'

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem intersectionRestrictionIso_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X)
    (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
    (α : generatorExtension Λ A ⟶ generatorExtension Λ A')
    (β : generatorExtension Λ B ⟶ generatorExtension Λ B')
    (ha : Functor.whiskerRight α (upperStar Λ a) ≫ generatorRestriction Λ A' =
      generatorRestriction Λ A)
    (hb : Functor.whiskerRight β (upperStar Λ b) ≫ generatorRestriction Λ B' =
      generatorRestriction Λ B)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStar Λ (pullback.fst a b ≫ a)).map (α.app L ⊗ₘ β.app M) ≫
      (intersectionRestrictionIso Λ a b A' B' L M).hom =
        (intersectionRestrictionIso Λ a b A B L M).hom := by
  have hA := restrictionAlong_compatible Λ A A' (pullback.fst a b) α ha L
  have hB := restrictionAlong_compatible Λ B B' (pullback.snd a b) β hb M
  have hB' := isoTransport_compatible
    (upperStarCongr Λ (pullback.condition (f := a) (g := b))) (β.app M)
    (restrictionAlong Λ B (pullback.snd a b) M)
    (restrictionAlong Λ B' (pullback.snd a b) M) hB
  dsimp only [intersectionRestrictionIso]
  exact tensorRestrictionIso_compatible (upperStar Λ (pullback.fst a b ≫ a))
    (restrictionAlong Λ A (pullback.fst a b) L) _
    (restrictionAlong Λ A' (pullback.fst a b) L) _
    (α.app L) (β.app M) hA hB'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryComparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    ∃ e : ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) ≅
      (generatorExtension Λ C).obj
        ((upperStar Λ (pullback.fst a b)).obj L ⊗
          (upperStar Λ (pullback.snd a b)).obj M),
      (upperStar Λ (pullback.fst a b ≫ a)).map e.hom ≫
        (generatorRestriction Λ C).app _ = (intersectionRestrictionIso Λ a b A B L M).hom := by
  have hs : universallySupported Λ (pullback.fst a b ≫ a)
      ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) :=
    supported_tensor_intersection Λ a b _ _
      (fun g hg ↦ generatorExtension_support Λ A g hg L)
      (fun g hg ↦ generatorExtension_support Λ B g hg M)
  have he := generatorExtension_reconstruct Λ C _ hs
  have hr := generatorRestriction_isIso Λ C
  exact normalized_comparison_of_essImage (generatorExtension Λ C)
    (upperStar Λ (pullback.fst a b ≫ a))
    (generatorExtension_fullyFaithful Λ C) (asIso (generatorRestriction Λ C))
    ((generatorExtension Λ A).obj L ⊗ (generatorExtension Λ B).obj M) _
    ⟨_, he⟩ (intersectionRestrictionIso Λ a b A B L M)

private noncomputable def ordinaryComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  Classical.choose (ordinaryComparison_exists Λ a b A B C L M)

private theorem ordinaryComparison_normalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStar Λ (pullback.fst a b ≫ a)).map (ordinaryComparison Λ a b A B C L M).hom ≫
      (generatorRestriction Λ C).app _ = (intersectionRestrictionIso Λ a b A B L M).hom :=
  Classical.choose_spec (ordinaryComparison_exists Λ a b A B C L M)

attribute [local irreducible] ordinaryComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryComparison_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    {L L' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {M M' : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (f : L ⟶ L') (g : M ⟶ M') :
    ((generatorExtension Λ A).map f ⊗ₘ (generatorExtension Λ B).map g) ≫
      (ordinaryComparison Λ a b A B C L' M').hom =
      (ordinaryComparison Λ a b A B C L M).hom ≫ (generatorExtension Λ C).map
        ((upperStar Λ (pullback.fst a b)).map f ⊗ₘ
          (upperStar Λ (pullback.snd a b)).map g) := by
  let R := upperStar Λ (pullback.fst a b ≫ a)
  let E := generatorExtension Λ C
  have hr := generatorRestriction_isIso Λ C
  apply restrict_hom_injective_of_iso E R (generatorExtension_fullyFaithful Λ C)
    (asIso (generatorRestriction Λ C)) (ordinaryComparison Λ a b A B C L M) (Iso.refl _)
  apply (cancel_mono ((generatorRestriction Λ C).app _)).1
  have hn := (generatorRestriction Λ C).naturality
    ((upperStar Λ (pullback.fst a b)).map f ⊗ₘ (upperStar Λ (pullback.snd a b)).map g)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [R, Functor.map_comp, Category.assoc]
  rw [ordinaryComparison_normalized, hn, ← Category.assoc,
    ordinaryComparison_normalized, intersectionRestrictionIso_natural]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryComparison_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
    (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
    (α : generatorExtension Λ A ⟶ generatorExtension Λ A')
    (β : generatorExtension Λ B ⟶ generatorExtension Λ B')
    (γ : generatorExtension Λ C ⟶ generatorExtension Λ C')
    (ha : Functor.whiskerRight α (upperStar Λ a) ≫ generatorRestriction Λ A' =
      generatorRestriction Λ A)
    (hb : Functor.whiskerRight β (upperStar Λ b) ≫ generatorRestriction Λ B' =
      generatorRestriction Λ B)
    (hc : Functor.whiskerRight γ (upperStar Λ (pullback.fst a b ≫ a)) ≫
      generatorRestriction Λ C' = generatorRestriction Λ C)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (α.app L ⊗ₘ β.app M) ≫ (ordinaryComparison Λ a b A' B' C' L M).hom =
      (ordinaryComparison Λ a b A B C L M).hom ≫
        γ.app ((upperStar Λ (pullback.fst a b)).obj L ⊗
          (upperStar Λ (pullback.snd a b)).obj M) := by
  let R := upperStar Λ (pullback.fst a b ≫ a)
  let E := generatorExtension Λ C'
  have hr := generatorRestriction_isIso Λ C'
  apply restrict_hom_injective_of_iso E R (generatorExtension_fullyFaithful Λ C')
    (asIso (generatorRestriction Λ C')) (ordinaryComparison Λ a b A B C' L M) (Iso.refl _)
  apply (cancel_mono ((generatorRestriction Λ C').app _)).1
  have hc' := congrArg (fun t ↦ t.app
    ((upperStar Λ (pullback.fst a b)).obj L ⊗
      (upperStar Λ (pullback.snd a b)).obj M)) hc
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hc'
  simp only [R, Functor.map_comp, Category.assoc]
  rw [ordinaryComparison_normalized, hc', ordinaryComparison_normalized,
    intersectionRestrictionIso_compatible Λ a b A A' B B' α β ha hb]

section TensorExistence
universe uE vE
variable {D : Type uE} [Category.{vE} D] [MonoidalCategory D]

-- Cache the coproduct and tensor-preservation proofs before specializing to sheaf modules.
private theorem gradedTensorExists [HasColimitsOfSize.{0, 0} D]
    (X₁ X₂ : GradedObject ℤ D) : X₁.HasTensor X₂ := by
  infer_instance

private theorem gradedTensorFourExists [MonoidalClosed D]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ D) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
  infer_instance

private theorem gradedGoodTensor12 [MonoidalClosed D] [BraidedCategory D]
    (X₁ X₂ X₃ : GradedObject ℤ D) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
  infer_instance

private theorem gradedGoodTensor23 [MonoidalClosed D]
    (X₁ X₂ X₃ : GradedObject ℤ D) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
  infer_instance

end TensorExistence

attribute [local instance] gradedTensorExists gradedTensorFourExists
  gradedGoodTensor12 gradedGoodTensor23

section SingleTensor
universe uK vK wK
variable {D : Type uK} [Category.{vK} D] [Abelian D] [MonoidalCategory D]
  [hBraided : BraidedCategory D] [hClosed : MonoidalClosed D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{vK} D] [hFlatResolution : Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{wK} D]

private theorem singleDerivedMonoidalExists :
    (DerivedCategory.Qh (C := D)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso D (.up ℤ)) := by
  infer_instance

attribute [local instance] singleDerivedMonoidalExists

omit [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] in
@[reassoc]
private theorem singleTensor_component (F G : D) :
    HomologicalComplex.ιTensorObj
        ((CochainComplex.singleFunctor D 0).obj F)
        ((CochainComplex.singleFunctor D 0).obj G) 0 0 0 (by omega) ≫
      (DerivedCategory.moduleCup_singleTensorIso F G).hom.f 0 =
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F ⊗ G)).inv := by
  dsimp only [DerivedCategory.moduleCup_singleTensorIso, Iso.trans_hom,
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso, Iso.app,
    NatIso.ofComponents, CochainComplex.mapBifunctorSingle₂Iso,
    Iso.symm_hom, HomologicalComplex.comp_f, CochainComplex.singleFunctor]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  dsimp only [CochainComplex.mapBifunctorSingle₁Iso, Iso.symm_hom,
    HomologicalComplex.Hom.isoOfComponents]
  dsimp only [Iso.symm_inv, CochainComplex.mapBifunctorSingle₁XIso]
  have hs : (ComplexShape.up ℤ).σ (.up ℤ) (.up ℤ) 0 0 = 1 := by rfl
  rw [hs, one_smul]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [and_self, dif_pos,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [whiskerLeft_id, id_whiskerRight, Category.comp_id, Category.id_comp, tensorHom_id]
  exact Category.id_comp _

omit [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory D] in
private theorem singleComplexTensor_natural {F F' G G' : D} (f : F ⟶ F') (g : G ⟶ G') :
    ((CochainComplex.singleFunctor D 0).map f ⊗ₘ
      (CochainComplex.singleFunctor D 0).map g) ≫
      (DerivedCategory.moduleCup_singleTensorIso F' G').hom =
    (DerivedCategory.moduleCup_singleTensorIso F G).hom ≫
      (CochainComplex.singleFunctor D 0).map (f ⊗ₘ g) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      obtain rfl : n = 0 := by
        change (0 : ℤ) + 0 = n at hpq
        omega
      simp only [HomologicalComplex.comp_f, MonoidalCategory.tensorHom_def, Category.assoc]
      erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
        CochainComplex.ιTensorObj_whiskerLeft_f_assoc, singleTensor_component_assoc,
        singleTensor_component]
      simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_map_f_self]
      dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
      simp only [Category.id_comp, id_tensorHom_id, Category.assoc]
      change (f ≫ 𝟙 F') ▷ G ≫ F' ◁ (g ≫ 𝟙 G') ≫ 𝟙 (F' ⊗ G') =
        𝟙 (F ⊗ G) ≫ f ▷ G ≫ F' ◁ g ≫ 𝟙 (F' ⊗ G')
      simp only [Category.comp_id, Category.id_comp]
    · have hz := (tensorLeft (((CochainComplex.singleFunctor D 0).obj F).X 0)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 G q hq)
      exact hz.eq_of_src _ _
  · have hz := (tensorRight (((CochainComplex.singleFunctor D 0).obj G).X q)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F p hp)
    exact hz.eq_of_src _ _

attribute [local irreducible] Functor.LaxMonoidal.μ

set_option backward.isDefEq.respectTransparency true in
private noncomputable def singleTensorHom (F G : D) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ⟶
        (DerivedCategory.singleFunctor D 0).obj (F ⊗ G) :=
  (((DerivedCategory.singleFunctorIsoCompQ D 0).app F).hom ⊗ₘ
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app G).hom) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor D 0).obj F) ((CochainComplex.singleFunctor D 0).obj G) ≫
    DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom ≫
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app (F ⊗ G)).inv

private theorem singleTensorHom_isIso (F G : D) (hF : ObjectProperty.flat F) :
    IsIso (singleTensorHom F G) := by
  have hK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor D 0).obj F) :=
    (CochainComplex.kFlat_single_obj_iff_flat F 0).mpr hF
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor D 0).obj F)
      ((CochainComplex.singleFunctor D 0).obj G)) := by
    rw [← DerivedCategory.flat_comparison _ _ hK]
    infer_instance
  dsimp only [singleTensorHom]
  infer_instance

private noncomputable def singleTensorIso (F G : D) (hF : ObjectProperty.flat F) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ≅
        (DerivedCategory.singleFunctor D 0).obj (F ⊗ G) := by
  have := singleTensorHom_isIso F G hF
  exact asIso (singleTensorHom F G)

@[reassoc]
private theorem singleTensorHom_natural {F F' G G' : D} (f : F ⟶ F') (g : G ⟶ G') :
    ((DerivedCategory.singleFunctor D 0).map f ⊗ₘ
      (DerivedCategory.singleFunctor D 0).map g) ≫ singleTensorHom F' G' =
      singleTensorHom F G ≫ (DerivedCategory.singleFunctor D 0).map (f ⊗ₘ g) := by
  have hf := (DerivedCategory.singleFunctorIsoCompQ D 0).hom.naturality f
  have hg := (DerivedCategory.singleFunctorIsoCompQ D 0).hom.naturality g
  have hi := (DerivedCategory.singleFunctorIsoCompQ D 0).inv.naturality (f ⊗ₘ g)
  dsimp only [Functor.comp_map] at hf hg hi
  simp only [singleTensorHom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
    ← DerivedCategory.Q.map_comp_assoc, singleComplexTensor_natural,
    DerivedCategory.Q.map_comp, Category.assoc, hi]

private noncomputable def singleTensorIsoComp (F G H : D)
    (hF : ObjectProperty.flat F) (e : F ⊗ G ≅ H) :
    (DerivedCategory.singleFunctor D 0).obj F ⊗
      (DerivedCategory.singleFunctor D 0).obj G ≅
        (DerivedCategory.singleFunctor D 0).obj H :=
  singleTensorIso F G hF ≪≫ (DerivedCategory.singleFunctor D 0).mapIso e

private theorem singleTensorIso_comp_natural {F F' G G' H H' : D}
    (hF : ObjectProperty.flat F) (hF' : ObjectProperty.flat F')
    (f : F ⟶ F') (g : G ⟶ G') (t : H ⟶ H')
    (e : F ⊗ G ≅ H) (e' : F' ⊗ G' ≅ H')
    (h : (f ⊗ₘ g) ≫ e'.hom = e.hom ≫ t) :
    ((DerivedCategory.singleFunctor D 0).map f ⊗ₘ
      (DerivedCategory.singleFunctor D 0).map g) ≫
        (singleTensorIsoComp F' G' H' hF' e').hom =
      (singleTensorIsoComp F G H hF e).hom ≫
        (DerivedCategory.singleFunctor D 0).map t := by
  simp only [singleTensorIsoComp, singleTensorIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [singleTensorHom_natural_assoc, ← Functor.map_comp, h,
    Functor.map_comp]

end SingleTensor

attribute [local instance] singleDerivedMonoidalExists

attribute [local irreducible] singleTensorHom singleTensorIsoComp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientModule_flatResolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Mod.hasFunctorialFlatResolution

set_option maxSynthPendingDepth 16 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def derivedComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hL : IsLisseCoefficientModule Λ L) :
    (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ A).obj L) ⊗
      (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ C).obj
          ((upperStar Λ (pullback.fst a b)).obj L ⊗
            (upperStar Λ (pullback.snd a b)).obj M)) := by
  exact singleTensorIsoComp
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    ((generatorExtension Λ A).obj L) ((generatorExtension Λ B).obj M) _
    (generatorExtension_flat Λ A L hL) (ordinaryComparison Λ a b A B C L M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedComparison_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a))
    {L L' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {M M' : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (hL : IsLisseCoefficientModule Λ L) (hL' : IsLisseCoefficientModule Λ L')
    (f : L ⟶ L') (g : M ⟶ M') :
    ((DerivedCategory.singleFunctor _ 0).map ((generatorExtension Λ A).map f) ⊗ₘ
      (DerivedCategory.singleFunctor _ 0).map ((generatorExtension Λ B).map g)) ≫
        (derivedComparison Λ a b A B C L' M' hL').hom =
      (derivedComparison Λ a b A B C L M hL).hom ≫
        (DerivedCategory.singleFunctor _ 0).map ((generatorExtension Λ C).map
          ((upperStar Λ (pullback.fst a b)).map f ⊗ₘ
            (upperStar Λ (pullback.snd a b)).map g)) := by
  exact singleTensorIso_comp_natural
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    (generatorExtension_flat Λ A L hL) (generatorExtension_flat Λ A L' hL')
    ((generatorExtension Λ A).map f) ((generatorExtension Λ B).map g)
    ((generatorExtension Λ C).map ((upperStar Λ (pullback.fst a b)).map f ⊗ₘ
      (upperStar Λ (pullback.snd a b)).map g))
    (ordinaryComparison Λ a b A B C L M) (ordinaryComparison Λ a b A B C L' M')
    (ordinaryComparison_natural Λ a b A B C f g)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedComparison_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
    (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
    (α : generatorExtension Λ A ⟶ generatorExtension Λ A')
    (β : generatorExtension Λ B ⟶ generatorExtension Λ B')
    (γ : generatorExtension Λ C ⟶ generatorExtension Λ C')
    (ha : Functor.whiskerRight α (upperStar Λ a) ≫ generatorRestriction Λ A' =
      generatorRestriction Λ A)
    (hb : Functor.whiskerRight β (upperStar Λ b) ≫ generatorRestriction Λ B' =
      generatorRestriction Λ B)
    (hc : Functor.whiskerRight γ (upperStar Λ (pullback.fst a b ≫ a)) ≫
      generatorRestriction Λ C' = generatorRestriction Λ C)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hL : IsLisseCoefficientModule Λ L) :
    ((DerivedCategory.singleFunctor _ 0).map (α.app L) ⊗ₘ
      (DerivedCategory.singleFunctor _ 0).map (β.app M)) ≫
        (derivedComparison Λ a b A' B' C' L M hL).hom =
      (derivedComparison Λ a b A B C L M hL).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          (γ.app ((upperStar Λ (pullback.fst a b)).obj L ⊗
            (upperStar Λ (pullback.snd a b)).obj M)) := by
  exact singleTensorIso_comp_natural
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hBraided := Mod.braidedCategory) (hClosed := Mod.monoidalClosed)
    (hFlatResolution := coefficientModule_flatResolution Λ X)
    (generatorExtension_flat Λ A L hL) (generatorExtension_flat Λ A' L hL)
    (α.app L) (β.app M)
    (γ.app ((upperStar Λ (pullback.fst a b)).obj L ⊗
      (upperStar Λ (pullback.snd a b)).obj M))
    (ordinaryComparison Λ a b A B C L M) (ordinaryComparison Λ a b A' B' C' L M)
    (ordinaryComparison_compatible Λ a b A A' B B' C C' α β γ ha hb hc L M)

attribute [local irreducible] derivedComparison

universe vD wD

private theorem homology_single_iso
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (K : DerivedCategory D) (P : D)
    (e : K ≅ (DerivedCategory.singleFunctor D 0).obj P) :
    (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor D q).obj K)) ∧
      Nonempty ((DerivedCategory.homologyFunctor D 0).obj K ≅ P) := by
  constructor
  · intro q hq
    have hz : IsZero ((DerivedCategory.homologyFunctor D q).obj
        ((DerivedCategory.singleFunctor D 0).obj P)) := by
      rcases lt_or_gt_of_ne hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ 0 q hq
      · exact DerivedCategory.isZero_of_isLE _ 0 q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctor D q).mapIso e)
  · exact ⟨(DerivedCategory.homologyFunctor D 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app P⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_closedOpen_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W V X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (i : W ⟶ V) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (P : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hP : IsLisseCoefficientModule Λ P)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P))) :
    (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj K) ∧
    Nonempty ((upperStar Λ (i ≫ j)).obj
      ((DerivedCategory.homologyFunctor _ 0).obj K) ≅ P) ∧
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      Disjoint (Set.range g) (Set.range (i ≫ j)) →
      IsZero ((upperStar Λ g).obj ((DerivedCategory.homologyFunctor _ 0).obj K)) := by
  obtain ⟨hz, ⟨eH⟩⟩ := homology_single_iso K _ e
  obtain ⟨hV, hVc⟩ := immersion_noetherian j
  let := hV
  let := hVc
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian V := ⟨⟩
  have hEP : IsConstantModelConstructible Λ X
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P)) := by
    have hs := stratified_openExtension Λ j _ (stratified_closedPush Λ i P
      (stratified_of_finiteModel Λ W P (lisse_finiteModel Λ W P hP)))
    simpa only [IsConstantModelConstructible,
      if_pos (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)]
      using hs
  have hc := moduleCounitOfAbelian Λ i (ProEtale.abelian_closed_counit i)
  let er : (upperStar Λ (i ≫ j)).obj
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P)) ≅ P :=
    (upperStarComp Λ i j).app _ ≪≫
      (upperStar Λ i).mapIso
        ((asIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit).symm.app
          ((lowerStar Λ i).obj P)) ≪≫
      (asIso (upperStarLowerStarAdjunction Λ i).counit).app P
  refine ⟨hz, ?_, ⟨(upperStar Λ (i ≫ j)).mapIso eH ≪≫ er⟩, ?_⟩
  · have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    simp only [IsConstantModelConstructible, if_pos hqc] at hEP ⊢
    obtain ⟨S, hS⟩ := hEP
    exact ⟨S, fun z ↦ finiteModel_iso Λ (S.domain z)
      ((upperStar Λ (S.immersion z)).mapIso eH.symm) (hS z)⟩
  · intro Y g hg
    exact (closedOpenExtension_zero_of_disjoint Λ i j g hg P).of_iso
      ((upperStar Λ g).mapIso eH)

private theorem single_closedOpen_properties_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W V X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (i : W ⟶ V) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (c : W ⟶ X) (hc : i ≫ j = c)
    (P : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hP : IsLisseCoefficientModule Λ P)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj P))) :
    (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj K) ∧
    Nonempty ((upperStar Λ c).obj
      ((DerivedCategory.homologyFunctor _ 0).obj K) ≅ P) ∧
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      Disjoint (Set.range g) (Set.range c) →
      IsZero ((upperStar Λ g).obj ((DerivedCategory.homologyFunctor _ 0).obj K)) := by
  subst c
  exact single_closedOpen_properties Λ i j P hP K e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedTensor_eq_curriedTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    derivedTensor Λ X = curriedTensor
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := by
  unfold derivedTensor
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorIntersectionModule_eq_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    (a : S ⟶ X) (b : T ⟶ X) :
    generatorIntersectionModule Λ a b =
      (((Functor.whiskeringLeft₂ _).obj (upperStar Λ (pullback.fst a b))).obj
        (upperStar Λ (pullback.snd a b))).obj
          (curriedTensor
            (Mod (Sheaf (Scheme.ProEt.topology (pullback a b)) Ab.{u + 1})
              (condensedRingObj Λ (pullback a b)))) := by
  unfold generatorIntersectionModule
  rfl

section TensorComparisonNaturality
universe uTC₁ vTC₁ uTC₂ vTC₂ uTC₃ vTC₃ uTC₄ vTC₄ uTC₅ vTC₅
variable {A₀ : Type uTC₁} [Category.{vTC₁} A₀]
  {B₀ : Type uTC₂} [Category.{vTC₂} B₀]
  {C₀ : Type uTC₃} [Category.{vTC₃} C₀]
  {D₀ : Type uTC₄} [Category.{vTC₄} D₀] [MonoidalCategory D₀]
  {E₀ : Type uTC₅} [Category.{vTC₅} E₀] [MonoidalCategory E₀]

private noncomputable def tensorComparisonSource
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (S : C₀ ⥤ D₀) : A₀ ⥤ B₀ ⥤ D₀ :=
  (((Functor.whiskeringLeft₂ _).obj (F ⋙ S)).obj (G ⋙ S)).obj (curriedTensor D₀)

private noncomputable def tensorComparisonTarget
    (R : A₀ ⥤ E₀) (T : B₀ ⥤ E₀) (J : E₀ ⥤ C₀) (S : C₀ ⥤ D₀) : A₀ ⥤ B₀ ⥤ D₀ :=
  (Functor.postcompose₂.obj (J ⋙ S)).obj
    ((((Functor.whiskeringLeft₂ _).obj R).obj T).obj (curriedTensor E₀))

private noncomputable def tensorComparisonNatIso
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (R : A₀ ⥤ E₀) (T : B₀ ⥤ E₀)
    (J : E₀ ⥤ C₀) (S : C₀ ⥤ D₀)
    (e : ∀ L M, S.obj (F.obj L) ⊗ S.obj (G.obj M) ≅
      S.obj (J.obj (R.obj L ⊗ T.obj M)))
    (he : ∀ {L L' : A₀} {M M' : B₀} (f : L ⟶ L') (g : M ⟶ M'),
      (S.map (F.map f) ⊗ₘ S.map (G.map g)) ≫ (e L' M').hom =
        (e L M).hom ≫ S.map (J.map (R.map f ⊗ₘ T.map g))) :
    tensorComparisonSource F G S ≅ tensorComparisonTarget R T J S := by
  refine NatIso.ofComponents (fun L ↦ ?_) ?_
  · refine NatIso.ofComponents (fun M ↦ e L M) ?_
    intro M M' g
    change S.obj (F.obj L) ◁ S.map (G.map g) ≫ _ =
      _ ≫ S.map (J.map (R.obj L ◁ T.map g))
    have hn := he (𝟙 L) g
    simpa only [F.map_id, S.map_id, R.map_id, id_tensorHom] using hn
  · intro L L' f
    apply NatTrans.ext
    funext M
    change S.map (F.map f) ▷ S.obj (G.obj M) ≫ _ =
      _ ≫ S.map (J.map (R.map f ▷ T.obj M))
    have hn := he f (𝟙 M)
    simpa only [NatIso.ofComponents_hom_app, G.map_id, S.map_id, T.map_id,
      tensorHom_id] using hn

private noncomputable def tensorComparisonComponent
    {F : A₀ ⥤ C₀} {G : B₀ ⥤ C₀} {R : A₀ ⥤ E₀} {T : B₀ ⥤ E₀}
    {J : E₀ ⥤ C₀} {S : C₀ ⥤ D₀}
    (e : tensorComparisonSource F G S ≅ tensorComparisonTarget R T J S)
    (L : A₀) (M : B₀) :
    S.obj (F.obj L) ⊗ S.obj (G.obj M) ≅
      S.obj (J.obj (R.obj L ⊗ T.obj M)) :=
  (e.app L).app M

private theorem curriedTensor_coherence
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : D₀} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (e : X₁ ⊗ Y₁ ⟶ Z₁) (e' : X₂ ⊗ Y₂ ⟶ Z₂) (t : Z₁ ⟶ Z₂)
    (h : (f ⊗ₘ g) ≫ e' = e ≫ t) :
    ((curriedTensor D₀).map f).app Y₁ ≫ ((curriedTensor D₀).obj X₂).map g ≫ e' =
      e ≫ t := by
  simpa only [curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc] using h

end TensorComparisonNaturality

private theorem whiskeringLeft₂_comp
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* E] (F : A ⥤ B) (G : C ⥤ D) (R : B ⥤ E) (T : D ⥤ E)
    (H : E ⥤ E ⥤ E) :
    (((Functor.whiskeringLeft₂ _).obj F).obj G).obj
        ((((Functor.whiskeringLeft₂ _).obj R).obj T).obj H) =
      (((Functor.whiskeringLeft₂ _).obj (F ⋙ R)).obj (G ⋙ T)).obj H := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem functorComp_assoc
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H := rfl

section

set_option maxSynthPendingDepth 16 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorComparison_normalized_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a)) :
    ∃ e : (tensorComparisonSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
            generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙
            generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)) ≅ (tensorComparisonTarget
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
            upperStar Λ (pullback.fst a b))
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙
            upperStar Λ (pullback.snd a b))
          (generatorExtension Λ C)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)),
      ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
        (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
        (tensorComparisonComponent e L M).hom =
          (derivedComparison Λ a b A B C L.obj M.obj L.property).hom := by
  refine ⟨tensorComparisonNatIso
    (C₀ := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (D₀ := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (E₀ := Mod (Sheaf (Scheme.ProEt.topology (pullback a b)) Ab.{u + 1})
      (condensedRingObj Λ (pullback a b)))
    (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
    (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
    (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
      upperStar Λ (pullback.fst a b))
    (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙
      upperStar Λ (pullback.snd a b))
    (generatorExtension Λ C) (DerivedCategory.singleFunctor _ 0)
    (fun L M ↦ derivedComparison Λ a b A B C L.obj M.obj L.property)
    (fun {L L' _ _} f g ↦
      derivedComparison_natural Λ a b A B C L.property L'.property f.hom g.hom), ?_⟩
  intro L M
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized comparison is built from support reconstruction, and its naturality and
factorization coherence follow by restricting to the intersection. -/
private theorem generator_comparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X S T : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b] :
    ∃ e : ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b)
        (C : GeneratorFactorization (pullback.fst a b ≫ a)),
        (tensorComparisonSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
            generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙
            generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)) ≅ (tensorComparisonTarget
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙
            upperStar Λ (pullback.fst a b))
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙
            upperStar Λ (pullback.snd a b))
          (generatorExtension Λ C)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)),
      ∀ (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
        (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
        (α : generatorExtension Λ A ≅ generatorExtension Λ A')
        (β : generatorExtension Λ B ≅ generatorExtension Λ B')
        (γ : generatorExtension Λ C ≅ generatorExtension Λ C'),
        Functor.whiskerRight α.hom (upperStar Λ a) ≫ generatorRestriction Λ A' =
          generatorRestriction Λ A →
        Functor.whiskerRight β.hom (upperStar Λ b) ≫ generatorRestriction Λ B' =
          generatorRestriction Λ B →
        Functor.whiskerRight γ.hom (upperStar Λ (pullback.fst a b ≫ a)) ≫
          generatorRestriction Λ C' = generatorRestriction Λ C →
        ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
          (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
          ((curriedTensor (DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).map
            ((DerivedCategory.singleFunctor _ 0).map (α.hom.app L.obj))).app
              ((DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M.obj)) ≫
            ((curriedTensor (DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((generatorExtension Λ A').obj L.obj))).map
                ((DerivedCategory.singleFunctor _ 0).map (β.hom.app M.obj)) ≫
            (tensorComparisonComponent (e A' B' C') L M).hom =
          (tensorComparisonComponent (e A B C) L M).hom ≫
            (DerivedCategory.singleFunctor _ 0).map
              (γ.hom.app (((upperStar Λ (pullback.fst a b)).obj L.obj ⊗
            (upperStar Λ (pullback.snd a b)).obj M.obj))) := by
  classical
  choose e he using fun (A : GeneratorFactorization a) (B : GeneratorFactorization b)
    (C : GeneratorFactorization (pullback.fst a b ≫ a)) ↦
      generatorComparison_normalized_exists Λ a b A B C
  refine ⟨e, ?_⟩
  intro A A' B B' C C' α β γ ha hb hc L M
  rw [he A' B' C' L M, he A B C L M]
  exact curriedTensor_coherence
    (D₀ := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    ((DerivedCategory.singleFunctor _ 0).map (α.hom.app L.obj))
    ((DerivedCategory.singleFunctor _ 0).map (β.hom.app M.obj))
    (derivedComparison Λ a b A B C L.obj M.obj L.property).hom
    (derivedComparison Λ a b A' B' C' L.obj M.obj L.property).hom
    ((DerivedCategory.singleFunctor _ 0).map
      (γ.hom.app ((upperStar Λ (pullback.fst a b)).obj L.obj ⊗
        (upperStar Λ (pullback.snd a b)).obj M.obj)))
    (derivedComparison_compatible Λ a b A A' B B' C C' α.hom β.hom γ.hom
      ha hb hc L.obj M.obj L.property)

section ActualTensorAssembly
variable {A₀ B₀ C₀ D₀ E₀ : Type*} [Category* A₀] [Category* B₀]
  [Category* C₀] [Category* D₀] [Category* E₀]

private noncomputable def actualTensorSource
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (S : C₀ ⥤ D₀) (TF : D₀ ⥤ D₀ ⥤ D₀) :
    A₀ ⥤ B₀ ⥤ D₀ :=
  (((Functor.whiskeringLeft₂ _).obj (F ⋙ S)).obj (G ⋙ S)).obj TF

private noncomputable def actualTensorTarget
    (P : A₀ ⥤ B₀ ⥤ E₀) (J : E₀ ⥤ C₀) (S : C₀ ⥤ D₀) : A₀ ⥤ B₀ ⥤ D₀ :=
  (Functor.postcompose₂.obj (J ⋙ S)).obj P

private theorem actualTensor_target_transport
    (F : A₀ ⥤ C₀) (G : B₀ ⥤ C₀) (S : C₀ ⥤ D₀) (TF : D₀ ⥤ D₀ ⥤ D₀)
    (P : A₀ ⥤ B₀ ⥤ E₀) (J : E₀ ⥤ C₀)
    (h : Nonempty (actualTensorSource F G S TF ≅ actualTensorTarget P J S))
    (J' : E₀ ⥤ C₀) (he : J = J') (L : A₀) (M : B₀) :
    Nonempty (((actualTensorSource F G S TF).obj L).obj M ≅
      S.obj (J'.obj ((P.obj L).obj M))) := by
  subst J'
  exact ⟨(h.some.app L).app M⟩

end ActualTensorAssembly

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actual_generator_comparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X S T : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (TF : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (P : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback a b)) Ab.{u + 1})
        (condensedRingObj Λ (pullback a b)))
    (hTF : TF = curriedTensor
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : P =
      (((Functor.whiskeringLeft₂ _).obj (upperStar Λ (pullback.fst a b))).obj
        (upperStar Λ (pullback.snd a b))).obj
          (curriedTensor
            (Mod (Sheaf (Scheme.ProEt.topology (pullback a b)) Ab.{u + 1})
              (condensedRingObj Λ (pullback a b))))) :
    ∃ e : ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b)
        (C : GeneratorFactorization (pullback.fst a b ≫ a)),
        (actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF) ≅ (actualTensorTarget
          ((((Functor.whiskeringLeft₂ _).obj
            (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
            (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj (P))
          (generatorExtension Λ C)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)),
      ∀ (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
        (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
        (α : generatorExtension Λ A ≅ generatorExtension Λ A')
        (β : generatorExtension Λ B ≅ generatorExtension Λ B')
        (γ : generatorExtension Λ C ≅ generatorExtension Λ C'),
        Functor.whiskerRight α.hom (upperStar Λ a) ≫ generatorRestriction Λ A' =
          generatorRestriction Λ A →
        Functor.whiskerRight β.hom (upperStar Λ b) ≫ generatorRestriction Λ B' =
          generatorRestriction Λ B →
        Functor.whiskerRight γ.hom (upperStar Λ (pullback.fst a b ≫ a)) ≫
          generatorRestriction Λ C' = generatorRestriction Λ C →
        ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
          (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
          (TF.map
            ((DerivedCategory.singleFunctor _ 0).map (α.hom.app L.obj))).app
              ((DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M.obj)) ≫
            (TF.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((generatorExtension Λ A').obj L.obj))).map
                ((DerivedCategory.singleFunctor _ 0).map (β.hom.app M.obj)) ≫
            ((e A' B' C').hom.app L).app M =
          ((e A B C).hom.app L).app M ≫
            (DerivedCategory.singleFunctor _ 0).map
              (γ.hom.app ((P.obj L.obj).obj M.obj)) := by
  subst TF
  subst P
  simpa only [actualTensorSource, actualTensorTarget, tensorComparisonSource,
    tensorComparisonTarget, tensorComparisonComponent, Iso.app_hom,
    whiskeringLeft₂_comp, functorComp_assoc,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj] using
    generator_comparison_exists Λ a b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actual_tensor_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X S T : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b]
    (TF : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b)
      (C : GeneratorFactorization (pullback.fst a b ≫ a)),
      Nonempty ((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF) ≅
        (actualTensorTarget
          ((((Functor.whiskeringLeft₂ _).obj
            (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
            (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj
            (generatorIntersectionModule Λ a b))
          (generatorExtension Λ C)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0)))) :
    ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
      (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
      (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (pullback a b),
        ∃ m n : U.I₀ → ℕ, ∀ k : U.I₀,
          Nonempty ((upperStar Λ (U.f k ≫ pullback.fst a b)).obj L.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k)) ∧
          Nonempty ((upperStar Λ (U.f k ≫ pullback.snd a b)).obj M.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (n k)) ∧
          Nonempty ((upperStar Λ (U.f k)).obj
            (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj) ≅
              Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k * n k))) ∧
      ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b),
        (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M))) ∧
        IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj
          ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M)) ∧
        Nonempty ((upperStar Λ (pullback.fst a b ≫ a)).obj
          ((DerivedCategory.homologyFunctor _ 0).obj
            ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M)) ≅
          (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj)) ∧
        ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
          Disjoint (Set.range g) (Set.range (pullback.fst a b ≫ a)) →
          IsZero ((upperStar Λ g).obj ((DerivedCategory.homologyFunctor _ 0).obj
            ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M))) := by
  classical
  intro L M
  refine ⟨intersection_commonCover Λ a b L M, ?_⟩
  intro A B
  obtain ⟨V, i, j, hi, hj, hc⟩ := IsImmersion.isImmersion_iff_exists.mp
    (inferInstance : IsImmersion (pullback.fst a b ≫ a))
  let : IsClosedImmersion i := hi
  let : IsOpenImmersion j := hj
  obtain ⟨e⟩ : Nonempty ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((openImmersionLowerShriek Λ j).obj ((lowerStar Λ i).obj
          (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj)))) := by
    exact actualTensor_target_transport
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
      (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
      (DerivedCategory.singleFunctor _ 0) TF
      ((((Functor.whiskeringLeft₂ _).obj
        (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)))).obj
        (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)))).obj
          (generatorIntersectionModule Λ a b))
      (generatorExtension Λ (.inl ⟨V, i, j, hc, hi, hj⟩))
      (h A B (.inl ⟨V, i, j, hc, hi, hj⟩))
      (lowerStar Λ i ⋙ openImmersionLowerShriek Λ j)
      (generatorExtension_inl_eq Λ i j hc) L M
  exact single_closedOpen_properties_transport Λ i j (pullback.fst a b ≫ a) hc
    (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj)
    (intersection_lisse Λ a b L M) ((((actualTensorSource
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := S)) ⋙ generatorExtension Λ A)
          (ObjectProperty.ι (IsLisseCoefficientModule Λ (X := T)) ⋙ generatorExtension Λ B)
          (DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) 0) TF)).obj L).obj M) e

end

end GeneratorTensorProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor-intersection isomorphisms, natural in both lisse modules and independent of
both orders of open/closed factorization under normalized extension comparisons.
Source: blueprint main-20261015, sk-thm-sf-pf-field-tensor.proof.md, Proof (1)
(blueprint: lem-sfb-locally-closed-generator-tensor-intersection).

Proof. Immersions into the Noetherian scheme have Noetherian, quasi-compact sources.
Use this also for their factors, pullbacks and complementary immersions. All intersections
below are actual scheme fibre products, with their pulled-back coefficient rings.

Pull the two lisse covers back to the intersection and refine them by pairwise fibre
products. Monoidal inverse image and finite-biproduct distributivity identify the tensor
with the finite free module of rank `m * n`. This includes empty covers and zero ranks.

For either order of factors, the open unit and closed counit make restriction of extension
isomorphic to the identity, and extension is fully faithful. Open base change, closed base
change and complementary vanishing show that these extensions vanish after disjoint
pullbacks. Successive open and closed support reconstruction therefore identifies any
supported module with the extension of its restriction. Tensor preserves support; the
tensor of modules supported on the two immersions is supported on their fibre product.
Normalize its extension comparison by the monoidal restriction isomorphism. Full
faithfulness and the restriction isomorphism make restriction injective on Hom sets, giving
naturality and compatibility with every normalized change of either factorization.

Lisse modules are flat by local finite freeness. Their extensions are flat as well: the
kernel of tensoring a monomorphism with such an extension is supported on the immersion,
and its restriction vanishes by exact monoidal inverse image and flatness of the lisse
restriction. Support reconstruction detects the kernel as zero.

The degree-zero complex of a flat module is K-flat. The localization tensor comparison
and the canonical tensor isomorphism for two single complexes identify the derived tensor
with the single complex of the ordinary tensor. Checking the `(0,0)` summand proves
naturality; the other summands vanish. Combining with the ordinary comparison gives the
isomorphism of bifunctors and its factorization compatibility. Tensor functors are passed
as parameters in the final assembly, so transport uses their proved whole-functor equations.

Finally choose a closed-then-open factorization of the intersection. Homology of the single
complex vanishes away from zero; its degree-zero module has the constructible stratification
obtained by closed direct image and open extension of the lisse module. The restriction
isomorphism identifies its restriction to the intersection, and disjoint-pullback vanishing
for this factorization applies to arbitrary source schemes. -/
theorem locallyClosedGeneratorTensorIntersection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X S T : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (a : S ⟶ X) (b : T ⟶ X) [IsImmersion a] [IsImmersion b] :
    (∃ e : ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b)
        (C : GeneratorFactorization (pullback.fst a b ≫ a)),
        generatorTensorSource Λ A B ≅ generatorTensorTarget Λ a b C,
      ∀ (A A' : GeneratorFactorization a) (B B' : GeneratorFactorization b)
        (C C' : GeneratorFactorization (pullback.fst a b ≫ a))
        (α : generatorExtension Λ A ≅ generatorExtension Λ A')
        (β : generatorExtension Λ B ≅ generatorExtension Λ B')
        (γ : generatorExtension Λ C ≅ generatorExtension Λ C'),
        Functor.whiskerRight α.hom (upperStar Λ a) ≫ generatorRestriction Λ A' =
          generatorRestriction Λ A →
        Functor.whiskerRight β.hom (upperStar Λ b) ≫ generatorRestriction Λ B' =
          generatorRestriction Λ B →
        Functor.whiskerRight γ.hom (upperStar Λ (pullback.fst a b ≫ a)) ≫
          generatorRestriction Λ C' = generatorRestriction Λ C →
        ∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
          (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
          ((derivedTensor Λ X).map
            ((DerivedCategory.singleFunctor _ 0).map (α.hom.app L.obj))).app
              ((DerivedCategory.singleFunctor _ 0).obj ((generatorExtension Λ B).obj M.obj)) ≫
            ((derivedTensor Λ X).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((generatorExtension Λ A').obj L.obj))).map
                ((DerivedCategory.singleFunctor _ 0).map (β.hom.app M.obj)) ≫
            ((e A' B' C').hom.app L).app M =
          ((e A B C).hom.app L).app M ≫
            (DerivedCategory.singleFunctor _ 0).map
              (γ.hom.app (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj))) ∧
    (∀ (L : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S)))
      (M : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := T))),
      (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage (pullback a b),
        ∃ m n : U.I₀ → ℕ, ∀ k : U.I₀,
          Nonempty ((upperStar Λ (U.f k ≫ pullback.fst a b)).obj L.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k)) ∧
          Nonempty ((upperStar Λ (U.f k ≫ pullback.snd a b)).obj M.obj ≅
            Mod.finiteFree (condensedRingObj Λ (U.X k)) (n k)) ∧
          Nonempty ((upperStar Λ (U.f k)).obj
            (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj) ≅
              Mod.finiteFree (condensedRingObj Λ (U.X k)) (m k * n k))) ∧
      ∀ (A : GeneratorFactorization a) (B : GeneratorFactorization b),
        (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (((generatorTensorSource Λ A B).obj L).obj M))) ∧
        IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj
          (((generatorTensorSource Λ A B).obj L).obj M)) ∧
        Nonempty ((upperStar Λ (pullback.fst a b ≫ a)).obj
          ((DerivedCategory.homologyFunctor _ 0).obj
            (((generatorTensorSource Λ A B).obj L).obj M)) ≅
          (((generatorIntersectionModule Λ a b).obj L.obj).obj M.obj)) ∧
        ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
          Disjoint (Set.range g) (Set.range (pullback.fst a b ≫ a)) →
          IsZero ((upperStar Λ g).obj ((DerivedCategory.homologyFunctor _ 0).obj
            (((generatorTensorSource Λ A B).obj L).obj M)))) := by
  obtain ⟨e, _⟩ := actual_generator_comparison_exists Λ a b (derivedTensor Λ X)
    (generatorIntersectionModule Λ a b) (derivedTensor_eq_curriedTensor Λ X)
    (generatorIntersectionModule_eq_tensor Λ a b)
  have hp := actual_tensor_properties Λ a b (derivedTensor Λ X) (fun A B C ↦ ⟨e A B C⟩)
  have hn := And.intro (actual_generator_comparison_exists Λ a b (derivedTensor Λ X)
    (generatorIntersectionModule Λ a b) (derivedTensor_eq_curriedTensor Λ X)
    (generatorIntersectionModule_eq_tensor Λ a b)) hp
  simp only [generatorTensorSource, generatorTensorTarget, actualTensorSource,
    actualTensorTarget, functorComp_assoc] at hn ⊢
  exact hn

end AlgebraicGeometry.ProEtale.CondensedRing

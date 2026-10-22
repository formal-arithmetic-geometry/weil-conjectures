/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NP and K1
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Nilpotent derived reduction detects an upper cohomological bound

Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-derived-upper-bound).

Ordinary modules are encoded on the existing one-object site with bottom topology.
The additive scalar-extension functor and its left derived functor are specified by
exactly the object formula, morphism formula and universal property supplied by
`SheafOfModules.derivedChangeOfRings`; no choice of a particular model is required.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The one-object site is explicitly equivalent to ordinary modules.
private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := Opposite.op ⟨PUnit.unit⟩

private noncomputable abbrev pointEval (A : Type u) [CommRing A] :
    RingSiteModules A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)) point

private noncomputable def pointConstant (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ RingSiteModules A where
  obj M := ⟨{ obj := fun _ ↦ M
              map := fun _ ↦ ModuleCat.ofHom (LinearMap.id) }, Presheaf.isSheaf_bot _⟩
  map f := ⟨{ app := fun _ ↦ f }⟩

private noncomputable def pointUnitIso {A : Type u} [CommRing A]
    (M : RingSiteModules A) : M ≅ (pointConstant A).obj ((pointEval A).obj M) := by
  let e : M.val ≅ ((pointConstant A).obj ((pointEval A).obj M)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V g
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
        ext x
        simp [pointConstant, pointEval]
        rfl)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e

private noncomputable def pointEquivalence (A : Type u) [CommRing A] :
    RingSiteModules A ≌ ModuleCat.{u} A where
  functor := pointEval A
  inverse := pointConstant A
  unitIso := NatIso.ofComponents pointUnitIso (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private noncomputable local instance pointEval_isEquivalence (A : Type u) [CommRing A] :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private noncomputable local instance pointConstant_isEquivalence (A : Type u) [CommRing A] :
    (pointConstant A).IsEquivalence := (pointEquivalence A).isEquivalence_inverse

private local instance pointConstant_additive (A : Type u) [CommRing A] :
    (pointConstant A).Additive where
  map_add := by intros; rfl

private local instance pointEval_additive (A : Type u) [CommRing A] :
    (pointEval A).Additive where
  map_add := by intros; rfl

private noncomputable def pointTensorMap
    {A : Type u} [CommRing A] (M N : RingSiteModules A) :
    M.val ⊗ N.val ⟶
      (letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
       M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val

private theorem pointTensorMap_isIso
    {A : Type u} [CommRing A] (M N : RingSiteModules A) :
    IsIso (pointTensorMap M N) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)).obj)
  have : IsIso (adj.unit.app (M.val ⊗ N.val)) :=
    adj.isIso_unit_app_of_iso (X := ⟨M.val ⊗ N.val, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  have : IsIso (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))).map
      (SheafOfModules.tensorObjIsoSheafification
        (R := CochainComplex.onePointRingSheaf A) M N).inv))
  change IsIso (adj.unit.app (M.val ⊗ N.val) ≫ _)
  infer_instance

private theorem pointTensorMap_natural
    {A : Type u} [CommRing A] {M M' N N' : RingSiteModules A}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (f.val ⊗ₘ g.val) ≫ pointTensorMap M' N' =
      pointTensorMap M N ≫ (f ⊗ₘ g).val := by
  let R := CochainComplex.onePointRingSheaf A
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  have h : (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom ≫
        S.map (f.val ⊗ₘ g.val) := by
    rw [tensorHom_def, Category.assoc,
      SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := R) M' g,
      ← Category.assoc, SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := R) f N,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv ≫
      (f ⊗ₘ g) = S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').inv := by
    rw [← cancel_mono (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom]
    simp [Category.assoc, h]
  have hu := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.naturality
      (f.val ⊗ₘ g.val)
  dsimp at hu
  dsimp only [pointTensorMap]
  rw [← Category.assoc, hu, Category.assoc]
  exact congrArg (fun z ↦ _ ≫ z) (congrArg SheafOfModules.Hom.val hi.symm)

private noncomputable def pointTensorIso
    {A : Type u} [CommRing A] (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (pointEval A).obj M ⊗ (pointEval A).obj N ≅ (pointEval A).obj (M ⊗ N) := by
  have := pointTensorMap_isIso M N
  exact (PresheafOfModules.evaluation _ point).mapIso (asIso (pointTensorMap M N))

private noncomputable def pointTensorNatIso (A : Type u) [CommRing A] :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (((Functor.whiskeringLeft₂ _).obj (pointEval A)).obj
      (pointEval A)).obj (curriedTensor _) ≅
      (Functor.postcompose₂.obj (pointEval A)).obj (curriedTensor _) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ pointTensorIso M N)
    (fun {N N'} g ↦ ?_)) (fun {M M'} f ↦ ?_)
  · change (M.val.obj point ◁ g.val.app point) ≫ (pointTensorMap M N').app point =
      (pointTensorMap M N).app point ≫ (M ◁ g).val.app point
    have h := congrArg (fun z ↦ z.app point) (pointTensorMap_natural (𝟙 M) g)
    simp only [SheafOfModules.id_val, id_tensorHom, PresheafOfModules.comp_app] at h
    exact h
  · apply NatTrans.ext
    funext N
    change (f.val.app point ▷ N.val.obj point) ≫ (pointTensorMap M' N).app point =
      (pointTensorMap M N).app point ≫ (f ▷ N).val.app point
    have h := congrArg (fun z ↦ z.app point) (pointTensorMap_natural f (𝟙 N))
    simp only [SheafOfModules.id_val, tensorHom_id, PresheafOfModules.comp_app] at h
    exact h

private local instance pointExtend_additive
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).left_adjoint_additive

private noncomputable def pointExtensionPresheaf
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    RingSiteModules A ⥤ PresheafOfModules.{u}
      (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf B)).obj) where
  obj M := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap ρ) M
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars ρ).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap ρ) _ f }
  map_id := by intro M; ext U : 1; simp; rfl
  map_comp := by intro M N P f g; ext U : 1; simp

private noncomputable def pointExtensionFunctor
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    RingSiteModules A ⥤ RingSiteModules B :=
  pointExtensionPresheaf ρ ⋙ PresheafOfModules.sheafification
    (𝟙 (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf B)).obj))

private noncomputable def pointExtensionIso
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (E : RingSiteModules A ⥤ RingSiteModules B)
    (ho : ∀ M, E.obj M = SheafOfModules.changeOfRings (ringSiteMap ρ) M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap ρ) M f ≫ eqToHom (ho N).symm) :
    pointExtensionFunctor ρ ≅ E :=
  NatIso.ofComponents (fun M ↦ eqToIso (ho M).symm) (by
    intro M N f
    dsimp
    rw [hm]
    simp
    rfl)

private noncomputable def pointExtensionComparison
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    pointEval A ⋙ ModuleCat.extendScalars ρ ≅ pointExtensionFunctor ρ ⋙ pointEval B := by
  let R := ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf B))
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  have h (M : RingSiteModules A) :
      IsIso (adj.unit.app ((pointExtensionPresheaf ρ).obj M)) :=
    adj.isIso_unit_app_of_iso
      (X := ⟨(pointExtensionPresheaf ρ).obj M, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  refine NatIso.ofComponents (fun M ↦
    (PresheafOfModules.evaluation R.obj point).mapIso
      (asIso (adj.unit.app ((pointExtensionPresheaf ρ).obj M)))) ?_
  intro M N f
  exact congrArg (fun z ↦ z.app point)
    (adj.unit.naturality ((pointExtensionPresheaf ρ).map f))

private theorem pointEval_flat
    {A : Type u} [CommRing A] (M : RingSiteModules A)
    (hM : SheafOfModules.IsFlat (R := CochainComplex.onePointRingSheaf A) M) :
    Module.Flat A ((pointEval A).obj M) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let := SheafOfModules.symmetricCategory (CochainComplex.onePointRingSheaf A)
  have : PreservesFiniteLimits (tensorRight M) := (exactFunctor_iff _).1 hM |>.1
  have : PreservesFiniteLimits (tensorLeft M) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
  let e : pointConstant A ⋙ tensorLeft M ⋙ pointEval A ≅
      tensorLeft ((pointEval A).obj M) :=
    (Functor.isoWhiskerLeft (pointConstant A) ((pointTensorNatIso A).app M)).symm
  have : PreservesFiniteLimits (tensorLeft ((pointEval A).obj M)) :=
    preservesFiniteLimits_of_natIso e
  exact (ModuleCat.flat_iff_flat _).1
    ((ObjectProperty.flat_iff_preservesFiniteLimits _).2 inferInstance)

private theorem pointEval_kFlat
    {A : Type u} [CommRing A] (P : CochainComplex (RingSiteModules A) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat
      (R := CochainComplex.onePointRingSheaf A) P) :
    ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L
        (((pointEval A).mapHomologicalComplex (.up ℤ)).obj P) (curriedTensor _)).Acyclic := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro L hL
  let L' := ((pointConstant A).mapHomologicalComplex (.up ℤ)).obj L
  have hL' : L'.Acyclic := fun i ↦ (hL i).map (pointConstant A)
  have ht := hP L' hL'
  have he : (((pointEval A).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor L' P (curriedTensor _))).Acyclic :=
    fun i ↦ (ht i).map (pointEval A)
  let comparison := asIso (HomologicalComplex.mapBifunctorComparison
    (pointTensorNatIso A).inv (.up ℤ) L' P)
  let counit := (pointEquivalence A |>.mapHomologicalComplex (.up ℤ)).counitIso.app L
  let ec := ((curriedTensor _).mapIso counit).app
    (((pointEval A).mapHomologicalComplex (.up ℤ)).obj P)
  intro i
  exact (he i).of_iso (comparison ≪≫ ec)

-- Any property stable under extensions propagates along the nilpotent filtration.
private theorem nilpotent_module_devissage
    {A : Type u} [CommRing A] (I : Ideal A) (T : ModuleCat.{u} A → Prop)
    (hzero : ∀ M, IsZero M → T M)
    (hext : ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
      T S.X₁ → T S.X₃ → T S.X₂)
    (hbase : ∀ M : ModuleCat.{u} A, (∀ a ∈ I, ∀ m : M, a • m = 0) → T M)
    (n : ℕ) : ∀ M : ModuleCat.{u} A,
      (∀ a ∈ I ^ n, ∀ m : M, a • m = 0) → T M := by
  induction n with
  | zero =>
    intro M hM
    apply hzero M
    apply (IsZero.iff_id_eq_zero M).2
    ext m
    simpa using hM 1 (by simp) m
  | succ n ih =>
    intro M hM
    let L : Submodule A M := I • (⊤ : Submodule A M)
    let S : ShortComplex (ModuleCat.{u} A) :=
      ShortComplex.mk (ModuleCat.ofHom L.subtype) (ModuleCat.ofHom L.mkQ)
        (by ext m; simp)
    have hS : S.ShortExact := by
      apply ModuleCat.shortComplex_shortExact
      · intro m
        change L.mkQ m = 0 ↔ ∃ x : L, L.subtype x = m
        simp
      · exact L.injective_subtype
      · exact L.mkQ_surjective
    apply hext S hS
    · apply ih (ModuleCat.of A L)
      intro a ha x
      apply Subtype.ext
      change a • (x : M) = 0
      refine Submodule.smul_induction_on x.property ?_ ?_
      · intro r hr m _
        rw [← mul_smul]
        apply hM (a * r)
        simpa only [pow_succ] using Ideal.mul_mem_mul ha hr
      · intro x y hx hy
        simp only [smul_add, hx, hy, add_zero]
    · apply hbase (ModuleCat.of A (M ⧸ L))
      intro a ha m
      obtain ⟨x, rfl⟩ := L.mkQ_surjective m
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero L).2
        (Submodule.smul_mem_smul ha (Submodule.mem_top : x ∈ (⊤ : Submodule A M)))

private noncomputable def moduleTensorComplex {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj M := ((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex
    ((MonoidalCategory.curriedTensor _).map f) (.up ℤ)).app P
  map_id M := by ext i; simp
  map_comp f g := by ext i; simp

private theorem module_kFlat_of_acyclic_tensor
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro L hL
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor L P (curriedTensor _))).2 (hP L hL)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

private theorem module_tensor_upper_bound
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (P.homology i))
    (M : ModuleCat.{u} A) :
    ∀ i : ℤ, b < i → IsZero (((moduleTensorComplex P).obj M).homology i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  have : P.IsLE b := (P.isLE_iff b).2 fun i hi ↦
    (HomologicalComplex.exactAt_iff_isZero_homology P i).2 (hb i hi)
  have : (Q.obj P).IsLE b := inferInstance
  have h := isLE_tensor (Q.obj P) ((singleFunctor _ 0).obj M) b 0
  have : (Q.obj (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P)).IsLE b := by
    simpa only [add_zero] using TStructure.t.isLE_of_iso
      (QObjTensorSingleFunctorObjIso P hP M) (b + 0)
  have h' : CochainComplex.IsLE
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) b :=
    (isLE_Q_obj_iff _ b).1 inferInstance
  intro i hi
  have e := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight M) (.up ℤ)).app P
  exact (CochainComplex.exactAt_of_isLE _ b i hi).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso e)

private theorem flat_tensor_nilpotent_devissage
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hflat : ∀ i : ℤ, Module.Flat A (P.X i)) (b : ℤ)
    (hbase : ∀ M : ModuleCat.{u} A, (∀ a ∈ I, ∀ m : M, a • m = 0) →
      ∀ i : ℤ, b < i → IsZero (((moduleTensorComplex P).obj M).homology i)) :
    ∀ i : ℤ, b < i → IsZero (P.homology i) := by
  let T := moduleTensorComplex P
  have : T.Additive := by
    constructor
    intro M N f g
    ext i : 1
    change (f + g) ▷ P.X i = f ▷ P.X i + g ▷ P.X i
    simp
  have hzero (M : ModuleCat.{u} A) (hM : IsZero M) :
      ∀ i : ℤ, b < i → IsZero ((T.obj M).homology i) := by
    intro i _
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero ((MonoidalCategory.tensorRight (P.X i)).obj M)
    exact Functor.map_isZero _ hM
  have hext (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
      (h₁ : ∀ i : ℤ, b < i → IsZero ((T.obj S.X₁).homology i))
      (h₃ : ∀ i : ℤ, b < i → IsZero ((T.obj S.X₃).homology i)) :
      ∀ i : ℤ, b < i → IsZero ((T.obj S.X₂).homology i) := by
    have hcomplex : (S.map T).ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro i
      have := hflat i
      change (S.map (MonoidalCategory.tensorRight (P.X i))).ShortExact
      exact hS.map_of_exact (MonoidalCategory.tensorRight (P.X i))
    intro i hi
    exact (hcomplex.homology_exact₂ i).isZero_X₂
      ((h₁ i hi).eq_of_src _ _) ((h₃ i hi).eq_of_tgt _ _)
  have hunit := nilpotent_module_devissage I
    (fun M ↦ ∀ i : ℤ, b < i → IsZero ((T.obj M).homology i)) hzero hext hbase N
      (ModuleCat.of A A) (by
        intro a ha m
        have ha' : a = 0 := by simpa [hI] using ha
        simp [ha'])
  intro i hi
  have e : T.obj (ModuleCat.of A A) ≅ P :=
    (NatIso.mapHomologicalComplex (MonoidalCategory.leftUnitorNatIso
      (ModuleCat.{u} A)) (.up ℤ)).app P ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
  exact (hunit i hi).of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e.symm)

-- The filtration argument for ordinary modules, before transporting it to the site.
private theorem ordinary_nilpotent_upper_bound
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hflat : ∀ i : ℤ, Module.Flat A (P.X i))
    (hP : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic)
    (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero
      ((((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P).homology i)) :
    ∀ i : ℤ, b < i → IsZero (P.homology i) := by
  let q := Ideal.Quotient.mk I
  let Q := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  have hQ := module_kFlat_of_acyclic_tensor Q
    (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat q P hP)
  apply flat_tensor_nilpotent_devissage I N hI P hflat b
  intro M hM
  have ht : Module.IsTorsionBySet A M I := fun {m a} ↦ hM a a.property m
  let := ht.module
  let M' : ModuleCat.{u} (A ⧸ I) := ModuleCat.of (A ⧸ I) M
  let res := ModuleCat.restrictScalars q
  let eM : res.obj M' ≅ M :=
    (show res.obj M' ≃ₗ[A] M from
      { AddEquiv.refl M with map_smul' := fun _ _ ↦ rfl }).toModuleIso
  obtain ⟨e, he⟩ := ModuleCat.exists_tensorRestrictExtend_module_natural q
  let e' : ((tensorLeft M' ⋙ res).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((tensorLeft (res.obj M')).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ e M' (P.X i)) (by
      intro i j hij
      exact (he M' M' (P.X i) (P.X j) (𝟙 _) (P.d i j)).symm)
  let e'' := (NatIso.mapHomologicalComplex
    ((curriedTensor _).mapIso eM) (.up ℤ)).app P
  intro i hi
  have hz := module_tensor_upper_bound Q hQ b hb M' i hi
  have hr := res.map_isZero hz
  let eh' := (res.mapHomologicalComplexHomologyIso (.up ℤ) i).app
    (((tensorLeft M').mapHomologicalComplex (.up ℤ)).obj Q)
  exact hr.of_iso (((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (e' ≪≫ e'')).symm ≪≫ eh')

/-- Reduction modulo a nilpotent ideal detects vanishing above the same integer.
Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-derived-upper-bound).

Proof:
1. Take a termwise flat K-flat resolution `P` of a representative of `C`.
   Uniqueness of left derived functors and `derivedChangeOfRings` identify
   `LF.obj C` with the localization of termwise scalar extension of `P`.
2. On the one-object bottom-topology site, evaluation is an exact equivalence
   with ordinary modules. The sheafification unit identifies evaluation of
   sheaf tensor and scalar extension with their ordinary module constructions.
   Evaluation preserves flat terms and K-flatness, including unbounded total tensors.
3. Let `Q` be the ordinary reduced complex. It is K-flat by base change.
   The source theorem `isLE_tensor` bounds `Q` tensor-derived `M[0]` above `b`.
   `QObjTensorSingleFunctorObjIso` identifies this with termwise tensor by `M`.
4. For an `A`-module killed by `I`, use its quotient-ring action and the natural
   balanced tensor-restriction-extension comparison to obtain the same bound
   for its tensor with the evaluated `P`.
5. Induct on the annihilating power of `I`, using the short exact sequence
   `IM → M → M/IM`. Flat terms preserve this sequence under tensor, and exactness
   of its homology sequence propagates vanishing from the outer terms to the middle.
6. Apply the induction to `M=A` and exponent `N`. The tensor unit isomorphism
   gives the bound for `P`; the evaluation equivalence reflects zero homology,
   and the resolution transports the bound to `C`.
-/
theorem isZero_homology_of_nilpotent_derived_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules (A ⧸ I))]
    (E : RingSiteModules A ⥤ RingSiteModules (A ⧸ I))
    (hobjects : ∀ M : RingSiteModules A,
      E.obj M = SheafOfModules.changeOfRings (ringSiteMap (Ideal.Quotient.mk I)) M)
    (hmaps : ∀ {M M' : RingSiteModules A} (f : M ⟶ M'),
      E.map f = eqToHom (hobjects M) ≫
        SheafOfModules.changeOfRingsHom (ringSiteMap (Ideal.Quotient.mk I)) M f ≫
          eqToHom (hobjects M').symm)
    [E.Additive]
    (LF : DerivedCategory (RingSiteModules A) ⥤ DerivedCategory (RingSiteModules (A ⧸ I)))
    (ε : Qh ⋙ LF ⟶ E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (RingSiteModules A) (ComplexShape.up ℤ)))
    (C : DerivedCategory (RingSiteModules A)) (b : ℤ)
    (hred : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (RingSiteModules (A ⧸ I)) i).obj (LF.obj C))) :
    ∀ i : ℤ, b < i → IsZero ((homologyFunctor (RingSiteModules A) i).obj C) := by
  by_cases hzero : N = 0
  · subst N
    exact (Nat.not_succ_le_zero 0 hN).elim
  let G := Q.objPreimage C
  obtain ⟨P, f, hP, hflat, hf, hepi⟩ := CochainComplex.exists_isKFlatResolution G
  let : QuasiIso f := hf
  let ePC : Q.obj P ≅ C := asIso (Q.map f) ≪≫ Q.objObjPreimageIso C
  let q := Ideal.Quotient.mk I
  obtain ⟨E₀, ho₀, hm₀, ha₀, _, _, LF₀, ε₀, hLF₀, _, hε₀⟩ :=
    SheafOfModules.derivedChangeOfRings (ringSiteMap q)
  let := ha₀
  let := hLF₀
  let := hLF
  let eE : E₀ ≅ E := (pointExtensionIso q E₀ ho₀ hm₀).symm ≪≫
    pointExtensionIso q E hobjects hmaps
  let W := HomotopyCategory.quasiIso (RingSiteModules A) (.up ℤ)
  let eH : E₀.mapHomotopyCategory (.up ℤ) ≅ E.mapHomotopyCategory (.up ℤ) :=
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex eE (.up ℤ))
        (HomotopyCategory.quotient _ (.up ℤ)))
  let eD := Functor.leftDerivedNatIso LF₀ LF ε₀ ε W
    (Functor.isoWhiskerRight eH Qh)
  let HP := (HomotopyCategory.quotient (RingSiteModules A) (.up ℤ)).obj P
  have : IsIso (ε₀.app HP) := hε₀ P hP
  let eModel : LF.obj C ≅ Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
    (LF.mapIso ePC).symm ≪≫ (LF.mapIso ((quotientCompQhIso _).app P)).symm ≪≫
      (eD.app (Qh.obj HP)).symm ≪≫ asIso (ε₀.app HP) ≪≫
      Qh.mapIso ((E₀.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (quotientCompQhIso _).app _ ≪≫
      Q.mapIso ((NatIso.mapHomologicalComplex eE (.up ℤ)).app P)
  have hEP (i : ℤ) (hi : b < i) :
      IsZero (((E.mapHomologicalComplex (.up ℤ)).obj P).homology i) :=
    ((hred i hi).of_iso ((homologyFunctor _ i).mapIso eModel).symm).of_iso
      ((homologyFunctorFactors _ i).app _).symm
  let eEval : pointEval A ⋙ ModuleCat.extendScalars q ≅ E ⋙ pointEval (A ⧸ I) :=
    pointExtensionComparison q ≪≫
      Functor.isoWhiskerRight (pointExtensionIso q E hobjects hmaps) (pointEval (A ⧸ I))
  let PA := ((pointEval A).mapHomologicalComplex (.up ℤ)).obj P
  let eComp : ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj PA ≅
      (((pointEval (A ⧸ I)).mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P)) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app P ≪≫
      (NatIso.mapHomologicalComplex eEval (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app P).symm
  have hb (i : ℤ) (hi : b < i) : IsZero
      ((((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj PA).homology i) := by
    have hz := (pointEval (A ⧸ I)).map_isZero (hEP i hi)
    let eh := ((pointEval (A ⧸ I)).mapHomologicalComplexHomologyIso (.up ℤ) i).app
      ((E.mapHomologicalComplex (.up ℤ)).obj P)
    exact (hz.of_iso eh).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso eComp)
  have hPA := ordinary_nilpotent_upper_bound I N hI PA
    (fun i ↦ pointEval_flat (P.X i) (hflat i)) (pointEval_kFlat P hP) b hb
  intro i hi
  have hz := (hPA i hi).of_iso
    (((pointEval A).mapHomologicalComplexHomologyIso (.up ℤ) i).app P).symm
  have hp0 := IsZero.of_full_of_faithful_of_isZero (pointEval A) (P.homology i) hz
  exact (hp0.of_iso ((homologyFunctorFactors _ i).app P)).of_iso
    ((homologyFunctor _ i).mapIso ePC).symm

end DerivedCategory

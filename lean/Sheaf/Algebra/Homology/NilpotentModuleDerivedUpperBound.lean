/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Homology.NilpotentDerivedUpperBound
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Nilpotent reduction detects upper bounds for ordinary modules

Source: Stacks Project, More on Algebra, Tag 0H75, upper-bound part used in Tag 09AR.
(blueprint: lem-weil-pbc-nilpotent-module-derived-upper-bound).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open CategoryTheory.Functor

namespace DerivedCategory

private noncomputable def pointLift {A : Type u} [CommRing A]
    (M N : RingSiteModules A)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ⟶ N where
  val :=
    { app := fun U ↦ by
        have hU : U = op ⟨PUnit.unit⟩ := by
          rcases U with ⟨⟨⟨⟩⟩⟩
          rfl
        rw [hU]
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU : U = op ⟨PUnit.unit⟩ := by
          rcases U with ⟨⟨⟨⟩⟩⟩
          rfl
        subst U
        have hV : V = op ⟨PUnit.unit⟩ := by
          rcases V with ⟨⟨⟨⟩⟩⟩
          rfl
        subst V
        have hi : i = 𝟙 _ := Subsingleton.elim _ _
        subst i
        ext x
        simp }

private def pointConstant {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    RingSiteModules A where
  val :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom (LinearMap.id : M →ₗ[A] M)
      map_id := by intro U; ext x; rfl
      map_comp := by intro U V W f g; ext x; rfl }
  isSheaf := Presheaf.isSheaf_bot _

private noncomputable def pointEquivalence (A : Type u) [CommRing A] :
    RingSiteModules A ≌ ModuleCat.{u} A := by
  let F := SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)
  have : F.Full := by
    constructor
    intro M N f
    exact ⟨pointLift M N f.hom, rfl⟩
  have : F.Faithful := by
    constructor
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    have hU : U = op ⟨PUnit.unit⟩ := by
      rcases U with ⟨⟨⟨⟩⟩⟩
      rfl
    subst U
    exact h
  have : F.EssSurj := ⟨fun M ↦ ⟨pointConstant M, ⟨(LinearEquiv.refl A M).toModuleIso⟩⟩⟩
  have : F.IsEquivalence := {}
  exact F.asEquivalence

private instance pointEquivalence_additive (A : Type u) [CommRing A] :
    (pointEquivalence A).functor.Additive := by
  constructor
  intro M N f g
  rfl

private noncomputable def pointExtensionIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hmaps : ∀ {M N : RingSiteModules A} (f : M ⟶ N),
      F.map f = eqToHom (hF M) ≫
        SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (hF N).symm) :
    (pointEquivalence A).functor ⋙ ModuleCat.extendScalars φ ≅
      F ⋙ (pointEquivalence B).functor := by
  letI := φ.toAlgebra
  let e (M : RingSiteModules A) :
      (ModuleCat.extendScalars φ).obj ((pointEquivalence A).functor.obj M) ≅
        (pointEquivalence B).functor.obj (F.obj M) := by
    let T := SheafOfModules.changeOfRingsPresheaf.{u} (ringSiteMap φ) M
    let η := toSheafify ⊥ T.presheaf
    have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
    let e : B ⊗[A] M.val.obj (op ⟨PUnit.unit⟩) →ₗ[B]
        (SheafOfModules.changeOfRings (ringSiteMap φ) M).val.obj (op ⟨PUnit.unit⟩) :=
      ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app
        (op ⟨PUnit.unit⟩) |>.hom
    exact (LinearEquiv.ofBijective e
      (ConcreteCategory.bijective_of_isIso (η.app (op ⟨PUnit.unit⟩)))).toModuleIso ≪≫
        (pointEquivalence B).functor.mapIso (eqToIso (hF M).symm)
  refine NatIso.ofComponents e ?_
  intro M N f
  dsimp only [Functor.comp_map]
  rw [hmaps f]
  let fT : SheafOfModules.changeOfRingsPresheaf.{u} (ringSiteMap φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u} (ringSiteMap φ) N :=
    { app := fun U ↦
        (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap φ) M f }
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.naturality fT
  have hp := congrArg (fun k ↦ k.app (op ⟨PUnit.unit⟩)) h
  let V := (pointEquivalence B).functor
  have heq : V.map (eqToHom (hF M).symm) ≫ V.map (eqToHom (hF M)) = 𝟙 _ := by
    rw [← V.map_comp]
    simp
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc, eqToIso.hom]
  rw [← Category.assoc (V.map (eqToHom (hF M).symm)) (V.map (eqToHom (hF M))) _,
    heq, Category.id_comp]
  ext x
  exact congrArg (fun y ↦ (V.map (eqToHom (hF N).symm)).hom y)
    (congrArg (fun k ↦ k.hom x) hp)

private noncomputable def homotopyEquivalence
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    HomotopyCategory C (ComplexShape.up ℤ) ≌
      HomotopyCategory D (ComplexShape.up ℤ) :=
  CategoryTheory.Equivalence.mk
    (e.functor.mapHomotopyCategory (ComplexShape.up ℤ))
    (e.inverse.mapHomotopyCategory (ComplexShape.up ℤ))
    ((Functor.mapHomotopyCategoryIdIso C _).symm ≪≫
      (Functor.mapHomotopyCategoryCompIso e.unitIso.symm _).symm)
    (Functor.mapHomotopyCategoryCompIso e.counitIso _ ≪≫
      Functor.mapHomotopyCategoryIdIso D _)

private noncomputable def scalarSquare
    {A B : Type u} {A' B' : Type (max u v)}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (a : A ≃+* A') (b : B ≃+* B')
    (φ : A →+* B) (φ' : A' →+* B')
    (h : φ.comp a.symm.toRingHom = b.symm.toRingHom.comp φ') :
    (ModuleCat.restrictScalars.{max u v} a.toRingHom) ⋙ ModuleCat.extendScalars φ ≅
      ModuleCat.extendScalars φ' ⋙ ModuleCat.restrictScalars b.toRingHom := by
  let EA : ModuleCat.{max u v} A' ≌ ModuleCat.{max u v} A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv a
  let EB : ModuleCat.{max u v} B' ≌ ModuleCat.{max u v} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv b
  let adj₁ := EA.toAdjunction.comp (ModuleCat.extendRestrictScalarsAdj.{max u v} φ)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').comp EB.toAdjunction
  let e : ModuleCat.restrictScalars.{max u v} φ ⋙ EA.inverse ≅
      EB.inverse ⋙ ModuleCat.restrictScalars.{max u v} φ' :=
    (ModuleCat.restrictScalarsComp a.symm.toRingHom φ).symm ≪≫
      eqToIso (congrArg ModuleCat.restrictScalars h) ≪≫
      ModuleCat.restrictScalarsComp φ' b.symm.toRingHom
  exact (conjugateIsoEquiv adj₂ adj₁).symm e.symm

private theorem kanPostcomposeEquiv
    {C D H H' : Type*} [Category* C] [Category* D] [Category* H] [Category* H']
    (Q : C ⥤ D) (G : C ⥤ H) (L : D ⥤ H) (ε : Q ⋙ L ⟶ G)
    [L.IsRightKanExtension ε] (F : H ⥤ H') [F.IsEquivalence] :
    (L ⋙ F).IsRightKanExtension
      ((Functor.associator _ _ _).inv ≫ whiskerRight ε F) := by
  let T := Functor.RightExtension.postcompose₂ Q G F
  have : T.IsEquivalence := by
    have h : IsIso (show (whiskeringLeft C D H).obj Q ⋙
        (whiskeringRight C H H').obj F ⟶
        (whiskeringRight D H H').obj F ⋙ (whiskeringLeft C D H').obj Q from
      { app _ := (Functor.associator _ _ _).inv }) := by
      apply NatIso.isIso_of_isIso_app
    apply CostructuredArrow.isEquivalenceMap₂
  have h := (IsTerminal.isTerminalIffObj T (Functor.RightExtension.mk L ε)).1
    (Functor.isUniversalOfIsRightKanExtension L ε)
  exact ⟨⟨IsTerminal.ofIso h (Functor.RightExtension.postcompose₂ObjMkIso F ε)⟩⟩

private theorem derivedComparison
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (eA : C ≌ C') (eB : D ≌ D')
    [eA.functor.Additive] [eA.inverse.Additive]
    [eB.functor.Additive] [eB.inverse.Additive]
    (E : C ⥤ D) (E' : C' ⥤ D') [E.Additive] [E'.Additive]
    (e : eA.functor ⋙ E' ≅ E ⋙ eB.functor)
    (L : DerivedCategory C' ⥤ DerivedCategory D')
    (ε : Qh ⋙ L ⟶ E'.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    [L.IsRightKanExtension ε]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (α : Qh ⋙ LF ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    [LF.IsRightKanExtension α] :
    Nonempty (eA.functor.mapDerivedCategory ⋙ L ≅
      LF ⋙ eB.functor.mapDerivedCategory) := by
  let HA := (homotopyEquivalence eA).functor
  let DA := eA.functor.mapDerivedCategory
  let DB := eB.functor.mapDerivedCategory
  let β : (HA ⋙ Qh) ⋙ L ⟶ HA ⋙ (E'.mapHomotopyCategory (.up ℤ) ⋙ Qh) :=
    (Functor.associator _ _ _).hom ≫ whiskerLeft HA ε
  have hβ : L.IsRightKanExtension β :=
    (Functor.isRightKanExtension_iff_precomp L HA ε).1 inferInstance
  let γ : Qh ⋙ (DA ⋙ L) ⟶ HA ⋙ (E'.mapHomotopyCategory (.up ℤ) ⋙ Qh) :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight eA.functor.mapDerivedCategoryFactorsh.hom L ≫ β
  have hγ : (DA ⋙ L).IsRightKanExtension γ :=
    (Functor.isRightKanExtension_iff_postcomp₁ DA
      eA.functor.mapDerivedCategoryFactorsh β).1 hβ
  let δ : Qh ⋙ (LF ⋙ DB) ⟶ (E.mapHomotopyCategory (.up ℤ) ⋙ Qh) ⋙ DB :=
    (Functor.associator _ _ _).inv ≫ whiskerRight α DB
  have hδ : (LF ⋙ DB).IsRightKanExtension δ := kanPostcomposeEquiv Qh _ LF α DB
  let eH : HA ⋙ E'.mapHomotopyCategory (.up ℤ) ≅
      E.mapHomotopyCategory (.up ℤ) ⋙ eB.functor.mapHomotopyCategory (.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl _) _ ≪≫
      { hom := NatTrans.mapHomotopyCategory e.hom _
        inv := NatTrans.mapHomotopyCategory e.inv _
        hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
        inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp } ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm
  let eG : HA ⋙ (E'.mapHomotopyCategory (.up ℤ) ⋙ Qh) ≅
      (E.mapHomotopyCategory (.up ℤ) ⋙ Qh) ⋙ DB :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eH Qh ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ eB.functor.mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator _ _ _).symm
  have : (DA ⋙ L).IsRightKanExtension (γ ≫ eG.hom) :=
    (Functor.isRightKanExtension_iff_of_iso₂ γ (γ ≫ eG.hom)
      eG (Iso.refl _) (by simp)).1 hγ
  exact ⟨Functor.rightKanExtensionUnique (DA ⋙ L) (γ ≫ eG.hom) (LF ⋙ DB) δ⟩

/-- Nilpotent derived reduction detects the same upper cohomological bound in the
ordinary module category, including a larger universe of module carriers.
Source: Stacks Project, Tag 0H75, upper-bound filtration argument used by Tag 09AR.
(blueprint: lem-weil-pbc-nilpotent-module-derived-upper-bound).

Proof:
1. Set A' = ULift A in the module-carrier universe and J = a(I), where a : A ≃+* A'
   is the lift ring isomorphism. Mapping powers proves J^N = 0. The quotient ring
   isomorphism q : A/I ≃+* A'/J sends the class of x to the class of a(x).
2. Evaluation on the unique object is an exact additive equivalence from RingSiteModules
   A' to ordinary A'-modules. Its inverse sends a module to the constant presheaf; every
   presheaf is a sheaf for the bottom topology. The scalar-extension presheaf evaluates
   to B tensor_A M. Its sheafification unit is invertible and natural, so evaluation
   intertwines site scalar extension and ordinary scalar extension. Composing evaluation
   with restriction along a and q gives equivalences eA and eB with the original ordinary
   module categories. The remaining scalar-extension square follows by taking adjunction
   mates of the restriction-of-scalars identity induced by q(mk(x)) = mk(a(x)).
3. Use standard derived categories for the two sites; their hom universes agree. The
   ordinary derived categories retain the independently specified hom universes w and w'.
   Precompose the right Kan extension defining L by the homotopy equivalence induced by
   eA. The factorization Qh composed with D(eA) identifies its localization functor with
   the site localization. Postcompose the site's left derived pair by D(eB): this preserves
   its universal property because postcomposition induces an equivalence of categories
   of right extensions. The natural scalar-extension square identifies the two functors
   being derived. Uniqueness of right Kan extensions therefore gives
   D(eA) composed with L isomorphic to LF composed with D(eB).
4. Take C' to be the inverse image of C under D(eA). The comparison from step 3 and the
   counit isomorphism D(eA)(C') ≅ C identify D(eB)(LF(C')) with L(C). Exact functors
   commute with cohomology, and eB and its inverse preserve zero objects, so hred gives
   vanishing above b for LF(C'). Apply lem-weil-pbc-nilpotent-derived-upper-bound to J,
   N, LF, and C'. Apply eA to its cohomology vanishing and use the same cohomology
   comparison and counit to obtain the conclusion for C. No bound below, finiteness, or
   nonzero-ring hypothesis enters this construction; I = 0 and the zero ring are included. -/
theorem isZero_homology_of_nilpotent_module_reduction
    (A : Type u) [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ)
    (hred : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{max u v} (A ⧸ I)) i).obj (L.obj C))) :
    ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{max u v} A) i).obj C) := by
  classical
  let A' := ULift.{v} A
  let a : A ≃+* A' := ULift.ringEquiv.symm
  let J : Ideal A' := I.map a.toRingHom
  have hJ : J ^ N = ⊥ := by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let bq : (A ⧸ I) ≃+* (A' ⧸ J) := Ideal.quotientEquiv I J a rfl
  let : HasDerivedCategory.{(max u v) + 1} (RingSiteModules A') :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{(max u v) + 1} (RingSiteModules (A' ⧸ J)) :=
    HasDerivedCategory.standard _
  let RA : ModuleCat.{max u v} A' ≌ ModuleCat.{max u v} A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv a
  let RB : ModuleCat.{max u v} (A' ⧸ J) ≌ ModuleCat.{max u v} (A ⧸ I) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv bq
  let eA := (pointEquivalence A').trans RA
  let eB := (pointEquivalence (A' ⧸ J)).trans RB
  have : eA.functor.Additive := by
    change ((pointEquivalence A').functor ⋙ RA.functor).Additive
    infer_instance
  have : eB.functor.Additive := by
    change ((pointEquivalence (A' ⧸ J)).functor ⋙ RB.functor).Additive
    infer_instance
  obtain ⟨E, hobjects, hmaps, hE, _, _, LF, α, hLF, _, _⟩ :=
    SheafOfModules.derivedChangeOfRings (ringSiteMap (Ideal.Quotient.mk J))
  let := hE
  let : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  let : (ModuleCat.extendScalars.{max u v, max u v, max u v}
      (Ideal.Quotient.mk J)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk J)).left_adjoint_additive
  let sq := scalarSquare a bq (Ideal.Quotient.mk I) (Ideal.Quotient.mk J)
    (by apply RingHom.ext; intro x; rfl)
  let e : eA.functor ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
      E ⋙ eB.functor :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ sq ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (pointExtensionIso (Ideal.Quotient.mk J) E hobjects hmaps) RB.functor ≪≫
      Functor.associator _ _ _
  have : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  let := hLF
  have : LF.IsRightKanExtension α :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LF α
      (HomotopyCategory.quasiIso (RingSiteModules A') (.up ℤ))
  obtain ⟨comparison⟩ := derivedComparison eA eB E _ e L ε LF α
  let DA := eA.mapDerivedCategory
  let DB := eB.mapDerivedCategory
  let C' := DA.inverse.obj C
  have hred' : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (RingSiteModules (A' ⧸ J)) i).obj (LF.obj C')) := by
    intro i hi
    let t : DB.functor.obj (LF.obj C') ≅ L.obj C :=
      (comparison.app C').symm ≪≫ L.mapIso (DA.counitIso.app C)
    have hz := (hred i hi).of_iso
      ((homologyFunctor (ModuleCat.{max u v} (A ⧸ I)) i).mapIso t)
    have hz' := hz.of_iso
      ((Functor.mapDerivedCategoryHomologyFunctorIso eB.functor i).app (LF.obj C'))
    exact (eB.inverse.map_isZero hz').of_iso (eB.unitIso.app _)
  have hvan := isZero_homology_of_nilpotent_derived_reduction J N hN hJ
    E hobjects hmaps LF α hLF C' b hred'
  intro i hi
  exact (eA.functor.map_isZero (hvan i hi)).of_iso
    (((Functor.mapDerivedCategoryHomologyFunctorIso eA.functor i).app C') ≪≫
      (homologyFunctor (ModuleCat.{max u v} A) i).mapIso (DA.counitIso.app C)).symm

end DerivedCategory

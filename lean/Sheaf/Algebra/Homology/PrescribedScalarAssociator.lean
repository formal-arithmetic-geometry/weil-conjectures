/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! # Associativity for prescribed scalar presentations

Source: Stacks Tags 06YY and 07A6; blueprint Proof (3).
(blueprint: lem-pur-prescribed-scalar-associator).

The presentations are supplied, so the comparison retains their actual universal counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient
namespace WeilConjectures.CompletedScalarAssociator

private def chosenPresentation
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (h : type_of% (SheafOfModules.derivedChangeOfRingsIndependentCoefficients a)) :
    Presentation a :=
  { ordinary := h.choose
    obj_eq := h.choose_spec.choose
    map_eq := h.choose_spec.choose_spec.choose
    additive := h.choose_spec.choose_spec.choose_spec.choose
    derived := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
    counit := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
    universal := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1 }

private def scalarPresentation
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) : Presentation a :=
  chosenPresentation a (SheafOfModules.derivedChangeOfRingsIndependentCoefficients a)

attribute [local irreducible] chosenPresentation

private theorem scalarCompData
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (hc : a ≫ b = c) :
    ∃ (o : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
      (d : (p a).derived ⋙ (p b).derived ≅ (p c).derived),
      (∀ M U s t x, (o.hom.app M).val.app U
        (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
        sectionTensor (p c) M U (t * b.hom.app U s) x) ∧
      (∀ P : CochainComplex (Modules R) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) ≫
            (p c).counit.app ((HomotopyCategory.quotient _ _).obj P) =
          (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
            (p b).counit.app ((HomotopyCategory.quotient _ _).obj
              (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) := by
  subst c
  let D := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦
    Classical.choice (adjData_exists (p a))
  let A := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦ (D a).ordinary
  refine ⟨ordinaryComp p A a b, derivedComp p D a b, ?_, ?_⟩
  · intro M U s t x
    simpa only [mul_comm] using
      ordinaryComp_hom p A (fun a ↦ (D a).ordinary_unit) a b M U x s t
  · intro P
    exact derivedComp_representative p D a b ((HomotopyCategory.quotient _ _).obj P)

private theorem scalarComp_unique
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (o o' : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
    (ho : ∀ M U s t x, (o.hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p c) M U (t * b.hom.app U s) x)
    (ho' : ∀ M U s t x, (o'.hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p c) M U (t * b.hom.app U s) x) : o = o' := by
  let D := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦
    Classical.choice (adjData_exists (p a))
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((D b).ordinary.homEquiv _ _).injective
  apply ((D a).ordinary.homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (o.hom.app M).val.app U
      (((D b).ordinary.unit.app _).val.app U
        (((D a).ordinary.unit.app M).val.app U x)) =
    (o'.hom.app M).val.app U
      (((D b).ordinary.unit.app _).val.app U
        (((D a).ordinary.unit.app M).val.app U x))
  simp only [(D a).ordinary_unit, (D b).ordinary_unit]
  exact (ho M U 1 1 x).trans (ho' M U 1 1 x).symm

private structure ScalarComposition
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S T : Sheaf J CommRingCat.{u}} {a : R ⟶ S} {b : S ⟶ T} {c : R ⟶ T}
    (pa : Presentation a) (pb : Presentation b) (pc : Presentation c) where
  ordinary : pa.ordinary ⋙ pb.ordinary ≅ pc.ordinary
  derived : pa.derived ⋙ pb.derived ≅ pc.derived
  tensor : ∀ M U s t x, (ordinary.hom.app M).val.app U
    (sectionTensor pb (pa.ordinary.obj M) U t (sectionTensor pa M U s x)) =
    sectionTensor pc M U (t * b.hom.app U s) x
  representative : ∀ P : CochainComplex (Modules R) ℤ,
    @Eq ((pb.derived.obj (pa.derived.obj (DerivedCategory.Q.obj P))) ⟶
      DerivedCategory.Q.obj ((pc.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
      (pb.derived.map (pa.counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        pb.counit.app ((HomotopyCategory.quotient _ _).obj
          ((pa.ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P))
      (derived.hom.app (DerivedCategory.Q.obj P) ≫
        pc.counit.app ((HomotopyCategory.quotient _ _).obj P))
  unique : ∀ (o : pa.ordinary ⋙ pb.ordinary ≅ pc.ordinary),
    (∀ M U s t x, (o.hom.app M).val.app U
      (sectionTensor pb (pa.ordinary.obj M) U t (sectionTensor pa M U s x)) =
      sectionTensor pc M U (t * b.hom.app U s) x) → o = ordinary

private theorem scalarCompositionData
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hc : a ≫ b = c) : Nonempty (ScalarComposition (p a) (p b) (p c)) := by
  obtain ⟨o, d, ho, hd⟩ := scalarCompData p a b c hc
  exact ⟨{
    ordinary := o
    derived := d
    tensor := ho
    representative := fun P ↦ (hd P).symm
    unique := fun o' ho' ↦ scalarComp_unique p a b c o' o ho' ho }⟩

/-- Prescribed ordinary and derived presentations admit their normalized associator.
Source: Stacks Tags 06YY and 07A6 (blueprint: lem-pur-prescribed-scalar-associator).
Proof: take the extension-restriction adjunction for each prescribed presentation.
Compose the ordinary adjunctions and their derived adjunctions, then use uniqueness
of left adjoints. The ordinary units insert one, so their comparison multiplies the
two scalar factors. The derived adjunction hom-comparison gives the displayed
universal-counit equation. Finally apply the two injective ordinary hom-equivalences:
the tensor formula at the two units determines every component uniquely. -/
theorem presentation_associator_exists
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hc : a ≫ b = c) :
    ∃ (o : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
      (d : (p a).derived ⋙ (p b).derived ≅ (p c).derived),
      (∀ M U s t x, (o.hom.app M).val.app U
        (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
        sectionTensor (p c) M U (t * b.hom.app U s) x) ∧
      (∀ P : CochainComplex (Modules R) ℤ,
        (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (p b).counit.app ((HomotopyCategory.quotient _ _).obj
            (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P) =
        d.hom.app (DerivedCategory.Q.obj P) ≫
          (p c).counit.app ((HomotopyCategory.quotient _ _).obj P)) ∧
      (∀ (o' : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary),
        (∀ M U s t x, (o'.hom.app M).val.app U
          (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
          sectionTensor (p c) M U (t * b.hom.app U s) x) → o' = o) := by
  obtain ⟨v⟩ := scalarCompositionData p a b c hc
  exact ⟨v.ordinary, v.derived, v.tensor, v.representative, v.unique⟩

end WeilConjectures.CompletedScalarAssociator

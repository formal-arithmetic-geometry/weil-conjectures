/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.TraceFormula.TwoTermPerfectDeterminantData
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence

/-! # Section-normalized coherence of the recorded derived pullback

Source: Stacks Project, Tags 0097 and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

omit d in
private theorem sectionAdjunction_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullbackSectionAdjunction g =
      Classical.choose (exists_tensorPullbackAdjunction g) := by
  classical
  apply ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).2
    (Classical.choose (exists_tensorPullbackAdjunction g)) ?_).symm
  intro M U m
  exact Classical.choose_spec (exists_tensorPullbackAdjunction g) M (Opposite.op U) m

omit d in
private theorem leftAdjointUniq_changeRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).symm =
      (conjugateIsoEquiv a b).symm e.symm := by
  apply Iso.ext
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

omit d in
private theorem sectionComp_eq {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X) :
    (tensorPullbackSectionComp h g).symm =
      (conjugateIsoEquiv
        (Classical.choose (exists_tensorPullbackAdjunction (h ≫ g)))
        ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (exists_tensorPullbackAdjunction h)))).symm
        (pushforwardComp h g).symm := by
  unfold tensorPullbackSectionComp
  rw [sectionAdjunction_eq, sectionAdjunction_eq, sectionAdjunction_eq]
  exact leftAdjointUniq_changeRight _ _ _

private theorem sectionLift_eq_recorded {X Y Z : Scheme.{u}} (h : Z ⟶ Y)
    (g : Y ⟶ X) :
    twoTermDeterminantDerivedCompositionLift h g =
      recordedDerivedPullbackCompositionLift h g := by
  unfold twoTermDeterminantDerivedCompositionLift recordedDerivedPullbackCompositionLift
  rw [sectionComp_eq]

/-- Coherent comparisons for the retained derived pullback, with composition pinned
by the normalized original counits. Source: Stacks Project, Tag 0D5S
(blueprint: lem-trf-two-term-determinant-pullback-coherence). -/
structure TwoTermDeterminantPullbackCoherence where
  derivedId : ∀ X : Scheme.{u}, derivedPullback (𝟙 X) ≅ 𝟭 (schemeDerivedCategory X)
  derivedComp : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X),
      derivedPullback g ⋙ derivedPullback h ≅ derivedPullback (h ≫ g)
  composition_normalization : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X),
        (derivedComp h g).hom = twoTermDeterminantDerivedCompositionLift h g
  left_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        derivedComp (𝟙 X) f ≪≫
          eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.id_comp f)) =
          Functor.isoWhiskerLeft (derivedPullback f) (derivedId X) ≪≫
            Functor.rightUnitor (derivedPullback f)
  right_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        derivedComp f (𝟙 Y) ≪≫
          eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.comp_id f)) =
          Functor.isoWhiskerRight (derivedId Y) (derivedPullback f) ≪≫
            Functor.leftUnitor (derivedPullback f)
  associativity : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
        Functor.isoWhiskerRight (derivedComp f g) (derivedPullback h) ≪≫ derivedComp h (f ≫ g) =
          Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
            Functor.isoWhiskerLeft (derivedPullback g) (derivedComp h f) ≪≫ derivedComp (h ≫ f) g ≪≫
              eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k) (Category.assoc h f g))

/-- The recorded derived pullbacks, with section-normalized composition, admit a
normalized identity and all coherence laws. Source: Stacks Project, Tag 0D5S
(blueprint: lem-trf-two-term-determinant-pullback-coherence).

Proof: the upstream and section-normalized adjunctions have the same unit on sections,
so uniqueness identifies them. Their mates of the pushforward comparison agree.
Consequently the normalized universal lift is the recorded composition lift. It is
invertible by the retained K-flat counits. Apply the proved coherence theorem to these
same counits; its left unit law at the identity is precisely the required normalization.
The argument also supplies the other unit law and associativity. -/
theorem exists_twoTermDeterminantPullbackCoherence :
    Nonempty (TwoTermDeterminantPullbackCoherence.{u, w}) := by
  let a : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (tensorPullback f).Additive :=
    fun f ↦ by
      rw [← recordedPullbackData_E f]
      exact recordedPullbackData_additive f
  let c := @recordedDerivedPullbackComposition.{u, w} d
  obtain ⟨i, hleft, hright, hassoc⟩ := derivedPullbackComposition_coherence a
    (fun f ↦ recordedDerivedPullbackCounit f)
    (fun f ↦ recordedDerivedPullbackCounit_universal f)
    (fun f P hP ↦ recordedDerivedPullbackCounit_kFlat f P hP) c
    (fun _ _ ↦ rfl)
  refine ⟨⟨i, c, ?_, hleft, hright, hassoc⟩⟩
  intro X Y Z h g
  exact (sectionLift_eq_recorded h g).symm

end AlgebraicGeometry

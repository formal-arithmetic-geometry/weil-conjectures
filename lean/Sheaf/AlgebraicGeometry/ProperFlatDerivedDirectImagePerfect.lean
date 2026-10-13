/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups S2 and S1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed

/-! # Perfect direct image for proper flat finitely presented morphisms

Source: Stacks Project, Tag 0B91, Lemma 36.30.4(1).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Localization uniqueness transports isomorphisms between the images of two complexes. -/
private theorem iso_Q_transport
    {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    (h₁ : HasDerivedCategory.{wX} C) (h₂ : HasDerivedCategory.{wY} C)
    (K L : CochainComplex C ℤ)
    (e : Nonempty ((@DerivedCategory.Q C _ _ h₁).obj K ≅
      (@DerivedCategory.Q C _ _ h₁).obj L)) :
    Nonempty ((@DerivedCategory.Q C _ _ h₂).obj K ≅
      (@DerivedCategory.Q C _ _ h₂).obj L) := by
  let Q₁ := @DerivedCategory.Q C _ _ h₁
  let Q₂ := @DerivedCategory.Q C _ _ h₂
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let F := (Localization.uniq Q₁ Q₂ W).functor
  let c := Localization.compUniqFunctor Q₁ Q₂ W
  obtain ⟨e⟩ := e
  exact ⟨(c.app K).symm ≪≫ F.mapIso e ≪≫ c.app L⟩

/-- Transport each local strictly perfect representative along a derived isomorphism. -/
private theorem perfect_of_iso (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (h : Scheme.IsPerfect X E) :
    Scheme.IsPerfect X F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨c⟩⟩ := h x
  exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm ≪≫ c⟩⟩

/-- Exact restriction and localization uniqueness preserve perfectness of a fixed complex. -/
private theorem perfect_Q_transport (X : Scheme.{u})
    (h₁ : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (h₂ : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (ho₁ : ∀ U : X.Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (ho₂ : ∀ U : X.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (h : @Scheme.IsPerfect X h₁ ho₁ ((@DerivedCategory.Q _ _ _ h₁).obj K)) :
    @Scheme.IsPerfect X h₂ ho₂ ((@DerivedCategory.Q _ _ _ h₂).obj K) := by
  intro x
  obtain ⟨U, hx, L, hL, ⟨e⟩⟩ := h x
  let F := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
  let c₁ := @Functor.mapDerivedCategoryFactors _ _ _ h₁ _ _ _ (ho₁ U) F _ _ _
  let c₂ := @Functor.mapDerivedCategoryFactors _ _ _ h₂ _ _ _ (ho₂ U) F _ _ _
  obtain ⟨e'⟩ := iso_Q_transport (ho₁ U) (ho₂ U)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) L ⟨(c₁.app K).symm ≪≫ e⟩
  exact ⟨U, hx, L, hL, ⟨c₂.app K ≪≫ e'⟩⟩

/-- A zero module is the free module with no generators, hence finitely presented.
Source: Stacks Project, Tag 01B5; the finite locally free presentation in the source library. -/
private theorem isFinitePresentation_of_isZero (X : Scheme.{u})
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hN : CategoryTheory.Limits.IsZero N) :
    N.IsFinitePresentation := by
  let M := SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}
  have hz : CategoryTheory.Limits.IsZero M :=
    (CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mpr (by
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      exact i.elim)
  let q : M.LocalGeneratorsData :=
    (SheafOfModules.free.generatingSections
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite PEmpty.{u + 1}
    infer_instance
  have : M.IsFiniteLocallyFree := by
    constructor
    exact ⟨q, hq, hf⟩
  have : N.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (hz.iso hN)
  infer_instance

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Apply Stacks Tag 0A1H with the structure sheaf in degree zero, then the right unitor. -/
private theorem properFlat_common_perfect
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj E) := by
  classical
  let : Zero (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.HasZeroObject.zero' (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let OX := SheafOfModules.unit X.ringCatSheaf
  have : SheafOfModules.IsInvertible.{u, u, u} OX := by
    dsimp [OX]
    infer_instance
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} OX := inferInstance
  have : OX.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation OX
  let G := (HomologicalComplex.single
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ) 0).obj OX
  have hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      CategoryTheory.Limits.IsZero (G.X n) := by
    refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hGfp : ∀ n : ℤ, (G.X n).IsFinitePresentation := by
    intro n
    dsimp [G, HomologicalComplex.single]
    split_ifs
    · infer_instance
    · exact isFinitePresentation_of_isZero X _ (CategoryTheory.Limits.isZero_zero _)
  have hGflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (G.X n) f := by
    intro n
    dsimp [G, HomologicalComplex.single]
    split_ifs
    · exact Scheme.Modules.isFlatOver_of_isInvertible f OX
    · intro V U e
      let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation _ (Opposite.op U.1)
      have hz := Functor.map_isZero F
        (CategoryTheory.Limits.isZero_zero (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      have : Subsingleton (F.obj
          (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
        ModuleCat.subsingleton_of_isZero hz
      let : Module Γ(Y, V.1) (F.obj
          (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
        Module.compHom _ (f.appLE V.1 U.1 e).hom
      change Module.Flat Γ(Y, V.1) (F.obj
        (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      infer_instance
  have hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n) := by
    intro n
    have hc := (Scheme.Modules.finite_type_module_support_closed X (G.X n)).2.2.2
    refine ⟨⟨_, hc⟩, rfl, ?_⟩
    change IsProper (_ ≫ f)
    infer_instance
  have hp := (properSupport_perfect_directImage f E hE G hGb hGflat hGproper).1
  let eG : DerivedCategory.Q.obj G ≅
      MonoidalCategory.tensorUnit (schemeDerivedCategory X) :=
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app OX).symm
  let e : MonoidalCategory.tensorObj E (DerivedCategory.Q.obj G) ≅ E :=
    MonoidalCategory.tensorIso (Iso.refl E) eG ≪≫ MonoidalCategory.rightUnitor E
  exact perfect_of_iso Y ((schemeDerivedDirectImage f).mapIso e) hp

/-- Proper flat finitely presented pushforward takes perfect complexes to perfect complexes.
Source: Stacks Project, Tag 0B91, Lemma 36.30.4(1), deduced from Tag 0A1H.
(blueprint: lem-sc-proper-flat-derived-direct-image-perfect-universes).

Proof: Choose a complex K representing the supplied E via essential surjectivity of Q.
Transfer its local strictly perfect representatives to the standard localization in Hom
universe u+1. On each open the exact-restriction comparison identifies the restriction
of QK with Q of the termwise restriction of K; uniqueness of localization transports
its isomorphism to the same strictly perfect complex.
In these standard models apply properSupport_perfect_directImage to QK and O_X in degree
zero. The latter is bounded. Its terms are finitely presented, including the zero terms,
which are free of rank zero. Flatness of f makes O_X relatively flat; zero terms are
flat because their sections are subsingleton. Finite-type quasi-coherent modules have
closed support; the corresponding reduced closed immersion followed by f is proper.
The single-complex comparison identifies Q(O_X[0]) with the derived tensor unit, and the
right unitor identifies QK tensor Q(O_X[0]) with QK.
Both the standard and supplied direct images of K are represented by the very same
complex J = f_*I(K), using derivedModuleDirectImageFactorization. Transport perfectness
of QJ back to the supplied localization and its supplied open localizations, then along
the direct-image comparison to Rf_*E. No new geometric hypothesis or derived model is
assumed. Empty schemes and zero E are covered by the same witnesses and isomorphisms. -/
theorem properFlat_derivedDirectImage_perfect
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj E) := by
  classical
  let CX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let CY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let hX : HasDerivedCategory.{wX} CX := inferInstance
  let hY : HasDerivedCategory.{wY} CY := inferInstance
  let hoX : ∀ U : X.Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance
  let hoY : ∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) := inferInstance
  let QX : CochainComplex CX ℤ ⥤ DerivedCategory CX := DerivedCategory.Q
  let K := QX.objPreimage E
  let eK : QX.obj K ≅ E := QX.objObjPreimageIso E
  have hK : Scheme.IsPerfect X (QX.obj K) := perfect_of_iso X eK.symm hE
  let hStd : ∀ Z : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun Z ↦ HasDerivedCategory.standard _
  let hoStd : ∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U)) :=
    fun Z U ↦ HasDerivedCategory.standard _
  let QXs : CochainComplex CX ℤ ⥤ DerivedCategory CX := DerivedCategory.Q
  let QYs : CochainComplex CY ℤ ⥤ DerivedCategory CY := DerivedCategory.Q
  have hKs : Scheme.IsPerfect X (QXs.obj K) :=
    perfect_Q_transport X hX (hStd X) hoX (hoStd X) K hK
  let Ds := schemeDerivedDirectImage f
  have hp := properFlat_common_perfect f (QXs.obj K) hKs
  let J : CochainComplex CY ℤ :=
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((CochainComplex.kInjectiveResolutionFunctor.{u} CX).obj K)
  let es : Ds.obj (QXs.obj K) ≅ QYs.obj J :=
    (Classical.choice (RingedSpace.derivedModuleDirectImageFactorization
      f.toLRSHom.toShHom)).app K
  have hJs : Scheme.IsPerfect Y (QYs.obj J) := perfect_of_iso Y es hp
  have hJ : @Scheme.IsPerfect Y hY hoY ((@DerivedCategory.Q _ _ _ hY).obj J) :=
    perfect_Q_transport Y (hStd Y) hY (hoStd Y) hoY J hJs
  let D := @schemeDerivedDirectImage X Y hX hY f
  let eD : D.obj E ≅ (@DerivedCategory.Q _ _ _ hY).obj J := D.mapIso eK.symm ≪≫
    (Classical.choice (@RingedSpace.derivedModuleDirectImageFactorization
      X.toRingedSpace Y.toRingedSpace hX hY f.toLRSHom.toShHom)).app K
  exact @perfect_of_iso Y hY hoY _ _ eD.symm hJ

end AlgebraicGeometry

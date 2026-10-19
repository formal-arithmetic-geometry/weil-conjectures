/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.FieldDerivedScalarTower
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.InducedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.LinearAlgebra.Dual.Lemmas
import Sheaf.Paper.PointFdMorphismDescent

/-! # The category of finite-stage coefficient complexes

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: def-weil-point-fd-qlbar-category).

Objects are literally pairs (finite coefficient field, finite-dimensional derived complex).
We realize their morphism colimits as morphisms between their scalar extensions in D(Qbar).
The common-stage bijection is `pointFdQbarCocone_isFilteredTwoColimit`, not an assumption.
This gives the same category up to its canonical identity-on-objects isomorphism.

## Main definitions and statements

* `PointFdQbar`: the finite-stage pairs with their canonical Hom realization.
* `pointFdQbarCocone_isFilteredTwoColimit`: the common-stage Hom colimit characterization.
* `pointFdQbarHasShift`, `pointFdQbarDistinguished`: the specified shifts and triangles.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension is faithful even before imposing finite-dimensionality.
Choose a linear functional on the extension field taking 1 to 1. Applying that
functional to the scalar tensor factor retracts the extension/restriction unit.
Termwise application and localization retain this natural retraction, which
detects equality of derived morphisms. Source: the tensor adjunction and
`Module.Projective.exists_dual_eq_one` in Mathlib. -/
private theorem fieldScalarExtension_faithful {K L : Type u} [Field K] [Field L] (f : K →+* L) :
    (fieldDerivedScalarExtension f).Faithful := by
  classical
  let F := ModuleCat.extendScalars.{u, u, u} f
  let R := ModuleCat.restrictScalars.{u} f
  let W := R.obj (ModuleCat.of L L)
  obtain ⟨p, hp⟩ := Module.Projective.exists_dual_eq_one K
    (show (show W from (1 : L)) ≠ 0 from (show (1 : L) ≠ 0 from one_ne_zero))
  let ρ : F ⋙ R ⟶ 𝟭 (ModuleCat.{u} K) :=
    { app := fun M ↦ ModuleCat.ofHom (X := R.obj (F.obj M)) (Y := M)
        { toFun := fun z ↦ (TensorProduct.lid K M) ((p.rTensor M) z)
          map_add' := by intros; simp
          map_smul' := by
            intro r z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul x y =>
              change (TensorProduct.lid K M)
                ((p.rTensor M) ((f r * (show L from x)) ⊗ₜ[K] y)) = _
              have hp' : p (f r * (show L from x)) = r * p x := by
                exact p.map_smul r x
              simp [hp', mul_smul]
            | add x y hx hy => simp_all [smul_add] }
      naturality := by
        intro M N g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change (TensorProduct.lid K N) ((p.rTensor N) (x ⊗ₜ[K] g y)) =
          g ((TensorProduct.lid K M) ((p.rTensor M) (x ⊗ₜ[K] y)))
        simp }
  have hρ : (ModuleCat.extendRestrictScalarsAdj f).unit ≫ ρ = 𝟙 _ := by
    ext M m
    change (TensorProduct.lid K M) ((p.rTensor M) ((show W from (1 : L)) ⊗ₜ[K] m)) = m
    simp [hp]
  let ηc : 𝟭 (CochainComplex (ModuleCat.{u} K) ℤ) ⟶
      (F ⋙ R).mapHomologicalComplex (.up ℤ) :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (.up ℤ)).inv ≫
      NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj f).unit (.up ℤ)
  let ρc : (F ⋙ R).mapHomologicalComplex (.up ℤ) ⟶
      𝟭 (CochainComplex (ModuleCat.{u} K) ℤ) :=
    NatTrans.mapHomologicalComplex ρ (.up ℤ) ≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (.up ℤ)).hom
  have hc : ηc ≫ ρc = 𝟙 _ := by
    apply NatTrans.ext
    funext M
    apply HomologicalComplex.Hom.ext
    funext i
    exact congrArg (fun t ↦ t.app (M.X i)) hρ
  let ηd : 𝟭 (DerivedCategory (ModuleCat.{u} K)) ⟶ (F ⋙ R).mapDerivedCategory :=
    Localization.liftNatTrans Q (HomologicalComplex.quasiIso _ (.up ℤ))
      Q ((F ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ Q)
      (𝟭 _) (F ⋙ R).mapDerivedCategory (Functor.whiskerRight ηc Q)
  let ρd : (F ⋙ R).mapDerivedCategory ⟶ 𝟭 (DerivedCategory (ModuleCat.{u} K)) :=
    Localization.liftNatTrans Q (HomologicalComplex.quasiIso _ (.up ℤ))
      ((F ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ Q) Q
      (F ⋙ R).mapDerivedCategory (𝟭 _) (Functor.whiskerRight ρc Q)
  have hd : ηd ≫ ρd = 𝟙 _ := by
    dsimp only [ηd, ρd]
    rw [Localization.comp_liftNatTrans]
    have hh : Functor.whiskerRight ηc Q ≫ Functor.whiskerRight ρc Q = 𝟙 Q := by
      rw [← Functor.whiskerRight_comp, hc]
      ext X
      simp
    rw [hh, Localization.liftNatTrans_id]
  have hfaith : (F ⋙ R).mapDerivedCategory.Faithful := by
    constructor
    intro X Y a b hab
    have hnat := ηd.naturality a
    have hnat' := ηd.naturality b
    have hsplit : ηd.app Y ≫ ρd.app Y = 𝟙 Y := congr_app hd Y
    dsimp only [Functor.id_map] at hnat hnat'
    calc
      a = a ≫ ηd.app Y ≫ ρd.app Y := by rw [hsplit]; simp
      _ = ηd.app X ≫ ((F ⋙ R).mapDerivedCategory).map a ≫ ρd.app Y := by
        rw [← Category.assoc, hnat, Category.assoc]
      _ = ηd.app X ≫ ((F ⋙ R).mapDerivedCategory).map b ≫ ρd.app Y := by rw [hab]
      _ = b := by rw [← Category.assoc, ← hnat', Category.assoc, hsplit]; simp
  have hcomp : (F.mapDerivedCategory ⋙ R.mapDerivedCategory).Faithful :=
    Functor.Faithful.of_iso (Functor.mapDerivedCategoryCompIso F R)
  exact Functor.Faithful.of_comp F.mapDerivedCategory R.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The finite-stage pairs before equipping them with morphisms.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
def PointFdQbarObjects :=
  Σ E : Padic.FiniteCoefficientFields l Ω,
    (pointFiniteDimensional E.val).FullSubcategory

/-- The canonical realization of a finite-stage object, by actual scalar extension.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarObject (X : PointFdQbarObjects l Ω) :
    DerivedCategory (ModuleCat.{u} Ω) :=
  (fieldDerivedScalarExtension (K := X.1.val) (L := Ω) X.1.val.subtype).obj X.2.obj

/-- A concrete realization of the common-stage category. Its Hom is canonically the
filtered common-stage colimit, as specified by the cocone theorem below.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
abbrev PointFdQbar :=
  InducedCategory (DerivedCategory (ModuleCat.{u} Ω)) (pointFdQbarObject l Ω)

/-- The faithful realization of the stagewise category in D(Qbar).
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarRealization :
    PointFdQbar l Ω ⥤ DerivedCategory (ModuleCat.{u} Ω) :=
  inducedFunctor (pointFdQbarObject l Ω)

/-- The canonical functor from a finite coefficient stage to the stagewise category.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarStage (E : Padic.FiniteCoefficientFields l Ω) :
    (pointFiniteDimensional E.val).FullSubcategory ⥤ PointFdQbar l Ω where
  obj C := ⟨E, C⟩
  map f := InducedCategory.homMk
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map f.hom)
  map_id C := InducedCategory.hom_ext
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map_id C.obj)
  map_comp f g := InducedCategory.hom_ext
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map_comp f.hom g.hom)

/-- Compatibility of the canonical finite-stage embeddings, with precisely the
termwise tensor tower comparison as underlying isomorphism.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarStageComp
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pointFdScalarExtension (IntermediateField.inclusion h).toRingHom ⋙
        pointFdQbarStage l Ω F ≅ pointFdQbarStage l Ω E :=
  ((fullyFaithfulInducedFunctor (pointFdQbarObject l Ω)).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (pointFiniteDimensional E.val).ι
      (fieldScalarTower (IntermediateField.inclusion h).toRingHom F.val.subtype))

/-- The finite-stage cocone of categories with the canonical tensor comparison.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarCocone :
    CategoryCocone
      (fun E : Padic.FiniteCoefficientFields l Ω ↦
        (pointFiniteDimensional E.val).FullSubcategory) (PointFdQbar l Ω) where
  T h := pointFdScalarExtension (IntermediateField.inclusion h).toRingHom
  Φ := pointFdQbarStage l Ω
  iso h := pointFdQbarStageComp l Ω h

omit [IsAlgClosure (Padic l) Ω] in
private theorem pointFdQbar_homInj : (pointFdQbarCocone l Ω).HomInj := by
  intro k x y g g' h
  change InducedCategory.homMk _ = InducedCategory.homMk _ at h
  have := fieldScalarExtension_faithful (K := k.val) (L := Ω) k.val.subtype
  have heq : g = g' := by
    apply ObjectProperty.hom_ext
    apply (fieldDerivedScalarExtension (K := k.val) (L := Ω) k.val.subtype).map_injective
    exact congrArg (fun z : (pointFdQbarStage l Ω k).obj x ⟶
      (pointFdQbarStage l Ω k).obj y ↦ z.hom) h
  exact ⟨k, le_refl k, congrArg ((pointFdQbarCocone l Ω).T (le_refl k)).map heq⟩

/-- The chosen realization has exactly the required common-stage Hom colimits.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category).
Proof: every object is its specified stage pair. For Hom surjectivity, split each
bounded finite-dimensional derived complex over its field into its finitely many
cohomology spaces. A morphism after scalar extension is a finite list of matrices.
The finitely many entries lie in a finite subextension of the algebraic closure;
take its compositum with the original stages. This gives the common-stage map.
For Hom injectivity, faithful scalar extension detects equality of those matrices;
thus equality holds at a common finite stage. Composition is transported from D(Ω)
and, by the canonical tower comparisons, is exactly common-stage composition. -/
theorem pointFdQbarCocone_isFilteredTwoColimit :
    (pointFdQbarCocone l Ω).IsFilteredTwoColimit := by
  refine ⟨?_, ?_, pointFdQbar_homInj l Ω⟩
  · intro d
    exact ⟨d.1, d.2, ⟨Iso.refl _⟩⟩
  · intro E F A B f
    obtain ⟨N, hE, hF, g, hg⟩ :=
      pointFd_morphism_descent l Ω E F A.obj B.obj A.property B.property f.hom
    refine ⟨N, hE, hF, ObjectProperty.homMk g, ?_⟩
    apply InducedCategory.hom_ext
    exact hg

/-- Finite-dimensional bounded cohomology is stable under every integer shift.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category).
Proof: H^i(C[n]) is canonically H^(i+n)(C); translate the finite support by -n
and retain the same finite-dimensionality proofs. -/
theorem pointFd_shift_mem {F : Type u} [Field F]
    (C : DerivedCategory (ModuleCat.{u} F)) (hC : pointFiniteDimensional F C) (n : ℤ) :
    pointFiniteDimensional F (C⟦n⟧) := by
  classical
  obtain ⟨⟨s, hs⟩, hfd⟩ := hC
  let e (i : ℤ) :
      (homologyFunctor (ModuleCat.{u} F) i).obj (C⟦n⟧) ≅
        (homologyFunctor (ModuleCat.{u} F) (n + i)).obj C :=
    ((homologyFunctor (ModuleCat.{u} F) 0).shiftIso n i (n + i) rfl).app C
  refine ⟨⟨s.image (fun i ↦ i - n), ?_⟩, ?_⟩
  · intro i hi
    have hni : n + i ∉ s := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨n + i, h, by omega⟩
    exact (hs (n + i) hni).of_iso (e i)
  · intro i
    let := hfd (n + i)
    exact (e i).symm.toLinearEquiv.finiteDimensional

/-- The shift of a stage pair, computed at that same stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftObj (X : PointFdQbar l Ω) (n : ℤ) : PointFdQbar l Ω :=
  ⟨X.1, ⟨X.2.obj⟦n⟧, pointFd_shift_mem X.2.obj X.2.property n⟩⟩

/-- The shifted realization with its object data fixed at the original finite stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftRealization (n : ℤ) :
    PointFdQbar l Ω ⥤ DerivedCategory (ModuleCat.{u} Ω) :=
  (pointFdQbarRealization l Ω ⋙ shiftFunctor _ n).copyObj
    (fun X ↦ pointFdQbarObject l Ω (pointFdQbarShiftObj l Ω X n))
    (fun X ↦ ((fieldDerivedScalarExtension (K := X.1.val) (L := Ω)
      X.1.val.subtype).commShiftIso n).symm.app X.2.obj)

/-- The actual shift functor on stage pairs and their induced morphisms.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShift (n : ℤ) : PointFdQbar l Ω ⥤ PointFdQbar l Ω where
  obj X := pointFdQbarShiftObj l Ω X n
  map f := InducedCategory.homMk ((pointFdQbarShiftRealization l Ω n).map f)
  map_id X := InducedCategory.hom_ext ((pointFdQbarShiftRealization l Ω n).map_id X)
  map_comp f g := InducedCategory.hom_ext ((pointFdQbarShiftRealization l Ω n).map_comp f g)

/-- The shift comparison used to transport the coherent shift structure faithfully.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftIso (n : ℤ) :
    pointFdQbarShift l Ω n ⋙ pointFdQbarRealization l Ω ≅
      pointFdQbarRealization l Ω ⋙ shiftFunctor _ n :=
  ((pointFdQbarRealization l Ω ⋙ shiftFunctor _ n).isoCopyObj
    (fun X ↦ pointFdQbarObject l Ω (pointFdQbarShiftObj l Ω X n))
    (fun X ↦ ((fieldDerivedScalarExtension (K := X.1.val) (L := Ω)
      X.1.val.subtype).commShiftIso n).symm.app X.2.obj)).symm

/-- The coherent integer shift structure induced from the faithful realization.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable instance pointFdQbarHasShift : HasShift (PointFdQbar l Ω) ℤ :=
  (fullyFaithfulInducedFunctor (pointFdQbarObject l Ω)).hasShift
    (pointFdQbarShift l Ω) (pointFdQbarShiftIso l Ω)

/-- Realization commutes with the specified shifts by its canonical tensor comparison.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable instance pointFdQbarRealizationCommShift :
    (pointFdQbarRealization l Ω).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (fullyFaithfulInducedFunctor (pointFdQbarObject l Ω))
    (pointFdQbarShift l Ω) (pointFdQbarShiftIso l Ω)

/-- Distinguished triangles are exactly those isomorphic, under faithful realization,
to scalar extensions of distinguished triangles at one common finite stage, with
all three vertices in D^b_fd of that stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarDistinguished (T : Triangle (PointFdQbar l Ω)) : Prop :=
  ∃ (E : Padic.FiniteCoefficientFields l Ω)
    (S : Triangle (DerivedCategory (ModuleCat.{u} E.val))),
    S ∈ distTriang _ ∧ pointFiniteDimensional E.val S.obj₁ ∧
      pointFiniteDimensional E.val S.obj₂ ∧ pointFiniteDimensional E.val S.obj₃ ∧
      Nonempty (((fieldDerivedScalarExtension (K := E.val) (L := Ω)
        E.val.subtype).mapTriangle).obj S ≅ (pointFdQbarRealization l Ω).mapTriangle.obj T)

end DerivedCategory

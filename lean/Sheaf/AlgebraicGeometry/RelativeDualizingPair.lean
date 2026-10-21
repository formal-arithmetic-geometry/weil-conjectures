/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

-- The successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Supplied coherent relative dualizing pairs

Source: Stacks Project, duality.tex, Definition 0E2T, with W = X ×_S X.
(blueprint: def-trf-coherent-relative-dualizing-pair).
The diagonal algebra is the ordinary direct image in degree zero. Its multiplication
is fixed on pure tensors, and its derived multiplication is induced by the canonical
lax monoidal localization. No relative dualizing complex is chosen or assumed to exist.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section
namespace AlgebraicGeometry

/-- The diagonal algebra as an ordinary module sheaf.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalModule {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace) :=
  (SheafOfModules.pushforward (pullback.diagonal f).toRingCatSheafHom).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))

/-- The diagonal algebra in degree zero, before localization.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalComplex {X S : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (relativeDualizingDiagonalModule f)

/-- The ordinary total tensor of the two degree-zero diagonal complexes.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalTensorComplex {X S : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) ℤ :=
  pullbackTensorTotal (pullback f f)
    (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f)

/-- Multiplication of diagonal sections characterizes the chain multiplication uniquely.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def IsRelativeDualizingDiagonalMultiplication {X S : Scheme.{u}} (f : X ⟶ S)
    (t : relativeDualizingDiagonalTensorComplex f ⟶ relativeDualizingDiagonalComplex f) :
    Prop :=
  letI := SheafOfModules.monoidalCategory (pullback f f).sheaf
  ∀ (U : (pullback f f).Opens)
    (a b : ((relativeDualizingDiagonalComplex f).X 0).val.obj (op U)),
    ((HomologicalComplex.ιMapBifunctor
        (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f)
        (curriedTensor _) (.up ℤ) 0 0 0 (by decide) ≫ t.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (relativeDualizingDiagonalModule f)).hom).val.app (op U))
      ((SheafOfModules.tensorObjIsoSheafification (R := (pullback f f).sheaf)
        ((relativeDualizingDiagonalComplex f).X 0)
        ((relativeDualizingDiagonalComplex f).X 0)).inv.val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (moduleRings (pullback f f).toRingedSpace).obj)).unit.app
          (((relativeDualizingDiagonalComplex f).X 0).val ⊗
            ((relativeDualizingDiagonalComplex f).X 0).val)).app (op U) (a ⊗ₜ b))) =
      (@id (X.presheaf.obj (op ((pullback.diagonal f) ⁻¹ᵁ U)))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (relativeDualizingDiagonalModule f)).hom.val.app (op U) a)) *
      (@id (X.presheaf.obj (op ((pullback.diagonal f) ⁻¹ᵁ U)))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (relativeDualizingDiagonalModule f)).hom.val.app (op U) b))

private def diagonalSectionProduct {X S : Scheme.{u}} (f : X ⟶ S)
    (U : (pullback f f : Scheme.{u}).Opensᵒᵖ) :
    (relativeDualizingDiagonalModule f).val.obj U →ₗ[(pullback f f).presheaf.obj U]
      (relativeDualizingDiagonalModule f).val.obj U →ₗ[(pullback f f).presheaf.obj U]
        (relativeDualizingDiagonalModule f).val.obj U := by
  letI : CommRing ((relativeDualizingDiagonalModule f).val.obj U) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op ((pullback.diagonal f) ⁻¹ᵁ U.unop))))
  refine
    { toFun := fun a ↦
        { toFun := fun b ↦ a * b
          map_add' := fun b c ↦ mul_add a b c
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro r b
    change _ * (_ * b) = _ * (_ * b)
    simp only [RingHom.id_apply]
    ac_rfl
  · intro a b
    ext c
    exact add_mul a b c
  · intro r a
    ext b
    change (_ * a) * b = _ * (a * b)
    simp only [RingHom.id_apply]
    exact mul_assoc _ _ _

private theorem diagonalSectionProduct_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : (pullback f f : Scheme.{u}).Opensᵒᵖ} (g : U ⟶ V)
    (a b : (relativeDualizingDiagonalModule f).val.obj U) :
    diagonalSectionProduct f V ((relativeDualizingDiagonalModule f).val.map g a)
        ((relativeDualizingDiagonalModule f).val.map g b) =
      (relativeDualizingDiagonalModule f).val.map g (diagonalSectionProduct f U a b) := by
  exact ((X.presheaf.map
    ((TopologicalSpace.Opens.map (pullback.diagonal f).base).op.map g)).hom.map_mul a b).symm

private def diagonalTensorSingleIso {X S : Scheme.{u}} (f : X ⟶ S) :
    relativeDualizingDiagonalTensorComplex f ≅
      (CochainComplex.singleFunctor _ 0).obj
        ((SheafOfModules.monoidalCategory (pullback f f).sheaf).tensorObj
          (relativeDualizingDiagonalModule f) (relativeDualizingDiagonalModule f)) := by
  letI := SheafOfModules.monoidalCategory (pullback f f).sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor (pullback f f).sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (pullback f f).sheaf
  exact CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _)
      (relativeDualizingDiagonalModule f) (relativeDualizingDiagonalComplex f) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (tensorLeft (relativeDualizingDiagonalModule f)) (.up ℤ) 0).app _

private theorem diagonalTensorSingleIso_component {X S : Scheme.{u}} (f : X ⟶ S) :
    letI := SheafOfModules.monoidalCategory (pullback f f).sheaf
    let A := relativeDualizingDiagonalModule f
    let C := relativeDualizingDiagonalComplex f
    HomologicalComplex.ιMapBifunctor C C (curriedTensor _) (.up ℤ) 0 0 0 (by decide) ≫
      (diagonalTensorSingleIso f).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A ⊗ A)).hom =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ⊗ₘ
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom) := by
  dsimp only [diagonalTensorSingleIso, Iso.trans_hom, HomologicalComplex.comp_f]
  simp [CochainComplex.mapBifunctorSingle₁Iso, CochainComplex.mapBifunctorSingle₁XIso,
    HomologicalComplex.singleObjXSelf, tensorHom_def]
  rfl

/-- The multiplication is uniquely specified by the ordinary diagonal algebra.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair).
Proof: the total tensor of two complexes supported in degree zero is supported in
 degree zero. Multiply sections in O_X on the inverse image of each open of X ×_S X.
These bilinear maps commute with restrictions and hence factor uniquely through
module sheafification of the sectionwise tensor. They define the degree-zero
component, with zero components elsewhere. The differentials vanish. Pure tensors
and the total-tensor summand inclusions determine every component, proving uniqueness. -/
theorem existsUnique_relativeDualizingDiagonalMultiplication
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃! t : relativeDualizingDiagonalTensorComplex f ⟶ relativeDualizingDiagonalComplex f,
      IsRelativeDualizingDiagonalMultiplication f t := by
  classical
  let := SheafOfModules.monoidalCategory (pullback f f).sheaf
  let A := relativeDualizingDiagonalModule f
  let C := relativeDualizingDiagonalComplex f
  obtain ⟨m, hm, huniq⟩ := SheafOfModules.tensor_bilinear_universal
    (pullback f f).sheaf A A A (diagonalSectionProduct f)
    (diagonalSectionProduct_naturality f)
  let e := diagonalTensorSingleIso f
  let t := e.hom ≫ (CochainComplex.singleFunctor _ 0).map m
  have ht : HomologicalComplex.ιMapBifunctor C C (curriedTensor _) (.up ℤ)
      0 0 0 (by decide) ≫ t.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = m := by
    dsimp only [t, HomologicalComplex.comp_f]
    erw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have he := diagonalTensorSingleIso_component f
    simp only [← Category.assoc] at he ⊢
    erw [he]
    simp only [curriedTensor_obj_obj, HomologicalComplex.single, ↓dreduceIte,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, tensorHom_def, id_whiskerRight, whiskerLeft_id,
      Category.comp_id]
    exact Category.id_comp m
  refine ⟨t, ?_, ?_⟩
  · intro U a b
    rw [ht]
    exact hm (op U) a b
  · intro t' ht'
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom).1
    apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := C) (K₂ := C)
      (F := curriedTensor _) (c := .up ℤ)
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by change (0 : ℤ) + q = 0 at hpq; omega
      subst q
      rw [ht]
      exact huniq _ (fun U a b ↦ ht' U.unop a b)
    · apply IsZero.eq_of_src
      exact Functor.map_isZero ((curriedTensor _).flip.obj (C.X q))
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p hp)

/-- The canonical derived multiplication of Δ_* O_X, from its actual algebra multiplication.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalMultiplication {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))] :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⊗
      DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
        DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) :=
  pullbackTensorModelMap (pullback f f)
      (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f) ≫
    DerivedCategory.Q.map
      (Classical.choose (existsUnique_relativeDualizingDiagonalMultiplication f).exists)

/-- The scalar map, the canonical transpose of the left unit action.
Source: Stacks 0E2V (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingScalarMap (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    𝟙_ (schemeDerivedCategory X) ⟶
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op K, K) :=
  (schemeDerivedTensorHomEquiv X _ K K).symm (λ_ K).hom

/-- Multiplication by a diagonal class, transposed under the canonical tensor-Hom bijection.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingClassMap {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedInternalHom (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj
          (op (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)),
            (derivedPullback (pullback.fst f f)).obj K) :=
  (schemeDerivedTensorHomEquiv (pullback f f : Scheme.{u}) _ _ _).symm
    (relativeDualizingDiagonalMultiplication f ≫ ξ)

/-- A supplied coherent relative dualizing pair: pseudo-coherence, locally finite
Tor amplitude over S, and invertibility of multiplication by its specified diagonal class.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def IsCoherentRelativeDualizingPair
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) : Prop :=
  Scheme.IsPseudoCoherent X K ∧
    (∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.HasFiniteTorDimensionOver (U.ι ≫ f) ((derivedPullback U.ι).obj K)) ∧
    IsIso (relativeDualizingClassMap f K ξ)

end AlgebraicGeometry

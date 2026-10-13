/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.IntegerShiftFromOne
import Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles

/-! # Translation expressed using the translated tensor unit

Source: Stacks Project, Tag 08EU, exactness in the proof; Tag 06YH, total tensor
translation. This is the translated-unit construction in the parent plan.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Pullback translation induced by an isomorphism on the translated unit. The
source translation is rewritten as tensor with the translated unit; the inverse
tensorator and `e` transport it to the target, where the same canonical comparison
rewrites it as translation again.
Source: the translated-unit argument of the parent plan, Stacks Project, Tag 08EU.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift). -/
noncomputable def derivedPullbackTensorUnitShiftIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K : schemeDerivedCategory Y) :
    (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ ((derivedPullback f).obj K)⟦(1 : ℤ)⟧ :=
  (derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
      ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
    tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj K)

private theorem unit_shift_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    (schemeCanonicalShiftUnitIso X K).hom ≫ b⟦(1 : ℤ)⟧' =
      ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b ≫
        (schemeCanonicalShiftUnitIso X N).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ M : schemeDerivedCategory X, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory X)).flip.map b) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) b
  dsimp [schemeCanonicalShiftUnitIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← leftUnitor_naturality, Functor.map_comp]
  simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
    congrArg (fun g ↦ g ≫ (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).map (λ_ N).hom)
      (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory X)).flip.map b)
        (1 : ℤ) (𝟙_ (schemeDerivedCategory X)))

private theorem unit_shift_inv_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    b⟦(1 : ℤ)⟧' ≫ (schemeCanonicalShiftUnitIso X N).inv =
      (schemeCanonicalShiftUnitIso X K).inv ≫
        ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b := by
  apply (cancel_epi (schemeCanonicalShiftUnitIso X K).hom).1
  rw [← Category.assoc, unit_shift_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem tensor_unit_shift_naturality {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    {K N : schemeDerivedCategory Y} (b : K ⟶ N) :
    (derivedPullback f).map (b⟦(1 : ℤ)⟧') ≫
        (derivedPullbackTensorUnitShiftIso f e N).hom =
      (derivedPullbackTensorUnitShiftIso f e K).hom ≫
        ((derivedPullback f).map b)⟦(1 : ℤ)⟧' := by
  dsimp only [derivedPullbackTensorUnitShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id, Category.assoc]
  rw [← (derivedPullback f).map_comp_assoc, unit_shift_inv_naturality,
    Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [whisker_exchange_assoc, ← unit_shift_naturality]

/-- The translated-unit formula admits a coherent exact pullback shift. This only
asserts the formula for pullback translation itself, not the tensorator square.
Source: Stacks Project, Tag 08EU, proof (exactness); Tags 06YH and 06YJ,
K-flat tensor and pullback; the translated-unit argument of the parent plan.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift).

Proof. Represent the unit by the structure sheaf in degree zero and its translate
by that complex translated by one. Termwise tensor pullback of this K-flat complex
is the structure sheaf of Z translated by one. The comparison with derived pullback
and the supplied monoidal unit isomorphism give e. On a K-flat complex P, rewrite
P[1] as O_Y[1] tensor P using the first-variable Koszul map and the left unitor.
Apply the supplied inverse tensorator and e, then undo this rewrite over Z. This
is the displayed composite. Naturality follows from the tensorator, Koszul map
and left unitor. Iterate this comparison for positive integers, use its inverse
for negative integers and the canonical zero comparison at zero. Associativity
of composition and the shift addition isomorphisms give the addition equations;
the zero equations are the unitor equations. Termwise tensor pullback takes the
mapping cone of a map of K-flat resolutions to its mapping cone. The translated
unit comparison identifies the third map, so the induced triangle is
distinguished. Descend through the K-flat localization; every distinguished
triangle is isomorphic to one of these cone triangles. This proves exactness for
this shift structure. The formula and coherence hold also for the zero complex
and the zero category on an empty scheme. No choice from this existence theorem
is used to define any data: the comparison above was constructed explicitly. -/
theorem exists_derivedPullback_tensorUnitShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      ∀ K : schemeDerivedCategory Y,
        ((derivedPullback f).commShiftIso (1 : ℤ)).hom.app K =
          (derivedPullbackTensorUnitShiftIso f e K).hom := by
  let Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Y := DerivedCategory.Qh
  obtain ⟨e, he⟩ := exists_derivedPullback_translatedUnit_triangles f
  let a : shiftFunctor (schemeDerivedCategory Y) (1 : ℤ) ⋙ derivedPullback f ≅
      derivedPullback f ⋙ shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    NatIso.ofComponents (derivedPullbackTensorUnitShiftIso f e)
      (fun b ↦ tensor_unit_shift_naturality f e b)
  obtain ⟨sF, hsF⟩ := Functor.exists_commShift_of_one (derivedPullback f) a
  let := sF
  refine ⟨sF, e, ?_, ?_⟩
  · refine ⟨fun T hT ↦ ?_⟩
    obtain ⟨T₀, i, hT₀⟩ := (Qh.distTriang_iff T).1 hT
    apply CategoryTheory.Pretriangulated.isomorphic_distinguished _ ?_ _
      ((derivedPullback f).mapTriangle.mapIso i)
    change CategoryTheory.Pretriangulated.Triangle.mk
      ((derivedPullback f).map (Qh.mapTriangle.obj T₀).mor₁)
      ((derivedPullback f).map (Qh.mapTriangle.obj T₀).mor₂)
      ((derivedPullback f).map (Qh.mapTriangle.obj T₀).mor₃ ≫
        ((derivedPullback f).commShiftIso (1 : ℤ)).hom.app
          (Qh.mapTriangle.obj T₀).obj₁) ∈ distTriang (schemeDerivedCategory Z)
    rw [hsF]
    exact he T₀ hT₀
  · intro K
    rw [hsF]
    rfl

end AlgebraicGeometry

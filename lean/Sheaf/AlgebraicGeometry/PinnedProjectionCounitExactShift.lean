/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Exact shifts for a pinned projection followed by a counit

Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-pinned-projection-counit-exact-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Exact shifts making a projection isomorphism followed by tensoring a fixed map to
O_Y compatible with translation. This assertion involves no right adjoint to Rf_*.
Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-pinned-projection-counit-exact-shift).

Proof. Fix E and ε : Rf_*E → O_Y. On K-flat representatives the functor
K ↦ Lf*K tensor E takes a cone to the cone of the tensored pullback map.
Translation of complexes supplies its zero and addition coherences. Direct image
on K-injective representatives also commutes with translation and mapping cones.
Quasi-coherent cohomology is stable under translations and extensions, so both
constructions restrict to the stated quasi-coherent functors Q and R.
For the specified monoidal structure on Lf*, use the tensorator and the identification
K[n] ≅ K tensor O_Y[n] to transport the pullback translation comparison. The
associativity and unit equations of the tensorator give the addition and zero
coherences. Transport the direct-image comparison across a by adjunction mates;
the unit and counit triangle identities give its compatible translation comparison.
These transported comparisons preserve distinguished triangles: on representative
complexes they identify the images with the mapping-cone triangles just described.
Expand the inverse projection component as the a-mate of the inverse tensorator
followed by Lf*K tensor the a-counit at E. Move translation through these factors.
The transported comparisons, counit naturality, and the adjunction triangle
identities identify the shifted component with the translation of the original.
Invert this equality using pf. Tensoring ε is natural in the shifted first variable;
the right unitor has the same translation comparison. Compose these three
compatibility equations to obtain the equation for ν. Its assumed component
formula transfers the equation to the specified ν. No ν component is cancelled:
ε = 0, E = 0, and zero triangles satisfy the same argument. -/
theorem pinnedProjectionCounit_exactShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty Y).IsTriangulated]
    [(schemeDerivedQCohProperty Z).IsTriangulated]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (E : schemeDerivedQCohCategory Z)
    (hTensor : ∀ K : schemeDerivedQCohCategory Y,
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (ε : (⟨(schemeDerivedDirectImage f).obj E.obj, hRf E⟩ :
      schemeDerivedQCohCategory Y) ⟶ ⟨𝟙_ _, hO⟩)
    (ν : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj)
      hTensor ⋙ (schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⟶
      𝟭 (schemeDerivedQCohCategory Y))
    (hν : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ E.obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj E.obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj) ∧
        (ν.app K).hom = pf.hom ≫ K.obj ◁ ε.hom ≫ (ρ_ K.obj).hom) :
    let Q := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj) hTensor
    let R := (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf
    ∃ (sQ : Q.CommShift ℤ) (sR : R.CommShift ℤ),
      letI := sQ
      letI := sR
      Q.IsTriangulated ∧ R.IsTriangulated ∧ NatTrans.CommShift ν ℤ := by
  obtain ⟨sL, sY, sZ, hL, hTZ, hYmap, hZmap, hδ, hρ⟩ :=
    exists_derivedMonoidalPullback_unitalShift f
  let := sL
  let := sY
  let := sZ
  have := hL
  let := a.rightAdjointCommShift ℤ
  have := a.commShift_of_leftAdjoint ℤ
  have := a.isTriangulated_rightAdjoint
  have := hTZ E.obj
  let Q := (schemeDerivedQCohProperty Z).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj) hTensor
  let R := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf
  refine ⟨inferInstanceAs (Q.CommShift ℤ), inferInstanceAs (R.CommShift ℤ),
    inferInstance, inferInstance, ?_⟩
  let φ : (Functor.postcompose₂.obj (derivedPullback f)).obj
      (curriedTensor (schemeDerivedCategory Y)).flip ⟶
      (((Functor.whiskeringLeft₂ (schemeDerivedCategory Z)).obj
        (derivedPullback f)).obj (derivedPullback f)).obj
        (curriedTensor (schemeDerivedCategory Z)).flip :=
    (flipFunctor _ _ _).map
      (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))
  let p : tensorRight ((schemeDerivedDirectImage f).obj E.obj) ⟶
      (derivedPullback f ⋙ tensorRight E.obj) ⋙ schemeDerivedDirectImage f :=
    (a.rightAdjointProjectionMap φ).app E.obj
  have hpshift : NatTrans.CommShift (F₁ :=
      tensorRight ((schemeDerivedDirectImage f).obj E.obj))
      (F₂ := (derivedPullback f ⋙ tensorRight E.obj) ⋙ schemeDerivedDirectImage f)
      p ℤ := by
    have := hδ ((schemeDerivedDirectImage f).obj E.obj)
    have := hZmap (a.counit.app E.obj)
    exact Adjunction.commShift_rightAdjointProjectionMap_app a φ E.obj
  let ιY := (schemeDerivedQCohProperty Y).ι
  let ιZ := (schemeDerivedQCohProperty Z).ι
  let e : (Q ⋙ R) ⋙ ιY ≅
      ιY ⋙ (derivedPullback f ⋙ tensorRight E.obj) ⋙ schemeDerivedDirectImage f :=
    Functor.associator Q R ιY ≪≫
      Functor.isoWhiskerLeft Q ((schemeDerivedQCohProperty Y).liftCompιIso
        (ιZ ⋙ schemeDerivedDirectImage f) hRf) ≪≫
      (Functor.associator Q ιZ (schemeDerivedDirectImage f)).symm ≪≫
      Functor.isoWhiskerRight ((schemeDerivedQCohProperty Z).liftCompιIso
        (ιY ⋙ derivedPullback f ⋙ tensorRight E.obj) hTensor)
        (schemeDerivedDirectImage f) ≪≫
      Functor.associator ιY (derivedPullback f ⋙ tensorRight E.obj)
        (schemeDerivedDirectImage f)
  have : NatTrans.CommShift e.hom ℤ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  let t : ιY ⋙ tensorRight ((schemeDerivedDirectImage f).obj E.obj) ⟶
      ιY ⋙ (derivedPullback f ⋙ tensorRight E.obj) ⋙ schemeDerivedDirectImage f :=
    Functor.whiskerLeft ιY p
  have : NatTrans.CommShift t ℤ := inferInstance
  have ht (K : schemeDerivedQCohCategory Y) : IsIso (t.app K) := by
    obtain ⟨pf, hpin, _⟩ := hν K
    have heq : t.app K = pf.inv := by
      simpa [t, p, φ, ιY, Adjunction.rightAdjointProjectionMap_app_app] using hpin.symm
    rw [heq]
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  have : NatTrans.CommShift (inv t) ℤ := NatTrans.CommShift.of_isIso t ℤ
  have := hρ
  let c := (curriedTensor (schemeDerivedCategory Y)).flip.map ε.hom ≫
    (rightUnitorNatIso (schemeDerivedCategory Y)).hom
  have : NatTrans.CommShift c ℤ := by
    have := hYmap ε.hom
    infer_instance
  have heq : Functor.whiskerRight ν ιY =
      e.hom ≫ inv t ≫ Functor.whiskerLeft ιY c ≫
        ιY.rightUnitor.hom ≫ ιY.leftUnitor.inv := by
    ext K
    obtain ⟨pf, hpin, hformula⟩ := hν K
    have htp : t.app K = pf.inv := by
      simpa [t, p, φ, ιY, Adjunction.rightAdjointProjectionMap_app_app] using hpin.symm
    have hinv : (inv t).app K = pf.hom := by
      apply (cancel_mono pf.inv).1
      rw [← htp]
      calc
        (inv t).app K ≫ t.app K = 𝟙 _ := (asIso t).inv_hom_id_app K
        _ = pf.hom ≫ t.app K := by
          rw [htp, pf.hom_inv_id]
          rfl
    simpa [e, c, ιY, ιZ, hinv, ObjectProperty.liftCompιIso, Q, R, Category.id_comp]
      using hformula
  have : NatTrans.CommShift (Functor.whiskerRight ν ιY) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight ν ιY

end AlgebraicGeometry

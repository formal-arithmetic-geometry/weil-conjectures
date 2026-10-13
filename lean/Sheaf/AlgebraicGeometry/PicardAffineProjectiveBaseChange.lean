/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Base change for an affine K-flat direct-image model

Source: Stacks Project, Tags 0A1D, 08DW(2) and 06Z0.
(blueprint: lem-sc-picard-affine-projective-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Sheafified scalar extension of an affine K-flat model represents the structure
sheaf's derived direct image after base change to the spectrum of the new ring.
Source: Stacks Project, Tags 0A1D, 08DW(2), 08FE and 06Z0.
(blueprint: lem-sc-picard-affine-projective-base-change).

Proof: Apply the exact over equivalence to the representing isomorphism. It
cancels the inverse over equivalence in affinePerfectSheafification, leaving
tilde(P) restricted along U ≅ Spec R. Open restriction of derived direct image
identifies the other side with the image along X ×_S U → U. Tensor-pullback
composition and the canonical isomorphism of the two iterated pullbacks carry
the coefficient to the given trivialization, hence to O_{X ×_S U}. Transport
through U ≅ Spec R. Base change this direct image along Spec B → Spec R.
The morphism X ×_S U → U is quasi-compact, separated and flat. Its
structure module is invertible. Canonical flat-invertible base change
(Tag 0A1D) therefore identifies this derived pullback with the derived
image of the derived pullback of O; flatness of O and the tensor-unit
isomorphism identify the latter coefficient with O_{X ×_S Spec B}.
The K-flat affine pullback formula of Tag 08DW(2) identifies derived pullback
of tilde(P) with tilde of termwise scalar extension PB. Compose the resulting
derived isomorphisms. Neither the structure-unit hypothesis nor a homology
claim is needed here. Empty affine opens and the zero coefficient ring satisfy
the same comparisons; all sheaves on the empty spectrum are zero. -/
theorem picard_affine_projective_base_change
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [QuasiCompact f] [IsSeparated f]
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf))
    (P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      L.Acyclic → (CochainComplex.mapBifunctor L P
        (MonoidalCategory.curriedTensor _)).Acyclic)
    (hrep : Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P))) :
    ∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
      let g : Spec (.of B) ⟶ S :=
        Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι ≫ k
      Nonempty
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{v} B ⥤
              SheafOfModules.{v} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{v} (moduleRings (pullback f g).toRingedSpace)) 0).obj
                (SheafOfModules.unit (pullback f g).ringCatSheaf))) := by sorry

end AlgebraicGeometry.Scheme

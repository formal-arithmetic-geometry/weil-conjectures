/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation
import Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveHomology

/-! # The unnormalized affine structure-image model

Source: Stacks Project, Tags 0BF2, 0B91, 08EB and 06Z0.
(blueprint: lem-sc-picard-affine-structure-projective-model).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The trivialized coefficient image has a bounded projective affine model whose
base changes have no negative homology and have free rank-one zeroth homology.
No cancellation of terms or vanishing of a differential is asserted here.

Source: Stacks Project, Tag 0BF2, perfect base-change paragraph; Tags 0B91, 08EB, 06Z0.
(blueprint: lem-sc-picard-affine-structure-projective-model).

Proof: Put R = Gamma(W,U). Exact restriction and open base change identify the
restricted image with the direct image on U of the pullback of M. Apply the given
trivialization to identify this with R(f_U)_*O. The structure sheaf is finitely
presented and flat over the base because f_U is flat. Proper finite-presentation
perfect base change therefore makes this image perfect and identifies every
further derived base change with R(f_B)_*O. Transport across isoSpec and overEquiv
and apply the affine bounded-projective characterization, obtaining P and the
stated representing isomorphism on the original U. Its bounded projective terms
compute derived scalar extension by ordinary termwise extension of scalars.
For every R -> B, the corresponding map Spec B -> U -> S is covered by hO.
Thus the zeroth direct image of O on that base change is O_Spec B; negative
cohomology vanishes since this is the right derived image of a sheaf in degree
zero. The affine tilde/Gamma equivalence identifies these assertions with the
homology of B tensor P. For the zero ring all modules and complexes are zero;
no nonempty-open hypothesis and no shrinking of U is needed. -/
theorem picard_affine_structure_projective_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ P : CochainComplex (ModuleCat.{v} (W.presheaf.obj (.op U))) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (W.presheaf.obj (.op U)) (P.X n)) ∧
      (∀ (B : Type v) [CommRing B] (φ : W.presheaf.obj (.op U) →+* B),
        let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
        (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
          Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨P, hb, hf, hp, hrep⟩ :=
    picard_affine_structure_projective_representation f M W k U hU htrivial
  exact ⟨P, hb, hf, hp,
    picard_affine_structure_projective_homology f hO M W k U hU htrivial P hb hp hrep,
    hrep⟩

end AlgebraicGeometry.Scheme

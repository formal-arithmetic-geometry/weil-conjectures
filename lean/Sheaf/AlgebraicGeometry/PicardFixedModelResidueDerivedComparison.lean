/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
/-! # Fixed-affine models used in the Picard comparison

Source: Stacks Project, Tag 0BF2.
(blueprint: lem-sc-picard-fixed-model-residue-derived-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Derived arrows and compatible residue identifications for the fixed Picard models.
Source: Stacks Project, Tag 0BF2; Tags 08CR and 0B91.
(blueprint: lem-sc-picard-fixed-model-residue-derived-comparison)

Proof: Restrict the canonical derived coefficient pullback maps to U and conjugate
by the supplied model isomorphisms, giving a_i. For any chain representatives φ_i
of these arrows, localization identifies their homology maps with those of a_i.
The source residue term ranks equal its Betti numbers, so the finite-dimensional
homology dimension formula forces its residue differentials to vanish. The universal
structure adjunction unit rules out an empty source fibre. Descending L_s from the
field and invertibility of its nonempty pullback make the descended module rank one,
hence trivial. Choose this source trivialization and pull it back to every target.
Derived base change, affine cohomology comparison, and the residue-field isomorphism
of an immersion identify the source residue degree-one term with H¹(X_s,O), giving α.
For each target, the zero incoming differential identifies residue H¹ with the kernel
of the outgoing differential. Choose a vector-space projection onto that kernel and
use the pulled-back source trivialization to identify the kernel with H¹(Xi_s,O).
Compose these maps with the tensorized coordinate projections and take their product
to obtain γ. Naturality of residue homology for each chain representative, together with the
vanishing source residue differential, puts its image in each target kernel, where
the chosen projection is the identity. Naturality of derived base change and affine
cohomology comparison then gives the displayed compatibility. The source basis e1
is incorporated through its inverse. For an empty family the product map is unique;
for zero source degree-one rank the source cohomology vanishes. -/
theorem picard_fixed_model_residue_derived_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCnegative : ∀ i j, j < 0 → IsZero ((C i).X j))
    (hCzero : ∀ i, (C i).d 0 1 = 0)
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    let p := RingHom.ker (W.evaluation U w hwU).hom
    letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
    ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
      (γ : (p.ResidueField ⊗[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U))))) →+
        (∀ i, Sheaf.H (structureSheafAb
          (pullback (fi i) (S.fromSpecResidueField s))) 1)),
      ∀ (φ : ∀ i, K ⟶ C i), (∀ i, DerivedCategory.Q.map (φ i) = a i) →
      let t : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)]
          (∀ i, ((C i).X 1).val.obj (.op (Over.mk (𝟙 U)))) :=
        LinearMap.pi (fun i ↦
          (((φ i).f 1).val.app (.op (Over.mk (𝟙 U)))).hom.comp e1.symm.toLinearMap)
      ∀ z, γ (t.baseChange p.ResidueField z) = fun i ↦
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (α z) := by sorry

end AlgebraicGeometry.Scheme

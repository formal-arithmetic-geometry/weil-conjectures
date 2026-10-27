/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.TraceFormula.FlatAssociatedEquidimensional
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.FinitePresentationStalkFibreData
import Sheaf.AlgebraicGeometry.FinitePresentationStalkBasisSpread
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber
import WeilConjectures.RingTheory.FlatSemilinearEquiv
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Relative flatness and a flat fibre stalk give a free neighbourhood

Source: Stacks Project, More on Morphisms, Tag 080Q, lemma-flat-and-free-at-point-fibre
(blueprint: lem-trf-flat-fibre-free-neighbourhood).

The proof follows Tag 080Q.  First the fibre flatness criterion, applied to the local rings at
`x`, identifies the stalk as flat over `𝒪_{X,x}`.  Finite flatness over a local ring gives a finite
basis.  Spreading the basis gives a surjection from a finite free module; finite presentation makes
its kernel finite type, so the zero kernel at `x` vanishes after shrinking.  The resulting map is
the required local isomorphism.  The zero stalk case is the same argument with rank zero.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness and flatness on the scheme-theoretic fibre imply local freeness.
(blueprint: lem-trf-flat-fibre-free-neighbourhood) -/
theorem exists_free_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (hflat : moduleFlatAt f F x)
    (hfibre : Module.Flat ((f.fiber (f x)).toRingedSpace.presheaf.stalk (f.asFiber x))
      ((AlgebraicGeometry.RingedSpace.moduleStalkFunctor (f.fiber (f x)).toRingedSpace
        (f.asFiber x)).obj ((AlgebraicGeometry.Scheme.Modules.tensorPullback
          (f.fiberι (f x))).obj F))) :
    ∃ (W : X.Opens) (r : ℕ), x ∈ W ∧
      Nonempty (((restrictFunctor W.ι).obj F) ≅
        (restrictFunctor W.ι).obj
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) := by
  classical
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F
  obtain ⟨hlocal, ⟨P, α, β, hP, hcomp, T, hloc⟩,
    ⟨a, b, v, w, hvw, hw⟩, θ, η, hθ, hη, hηgerm⟩ :=
    f.exists_finitePresentation_stalk_fibre_data F x
  have : Module.FinitePresentation B M :=
    Module.finitePresentation_of_free_of_surjective w hw
      (by rw [hvw.linearMap_ker_eq]; exact Submodule.fg_range v)
  have hfree : Module.Free B M := by
    cases subsingleton_or_nontrivial M with
    | inl h =>
      let := h
      infer_instance
    | inr h =>
      let := h
      let : Algebra R B := (f.stalkMap x).hom.toAlgebra
      let : Module R M := Module.compHom M (f.stalkMap x).hom
      have : IsScalarTower R B M := IsScalarTower.of_compHom R B M
      have : IsLocalHom (algebraMap R B) := hlocal
      have : Module.Flat R M := hflat
      let : Algebra R P := α.toAlgebra
      let : Algebra P B := β.toAlgebra
      have : IsScalarTower R P B :=
        IsScalarTower.of_algebraMap_eq fun z ↦ congrArg (fun g : R →+* B ↦ g z) hcomp.symm
      have : Algebra.FinitePresentation R P := hP
      have : IsLocalization T B := hloc
      let I : Ideal B := (IsLocalRing.maximalIdeal R).map (f.stalkMap x).hom
      have hquot : Module.Flat (B ⧸ I) (M ⧸ (I • (⊤ : Submodule B M))) := by
        apply (Module.Flat.semilinearEquiv_iff θ η ?_).mpr hfibre
        intro q m
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule B M)) m
        exact hη z n
      have := hquot
      have hclosed : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M) :=
        Module.Flat.of_linearEquiv
          ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
            Ideal.Quotient.mk_surjective)
      have : Module.Flat B M :=
        (Module.flat_of_flat_closedFiber R B B M P P T T hclosed).2
      exact Module.free_of_flat_of_isLocalRing
  let := hfree
  let r := Module.finrank B M
  obtain ⟨W, hxW, t, ψ, ht, hψ, hgen⟩ :=
    RingedSpace.exists_free_neighbourhood_prescribed_stalk_basis
      X.toRingedSpace F x r (Module.finBasis B M)
  let := hψ
  let W' : X.Opens := W
  exact ⟨W', r, hxW, ⟨overIsoFreeEquiv F W' _ (asIso ψ).symm ≪≫
    (restrictFreeIso W'.ι (ULift.{u} (Fin r))).symm⟩⟩

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.RingTheory.CotangentBootstrap
import WeilConjectures.RingTheory.DerivedDiagonalCotangentVanishing

/-!
# Vanishing of the cotangent complex of an étale ring map

Source: Stacks Project, Cotangent Complex, Tag 08R2 (lemma-when-zero), case (5)
(blueprint: lem-trf-etale-cotangent-vanishing).

The cotangent complex uses the standard polynomial resolution supplied by
`Algebra.CotangentResolution.Coherence`. The lifting hypothesis is written
explicitly as bijectivity of reduction for every square-zero ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

set_option backward.isDefEq.respectTransparency false in
private theorem flat_surjection_diagonal
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (hflat : f.hom.Flat)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B))) :
    IsIso (derivedDiagonalMultiplication f P) := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have hc : IsIso ((ModuleCat.extendRestrictScalarsAdj f.hom).counit.app
      (ModuleCat.of B B)) := by
    let : Algebra A B := f.hom.toAlgebra
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact LinearMap.mul'_bijective_of_surjective A B hf
  have : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f.hom) := inferInstance
  have : (ModuleCat.extendScalars.{u, u, u} f.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (ModuleCat.extendScalars.{u, u, u} f.hom).PreservesHomology := inferInstance
  have hπ : QuasiIso
      (((ModuleCat.extendScalars f.hom).mapHomologicalComplex (ComplexShape.down ℕ)).map
        P.π) := by
    exact HomologicalComplex.quasiIso_map_of_preservesHomology P.π _
  have hsingle : IsIso ((ChainComplex.single₀ (ModuleCat.{u} B)).map
      ((ModuleCat.extendRestrictScalarsAdj f.hom).counit.app (ModuleCat.of B B))) := by
    infer_instance
  unfold derivedDiagonalMultiplication
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  infer_instance

private theorem flat_tor_vanishing (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) [Module.Flat A M] (n : ℕ) :
    IsZero (((Tor' (ModuleCat.{u} A) (n + 1)).obj M).obj M) := by
  let P := projectiveResolution M
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj (MonoidalCategory.tensorRight M) (n + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  change ((P.complex.sc (n + 1)).map (MonoidalCategory.tensorRight M)).Exact
  exact Module.Flat.rTensor_shortComplex_exact M _ (P.complex_exactAt_succ n)

set_option backward.isDefEq.respectTransparency false in
/-- The standard cotangent complex of an étale ring map is zero, and all its
integer-indexed cohomology objects vanish.
Source: Stacks Project, Tag 08R2 (lemma-when-zero), case (5)
(blueprint: lem-trf-etale-cotangent-vanishing).

Proof:
1. Apply `lem-trf-etale-ring-map-weakly-etale` to finite presentation and the
   square-zero lifting bijections. Both `R → C` and multiplication
   `μ : C ⊗[R] C → C` are flat.
2. Multiplication is surjective since `c ⊗ 1` maps to `c`. Apply
   tensor exactness to a projective resolution of this flat surjection. The
   augmentation stays a quasi-isomorphism, and ordinary multiplication is an
   isomorphism by surjectivity. Thus the canonical derived multiplication is
   invertible. Then
   `lem-trf-derived-diagonal-cotangent-vanishing` gives `L_{C/(C ⊗[R] C)} = 0`.
3. Flatness over `R` gives `Tor_i^R(C,C) = 0` for every `i > 0`. Apply
   `lem-trf-cotangent-bootstrap` with the preceding diagonal vanishing to obtain
   `L_{C/R} = 0` in `D(C)`. The cohomology functors of
   `def-weil-abstract-derived-category` send this zero object to zero objects;
   conversely vanishing in every degree detects zero in the derived category. -/
theorem isZero_cotangentComplex_of_etale
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (κ : Coherence.{u}) (R C : CommRingCat.{u}) [Algebra R C]
    [FinitePresentation R C]
    (hlift : ∀ (D : Type u) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
      Function.Bijective
        ((Ideal.Quotient.mkₐ R J).comp : (C →ₐ[R] D) → C →ₐ[R] D ⧸ J)) :
    IsZero (cotangentComplex κ (Arrow.mk (CommRingCat.ofHom (algebraMap R C)))) ∧
      ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj
        (cotangentComplex κ (Arrow.mk (CommRingCat.ofHom (algebraMap R C))))) := by
  have : FormallyEtale R C := FormallyEtale.iff_comp_bijective.mpr
    (fun {D} _ _ J hJ ↦ hlift D J hJ)
  have : Etale R C := { formallyEtale := inferInstance, finitePresentation := inferInstance }
  let f := Arrow.mk (CommRingCat.ofHom (algebraMap R C))
  have hTor : ∀ i : ℕ, 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (arrowModule f)).obj (arrowModule f)) := by
    intro i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have : Module.Flat R (arrowModule f) := by
      change (algebraMap R C).Flat
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    exact flat_tor_vanishing R (arrowModule f) n
  have hDiagonal : IsZero (cotangentComplex κ (diagonalCotangentArrow f)) := by
    let d := diagonalCotangentArrow f
    apply derived_diagonal_cotangent_vanishing κ d.hom
      (projectiveResolution
        ((ModuleCat.restrictScalars d.hom.hom).obj (ModuleCat.of C C)))
    apply flat_surjection_diagonal d.hom
    · let : Algebra f.left f.right := f.hom.hom.toAlgebra
      intro c
      refine ⟨TensorProduct.tmul f.left c 1, ?_⟩
      exact mul_one c
    · change (@Algebra.TensorProduct.lmul' R C _ _ (algebraMap R C).toAlgebra).Flat
      rw [toAlgebra_algebraMap]
      exact WeaklyEtale.flat_lmul' R C
  have hZero := cotangentComplex_isZero_of_tor_and_diagonal κ f hTor hDiagonal
  exact ⟨hZero, fun i ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).map_isZero
    hZero⟩

end Algebra.CotangentResolution

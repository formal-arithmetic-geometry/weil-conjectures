/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# The long exact sequence of compactly supported cohomology

A morphism `f : K ⟶ L` of Weil complexes induces Frobenius-equivariant maps
`H_c^r(X ⊗ k̄, K) → H_c^r(X ⊗ k̄, L)`, and a distinguished triangle `K → L → M → K[1]` gives exact
sequences `H_c^r(K) → H_c^r(L) → H_c^r(M)`: the direct image with compact support `Ra_!` is
triangulated, the cohomology sheaves form a homological functor, and the global sections of Weil
sheaves on `Spec k₀`, which are sections on the spectrum of the algebraically closed field `k̄`,
form an exact functor.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.globalSectionsFunctor`: the global sections of the underlying
  sheaves of Weil sheaves, as a functor; it is exact on `Spec k₀`
  (`AlgebraicGeometry.WeilSheaf.exact_map_globalSectionsFunctor`).
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyMap`: the map induced on compactly
  supported cohomology, commuting with the Frobenius
  (`AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyMap_frobenius`).
- `AlgebraicGeometry.WeilComplex.exact_compactlySupportedCohomologyMap`: exactness in the middle
  for a distinguished triangle, and
  `AlgebraicGeometry.WeilSheaf.exact_compactlySupportedCohomologyMap` for a short exact sequence
  of Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

section GlobalSectionsFunctor

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The global sections `Γ(X̄, F)` of the underlying sheaf of a Weil sheaf, as a functor. -/
noncomputable abbrev globalSectionsFunctor : WeilSheaf k₀ l X ⥤ WeilCoefficients.{u} l :=
  sheafFunctor k₀ l X ⋙ Sheaf.Γ _ _

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

instance : PreservesFiniteLimits (sheafFunctor k₀ l X) := by
  unfold sheafFunctor
  infer_instance

instance : PreservesFiniteLimits (globalSectionsFunctor k₀ l X) := by
  unfold globalSectionsFunctor
  infer_instance

instance : (globalSectionsFunctor k₀ l X).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)).Additive := Functor.additive_of_preserves_binary_products _
  have : (sheafFunctor k₀ l X).Additive := inferInstanceAs
    (ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _).Additive
  unfold globalSectionsFunctor
  infer_instance

instance : IsIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsIso (𝟙 _))

instance : LocallyOfFiniteType (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

/-- The geometric fiber of `Spec k₀` is the spectrum of the algebraic closure `k̄`. -/
noncomputable def geometricFiberSpecIso :
    Spec (.of (AlgebraicClosure k₀)) ≅
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (asIso (pullback.snd (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
    (Scheme.specAlgebraicClosure k₀).hom)).symm

/-- The global sections on the geometric fiber `Spec k₀ ⊗ k̄ ≅ Spec k̄` preserve
epimorphisms, every pro-étale cover of the spectrum of an algebraically closed field being
split. -/
instance preservesEpimorphisms_Γ_geometricFiber_spec :
    (Sheaf.Γ (Scheme.ProEt.topology
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).PreservesEpimorphisms := by
  have := (ProEtale.upperStarLowerStarAdjunction (A := WeilCoefficients.{u} l)
    (g := (geometricFiberSpecIso k₀).hom)).isLeftAdjoint
  exact Functor.PreservesEpimorphisms.of_iso
    (ProEtale.globalSectionsUpperStarIso (WeilCoefficients.{u} l) (geometricFiberSpecIso k₀))

instance : (globalSectionsFunctor k₀ l (Spec (CommRingCat.of k₀))).PreservesEpimorphisms := by
  unfold globalSectionsFunctor
  infer_instance

/-- The global sections of Weil sheaves on `Spec k₀` form an exact functor: they are left exact,
and they preserve epimorphisms, being sections on the spectrum of `k̄`. -/
theorem exact_map_globalSectionsFunctor {S : ShortComplex (WeilSheaf k₀ l (Spec (.of k₀)))}
    (hS : S.Exact) : (S.map (globalSectionsFunctor k₀ l (Spec (.of k₀)))).Exact := by
  have : (globalSectionsFunctor k₀ l (Spec (.of k₀))).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact hS.map _

end GlobalSectionsFunctor

end WeilSheaf

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The map `H_c^r(X ⊗ k̄, K) → H_c^r(X ⊗ k̄, L)` induced by a morphism of Weil complexes: the
global sections of `𝓗ʳ(Ra_! f)`. -/
noncomputable def compactlySupportedCohomologyMap {K L : WeilComplex k₀ l X} (f : K ⟶ L)
    (r : ℤ) :
    (K.compactlySupportedCohomology r).carrier →ₗ[PadicAlgCl l]
      (L.compactlySupportedCohomology r).carrier :=
  ((WeilCoefficients.toModuleCat l).map (WeilSheaf.globalSectionsMap
    ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map f)))).hom

/-- The map induced on compactly supported cohomology commutes with the Frobenius. -/
theorem compactlySupportedCohomologyMap_frobenius {K L : WeilComplex k₀ l X} (f : K ⟶ L)
    (r : ℤ) (x : (K.compactlySupportedCohomology r).carrier) :
    compactlySupportedCohomologyMap f r ((K.compactlySupportedCohomology r).frobenius x) =
      (L.compactlySupportedCohomology r).frobenius (compactlySupportedCohomologyMap f r x) := by
  have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
    (WeilSheaf.globalSectionsMap_comp_frobeniusHom
      ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map f)))
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The cohomology sheaves of the direct image with compact support of a distinguished triangle
of Weil complexes form an exact sequence of Weil sheaves on `Spec k₀`. -/
theorem exact_homologySheaf_derivedLowerShriek {T : Triangle (WeilComplex k₀ l X)}
    (hT : T ∈ distTriang _) (r : ℤ) :
    (ShortComplex.mk
      ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₁))
      ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₂))
      (by rw [← Functor.map_comp, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT,
        Functor.map_zero, Functor.map_zero])).Exact := by
  let Φ := derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
  have hT' := (WeilComplex.objectProperty k₀ l (Spec (.of k₀))).ι.map_distinguished _
    (Φ.map_distinguished T hT)
  have h := (_root_.DerivedCategory.homologyFunctor _ r).map_distinguished_exact _ hT'
  have := (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).preservesKernels_ι
  have : (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).ι.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact (ShortComplex.exact_map_iff_of_faithful _
    (WeilSheaf.objectProperty k₀ l (Spec (.of k₀))).ι).1 h

/-- **Long exact sequence of compactly supported cohomology.** For a distinguished triangle
`K → L → M → K[1]` of Weil complexes, the sequence
`H_c^r(X ⊗ k̄, K) → H_c^r(X ⊗ k̄, L) → H_c^r(X ⊗ k̄, M)` is exact. -/
theorem exact_compactlySupportedCohomologyMap {T : Triangle (WeilComplex k₀ l X)}
    (hT : T ∈ distTriang _) (r : ℤ) :
    Function.Exact (compactlySupportedCohomologyMap T.mor₁ r)
      (compactlySupportedCohomologyMap T.mor₂ r) := by
  have h := WeilSheaf.exact_map_globalSectionsFunctor k₀ l
    (exact_homologySheaf_derivedLowerShriek hT r)
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h

end WeilComplex

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Long exact sequence of compactly supported cohomology** for a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of Weil sheaves: `H_c^r(F₁) → H_c^r(F₂) → H_c^r(F₃)` is exact. -/
theorem exact_compactlySupportedCohomologyMap {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (r : ℤ) :
    Function.Exact (WeilComplex.compactlySupportedCohomologyMap (toComplex.map S.f) r)
      (WeilComplex.compactlySupportedCohomologyMap (toComplex.map S.g) r) :=
  WeilComplex.exact_compactlySupportedCohomologyMap (singleTriangle_distinguished hS) r

end WeilSheaf

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-!
# Flatness of `𝒪_{E,X}` and `E_X` over `ℤ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X`
a scheme. The coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` on `X_proét`
are flat abelian sheaves: tensoring with them is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_padicIntegersRingObj` and
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_tensorLeft_continuousMapRingObj`).

Indeed, `T_X ≅ C(-, T)_X` for `T = 𝒪_E, E`
(`AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`),
and the sections `C(U, T)` of the latter are torsion-free, hence flat, abelian groups, so that
tensoring with it preserves monomorphisms
(`CategoryTheory.Sheaf.preservesMonomorphisms_tensorLeft_of_flat`), and it is right exact.

Consequently the derived pushforwards of `𝒪_E`- and `E`-module objects commute with forgetting
to abelian sheaves
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarCompMapDerivedCategoryForgetIso`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

/-- Continuous maps into a torsion-free topological additive monoid form a torsion-free
additive monoid. -/
lemma ULift.isAddTorsionFree_continuousMap (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]
    [AddMonoid T] [ContinuousAdd T] [IsAddTorsionFree T] :
    IsAddTorsionFree (ULift.{w} C(S, T)) :=
  ⟨fun _ hn _ _ h ↦ ULift.ext _ _ (ContinuousMap.ext fun s ↦
    nsmul_right_injective hn (congrArg (fun z : ULift.{w} C(S, T) ↦ z.down s) h))⟩

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

/-- For a Hausdorff, totally disconnected topological ring `T` which is torsion-free as an abelian
group, tensoring with the coefficient ring object `T_X = p_X^* T̲` preserves monomorphisms:
`T_X ≅ C(-, T)_X`, whose sections are torsion-free, hence flat, abelian groups. -/
lemma preservesMonomorphisms_tensorLeft_continuousMapComparison (T : Type) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] [T2Space T] [TotallyDisconnectedSpace T] [IsAddTorsionFree T] :
    (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ).PreservesMonomorphisms := by
  have hflat (U : X.ProEtᵒᵖ) : Module.Flat ℤ (((sheafCompose (ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)).obj.obj U) := by
    have := ULift.isAddTorsionFree_continuousMap.{u + 1} U.unop.left T
    have : Module.IsTorsionFree ℤ (ULift.{u + 1} C(U.unop.left, T)) := inferInstance
    exact inferInstanceAs (Module.Flat ℤ (ULift.{u + 1} C(U.unop.left, T)))
  have := Sheaf.preservesMonomorphisms_tensorLeft_of_flat (ProEt.topology X) _ hflat
  have := isIso_continuousMapComparison X T
  exact Functor.PreservesMonomorphisms.of_iso
    ((tensoringLeft _).mapIso (asIso (continuousMapComparison X T)).symm)

/-- Tensoring with an abelian sheaf on `X_proét` is exact as soon as it preserves monomorphisms,
being right exact. -/
lemma preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [(tensorLeft A).PreservesMonomorphisms] :
    PreservesFiniteLimits (tensorLeft A) := by
  have : (tensorLeft A).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (tensorLeft A).preservesFiniteLimits_of_preservesHomology

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- **`𝒪_{E,X}` is flat over `ℤ`**: tensoring with `𝒪_{E,X} = p_X^* 𝒪̲_E` is exact. -/
instance preservesFiniteLimits_tensorLeft_padicIntegersRingObj :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have := PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E
  have : CharZero E := (algebraMap E (PadicAlgCl ℓ)).charZero
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X (PadicAlgCl.integers ℓ E)
  preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

end Integers

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- **`E_X` is flat over `ℤ`**: tensoring with `E_X = p_X^* E̲` is exact. -/
instance preservesFiniteLimits_tensorLeft_continuousMapRingObj :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :=
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X E.1
  preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

end AlgebraicGeometry.ProEtale

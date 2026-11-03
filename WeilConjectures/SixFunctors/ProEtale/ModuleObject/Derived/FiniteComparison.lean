/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DualizingComplex
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleComparison

/-! # The finite comparison data needed for coefficient biduality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite comparison provides a constructible etale origin and preserves the two Hom
mates at that origin. It identifies the actual constructible exceptional image of the
unit, but makes no assertion about any double-dual morphism.

Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i).
(blueprint: lem-pd-finite-coefficient-comparison-witness).

Proof: use the finite discrete encoding and its coefficient-ring isomorphism to realize
constant-coefficient etale modules in the given internal module category. Finite
constructible comparison gives an etale origin of K. The symmetric tensor comparison
makes this realization braided. Compact-support comparison identifies its right adjoint
with the published constructible exceptional inverse image by adjunction uniqueness.
Apply this identification to the unit to obtain w, with the compact-support counit
normalization. For each constructible test object, tensor-Hom adjunction and tensor
comparison identify the Hom mate. The tests generate, so the mate is invertible, first
at L and then at its constructible Verdier dual. Transport these constructions along
the supplied coefficient-ring isomorphism. This includes the zero ring and empty scheme;
the equivalences and adjunction uniqueness do not require a nonzero coefficient ring.
-/
theorem finiteCoefficientComparisonWitness
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hbase : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    letI : HasCompactification X.hom := (NagataCompactification X.hom).hasCompactification
    ∃ (F : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ X.left))
      (_ : F.Braided)
      (L : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))))
      (w : F.obj (Etale.dualizingComplex (ULift.{u + 1} A) X.hom) ≅
        coefficientCaseDualizingComplex ell k hbase Λ hΛ X)
      (eK : F.obj L ≅ K.obj),
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.left L ∧
      IsIso ((Functor.LaxMonoidal.ihomComparison F L).natTrans.app
        (Etale.dualizingComplex (ULift.{u + 1} A) X.hom)) ∧
      IsIso ((Functor.LaxMonoidal.ihomComparison F
        ((ihom L).obj (Etale.dualizingComplex (ULift.{u + 1} A) X.hom))).natTrans.app
          (Etale.dualizingComplex (ULift.{u + 1} A) X.hom)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

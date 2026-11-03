/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Integration with the current discrete condensed finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-d-integral/def-trf-integration.md
(blueprint: def-trf-integration). The proper comparison is the inverse of the canonical
map from compact supports to ordinary direct image. The exceptional datum below is
exactly the datum selected by FiniteRingTrace.exceptional, including its counit.
The coefficient scalar is the degree-zero endomorphism evaluated at the unit section.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

namespace FiniteRingTrace

variable (A : Type) [CommRing A] [Finite A]

/-- Constant scalars act through their constant global sections, pulled to the scheme.
Source: the coefficient convention in def-trf-integration (blueprint: def-trf-integration). -/
def scalarRingHom (Y : Scheme.{u}) : A →+* MonObj.Γ (condensedRingObj (coefficient A) Y) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  letI : (upperStarFromPoint Y).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
        (toSpecZ Y))).isLeftAdjoint
  letI : PreservesBinaryBiproducts (upperStarFromPoint Y) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  letI : (upperStarFromPoint Y).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
    (Profinite.continuousMapConstRingHom A)

/-- The standard coefficient-linear structure on internal modules. The usual derived
linear instance then supplies the scalar action on Ambient, without transported morphisms.
Source: coefficient action in lem-trf-integration-linear (blueprint: lem-trf-integration-linear). -/
instance moduleLinear (Y : Scheme.{u}) :
    Linear A (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (coefficient A) Y)) :=
  Mod.linearOfRingHom (scalarRingHom A Y)

/-- Expose the same selected constructible adjunction as exceptional, rather than choosing
another right adjoint. Source: sk-thm-existence (3)--(4) (blueprint: def-trf-admissibility). -/
def integrationExceptionalData (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k))) [IsProper Y.hom] :
    letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
    letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
    letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
    CurrentConstructibleExceptionalData (coefficient A) (Over.mkIdTerminal.from Y) := by
  letI := fieldChar D
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let hcoeff : IsLocalizingAdmissibleCoefficient ell (coefficient A) :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩
  exact currentConstructibleExceptionalData (coefficient A) ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) (Over.mkIdTerminal.from Y) hcoeff

/-- The left functor of exactly the exceptional datum defining dualizingComplex.
Source: the constructible adjunction (blueprint: def-trf-admissibility). -/
def integrationLower (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k))) [IsProper Y.hom] :
    Ctf A Y.left ⥤ Ctf A (Spec (.of D.k)) := by
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  exact (integrationExceptionalData A D ell hell hA Y).lower

/-- The canonical map from compact supports to ordinary direct image: transpose the
extension-by-zero counit under pullback/direct image, push along the proper factor,
and use ordinary direct-image composition. This is the usual comparison for the chosen
compactification, normalized by the identity on the open part.
Source: the proper identification in def-trf-integration (blueprint: def-trf-integration). -/
def supportToOrdinary {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (K : Ambient A X) :
    (rightDerivedLowerShriekOfCompactification (coefficient A) c).obj K ⟶
      ((lowerStar (coefficient A) f).rightDerivedFunctor).obj K :=
  letI : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (coefficient A) c.i).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  ((lowerStar (coefficient A) c.g).rightDerivedFunctor).map
    (((derivedUpperStarLowerStarAdjunction (coefficient A) c.i).homEquiv _ _)
      ((leftDerivedUpperStarIsoMapDerivedCategory (coefficient A) c.i).hom.app _ ≫
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (coefficient A) c.i).unit.app K))) ≫
    (rightDerivedLowerStarComp (coefficient A) c.i c.g).hom.app K ≫
    (eqToIso (congrArg (fun g ↦ ((lowerStar (coefficient A) g).rightDerivedFunctor).obj K)
      c.comm.symm)).hom

/-- For a proper f the canonical support comparison is invertible, with the identity
normalization on the trivial compactification. Source: the proper-comparison clause of
prop-compactification-coherence-detailed and def-trf-integration
(blueprint: lem-trf-proper-support-comparison).

Proof: the open immersion c.i is proper by cancellation from c.i ≫ c.g = f and the
separatedness of c.g. It is therefore also closed. Extension by zero equals direct image
for this clopen immersion, and the transposed counit is this canonical identification.
Its derived version is invertible; pushforward and the composition isomorphism preserve
invertibility. For the trivial compactification the transposed identity-open counit is
the identity, giving the stated normalization and the same common-refinement comparison. -/
theorem supportToOrdinary_isIso {X Z : Scheme.{u}} {f : X ⟶ Z} [IsProper f]
    (c : Compactification f) (K : Ambient A X) : IsIso (supportToOrdinary A c K) := by
  sorry


end FiniteRingTrace

end WeilConjectures

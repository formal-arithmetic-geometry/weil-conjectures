/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.Paper.FiniteClopenExceptionalRestriction
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.PullbackTorAmplitude
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The section invariant in intrinsic finite-coefficient coordinates

Source: blueprint master, sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: def-pur-section-invariant).

This equivalent interface uses the canonical constant-ring realization and the
published finite exceptional functor. It avoids mixing the retired pro-etale
pullback API with the finite-coefficient API. The data remain Ls* Rg! A_B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The original site fits its object universe, with no extra scalar universe to infer.
Source: small pro-etale site convention (blueprint: def-pur-section-invariant). -/
instance (priority := 2000) intrinsicSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

/-- Finiteness of the actual positive coefficient quotient, by the published theorem.
Source: finite coefficient convention (blueprint: def-pur-section-invariant). -/
instance intrinsicCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The constant coefficient object in degree zero in the recorded intrinsic category.
Source: section-invariant definition, Lambda_B (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    proEtaleDerivedCategory T P.Ring :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- The existing K-flat derived tensor, with independent site and coefficient universes.
Source: section-invariant tensor invertibility (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  let R := (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} P.Ring))
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology T)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} P.Ring)))

/-- Actual exceptional image of the coefficient unit, using the specified etale adjoint
and the two canonical site comparisons. Source: omega_g in the section-invariant definition
(blueprint: def-pur-section-invariant). -/
def intrinsicDualizing (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] : proEtaleDerivedCategory V P.Ring :=
  (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification g)).obj
    (P.intrinsicCoefficientUnit B)

/-- The actual derived pullback Ls* Rg! A_B, with no choice of an orientation.
Source: section-invariant displayed definition (blueprint: def-pur-section-invariant). -/
def sectionInvariantIntrinsic (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :
    proEtaleDerivedCategory B P.Ring :=
  (Scheme.sfIntrinsicDerivedPullback P.Ring s).obj (P.intrinsicDualizing g)

/-- The invariant is tensor-invertible in the exact recorded finite-Tor category.
Smooth relative dimension may vary; no Tate orientation is supplied.
Source: section-invariant invertibility paragraph (blueprint: def-pur-section-invariant).
Proof: split the finite-type smooth source into its finitely many clopen relative-dimension
loci and use thm-pur-cohomological-smoothness on each. Reassemble the relative dualizing
object and its inverse along this finite partition. Derived inverse image preserves the
coefficient unit and tensor product. Pulling the two inverse isomorphisms along the section
gives the asserted two-sided inverse. Bounded constructibility and a uniform finite Tor
interval descend from the finite partition and are preserved by inverse image. The
canonical coefficient realization identifies precisely finiteTorConstructible, including
empty schemes and the dimension-zero identity section. -/
theorem sectionInvariantIntrinsic_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g] [Smooth g]
    [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantIntrinsic g s) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantIntrinsic g s, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantIntrinsic g s) ≅ P.intrinsicCoefficientUnit B) := by
  sorry

/-- Nagata supplies the compactification from the source hypotheses, with no added
exceptional-adjoint condition. Source: section-invariant finite-type setting
(blueprint: def-pur-section-invariant).
Proof: B is Noetherian since it is finite type over a field. The separated finite-type
map g therefore admits a compactification by Nagata. Smoothness in particular supplies
local finite type; quasi-compactness supplies finite type. -/
theorem sectionCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    HasCompactification g := by
  exact (P.comparedCompactification g aB).hasCompactification

/-- The section invariant on precisely the finite-type domain of the source.
Compactifiability is a consequence, rather than an additional assumption.
Source: displayed definition C(g,s) (blueprint: def-pur-section-invariant). -/
def sectionInvariantFinite (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    proEtaleDerivedCategory B P.Ring :=
  let _ := hs
  letI := P.sectionCompactifiable g aB
  P.sectionInvariantIntrinsic g s

/-- Tensor invertibility with all auxiliary admissibility hypotheses discharged.
Source: section-invariant Picard assertion (blueprint: def-pur-section-invariant).
Proof: use sectionCompactifiable and sectionInvariantIntrinsic_invertible. Their
coefficient objects and pullback are exactly the definition sectionInvariantFinite,
so the same finite-Tor inverse and its two tensor isomorphisms give the result. -/
theorem sectionInvariantFinite_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantFinite g aB s hs) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantFinite g aB s hs, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantFinite g aB s hs) ≅ P.intrinsicCoefficientUnit B) := by
  let := P.sectionCompactifiable g aB
  exact P.sectionInvariantIntrinsic_invertible g aB s hs

end WeilConjectures.PurityFiniteSetting

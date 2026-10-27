/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.Paper.FiniteTorAmplitudeSites
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Perfectness of the four cohomology point complexes

Source: Weil blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
statement and Proof Steps 1–3 (blueprint: sk-lem-finite).

The two choices of C are ordinary and compactly supported sections. The two
choices of B are C and its point dual RHom(C, Λ). Quotient index n means n+1.
The algebraically closed case retains the input's actual common coefficient stage,
then uses its canonical realization in D(Qbar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The native small-Hom localization of ordinary coefficient modules.
Source: Stacks 05RU; blueprint sk-def-perfect as used in sk-lem-finite
(blueprint: sk-lem-finite). -/
instance poincarePointModuleDerived (R : Type u) [CommRing R] :
    HasDerivedCategory.{u} (ModuleCat.{u} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u} R)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (d : ℕ) (S : PoincareDualitySetting D.k₀ d)

/-- The model's LocallyOfFiniteType structure, exposed through the standard Over projection.
Source: blueprint sk-def-set, used in sk-lem-finite (blueprint: sk-lem-finite). -/
instance poincarePointModelFiniteType :
    LocallyOfFiniteType (Over.mk S.modelStructureMorphism).hom :=
  inferInstanceAs (LocallyOfFiniteType S.modelStructureMorphism)

/-- The model's QuasiCompact structure, exposed through the standard Over projection.
Source: blueprint sk-def-set, used in sk-lem-finite (blueprint: sk-lem-finite). -/
instance poincarePointModelQuasiCompact :
    QuasiCompact (Over.mk S.modelStructureMorphism).hom :=
  inferInstanceAs (QuasiCompact S.modelStructureMorphism)

/-- The model's IsSeparated structure, exposed through the standard Over projection.
Source: blueprint sk-def-set, used in sk-lem-finite (blueprint: sk-lem-finite). -/
instance poincarePointModelSeparated :
    IsSeparated (Over.mk S.modelStructureMorphism).hom :=
  inferInstanceAs (IsSeparated S.modelStructureMorphism)

/-- Separatedness of the specified base change, from the standard pullback instance.
Source: blueprint sk-def-set, used in sk-lem-finite (blueprint: sk-lem-finite). -/
instance poincarePointGeometricSeparated :
    IsSeparated ((D.geometricFiber (Over.mk S.modelStructureMorphism)).left ↘
      Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd S.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- At finite coefficients, ordinary and compact cohomology and their point duals
are dualizable, bounded with finite cohomology, and have finite Tor amplitude.
Source: Weil blueprint main-20261015, sk-lem-finite (blueprint: sk-lem-finite).
Proof: Step 1 applies separated finite-type base change and the finite dimension bound.
Apply clause 1 of thm-pod-point-perfectness to K. Its finite free representatives
are finite projective, hence give the dualizable point complexes of sk-def-perfect.
This is exactly Step 2 of the node proof, without properness or a Weil structure. -/
theorem poincarePointFiniteness_finite (hl : l ≠ D.p)
    (c : Compactification
      ((D.geometricFiber (Over.mk S.modelStructureMorphism)).left ↘ Spec (.of D.k)))
    (n : ℕ) (hn : 1 ≤ n)
    (K : finiteTorConstructibleCategory l E n hn
      (D.geometricFiber (Over.mk S.modelStructureMorphism)).left) :
    ∀ C ∈ ({finiteOrdinarySections D l E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left n hn K.obj,
        finiteCompactSections D l E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left c n hn K.obj} :
      Set (DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))),
      ∀ B ∈ ({C, (ihom C).obj (𝟙_ _)} : Set _),
        IsDualizable B ∧ DerivedCategory.TStructure.t.bounded B ∧
          (∀ i : ℤ, Finite ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
            i).obj B)) ∧
          DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) B := by
  sorry

/-- At integral coefficients all four point complexes are perfect with bounded
finitely generated cohomology. Their finite reductions are perfect in one Tor interval.
Source: Weil blueprint main-20261015, sk-lem-finite (blueprint: sk-lem-finite).
Proof: Step 1 supplies separated finite-type geometry and a dimension bound.
Step 3 applies clause 2 of thm-pod-point-perfectness to the same integral K.
The point complexes are bounded with finitely generated cohomology and bounded
finite projective representatives. Their reductions agree with the finite-level
complexes of K_n and have a Tor interval independent of n. Duals here are point
duals, so no identification with a sheaf coefficient dual is used. -/
theorem poincarePointFiniteness_integral (hl : l ≠ D.p)
    (c : Compactification
      ((D.geometricFiber (Over.mk S.modelStructureMorphism)).left ↘ Spec (.of D.k)))
    (K : finiteTorConstructibleIntegralCategory l E
      (D.geometricFiber (Over.mk S.modelStructureMorphism)).left) :
    ∀ C ∈ ({(integralOrdinarySections D l hl E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left
          ⟨K.obj, K.property.1⟩).obj,
        (integralCompactSections D l hl E (D.geometricFiber (Over.mk S.modelStructureMorphism)).left
          c ⟨K.obj, K.property.1⟩).obj} :
      Set (DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))),
      ∀ B ∈ ({C, (ihom C).obj (𝟙_ _)} : Set _),
        IsDualizable B ∧ DerivedCategory.TStructure.t.bounded B ∧
          (∀ i : ℤ, Module.Finite
            (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
            ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) i).obj B)) ∧
          ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
            IsDualizable ((pointReductionModuleTensor l E n).obj B) ∧
              DerivedCategory.torAmplitudeIn.{u + 1, u + 1, u + 2} (ModuleCat.{u + 1}
                (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) a b
                ((pointReductionModuleTensor l E n).obj B) := by
  sorry

/-- At the rational field stage all four point complexes are perfect and have
bounded finite-dimensional cohomology.
Source: Weil blueprint main-20261015, sk-lem-finite (blueprint: sk-lem-finite).
Proof: Step 1 gives the geometric hypotheses of thm-pod-point-perfectness.
Step 4 applies its clause 3 to the rational coefficient object. The field
characterization in sk-def-perfect identifies bounded finite-dimensional cohomology
with perfectness. This treats both ordinary and compact sections and both point duals. -/
theorem poincarePointFiniteness_rational (hl : l ≠ D.p)
    (c : Compactification
      ((D.geometricFiber (Over.mk S.modelStructureMorphism)).left ↘ Spec (.of D.k)))
    (K : finiteTorFieldCoefficientCategory
      (sfRationalConstructibleCategory l E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left)) :
    ∀ C ∈ ({(rationalOrdinarySections D l hl E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left K).obj,
        (rationalCompactSections D l hl E
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left c K).obj} :
      Set (DerivedCategory (ModuleCat.{u} E))),
      ∀ B ∈ ({C, (ihom C).obj (𝟙_ _)} : Set _),
        IsDualizable B ∧ DerivedCategory.pointFiniteDimensional E B := by
  sorry

/-- At the algebraically closed field stage the canonical common-stage
realizations of all four point complexes are perfect with bounded finite-dimensional cohomology.
Source: Weil blueprint main-20261015, sk-lem-finite (blueprint: sk-lem-finite).
Proof: Step 1 verifies separated finite-type geometry. Step 4 applies clause 3
of thm-pod-point-perfectness at the algebraically closed coefficient stage.
All constructions use the recorded finite-stage object and scalar extension, so
the field characterization of sk-def-perfect applies to its realized point complex
and its ordinary coefficient dual, and likewise to compact support. -/
theorem poincarePointFiniteness_qbar (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c : Compactification
      ((D.geometricFiber (Over.mk S.modelStructureMorphism)).left ↘ Spec (.of D.k)))
    (K : finiteTorFieldCoefficientCategory
      (generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left)) :
    ∀ C ∈ ({(DerivedCategory.pointFdQbarRealization l Ω).obj
          (qbarOrdinarySections D l hl
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left Ω K),
        (DerivedCategory.pointFdQbarRealization l Ω).obj
          (qbarCompactSections D l hl
          (D.geometricFiber (Over.mk S.modelStructureMorphism)).left Ω c K)} :
      Set (DerivedCategory (ModuleCat.{u} Ω))),
      ∀ B ∈ ({C, (ihom C).obj (𝟙_ _)} : Set _),
        IsDualizable B ∧ DerivedCategory.pointFiniteDimensional Ω B := by
  sorry

end WeilConjectures

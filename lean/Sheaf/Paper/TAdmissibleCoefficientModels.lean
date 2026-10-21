/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel

/-!
# T-admissibility and its scalar local models

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: def-zl-t-admissible-coefficient-models).

## Main definitions

- `IsTAdmissible`: regular coherent scalar coefficients and flat profinite evaluations.
- `HasScalarLocalModels`: the existing finite constant local models on some pro-etale cover.
- `dualizableProperty`, `HasRestrictedStandardTStructure`: the inherited derived notions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The actual section-ring sheaf of the condensed coefficient ring.
Source: HRS Section 3 (blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev scalarRingSheaf : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  sectionRingSheaf (coherentTopology Profinite.{u}) Λ.X

/-- The ring R = Γ(*, Λ), evaluated at the terminal profinite set.
Source: HRS Definition 6.1 (blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev scalarRing : CommRingCat.{u + 1} :=
  (scalarRingSheaf Λ).obj.obj (op (⊤_ Profinite.{u}))

/-- The scalar map to sections on S is restriction along its unique map to the point.
Source: HRS Definition 6.1 (blueprint: def-zl-t-admissible-coefficient-models). -/
def scalarSectionMap (S : Profinite.{u}) :
    scalarRing Λ →+* (scalarRingSheaf Λ).obj.obj (op S) :=
  ((scalarRingSheaf Λ).obj.map (terminal.from S).op).hom

/-- T-admissibility: coherence, finite finite-projective resolutions of all finitely
presented modules, and flat restriction to extremally disconnected profinite sets.
A module in degree zero is perfect precisely when it has the stated finite resolution.
Source: HRS Definition 6.1 and Proposition 6.6
(blueprint: def-zl-t-admissible-coefficient-models). -/
def IsTAdmissible : Prop :=
  (∀ I : Ideal (scalarRing Λ), I.FG → Module.FinitePresentation (scalarRing Λ) I) ∧
  (∀ N : ModuleCat.{u + 1} (scalarRing Λ), Module.FinitePresentation (scalarRing Λ) N →
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N)) ∧
  (∀ S : Profinite.{u}, ExtremallyDisconnected S → (scalarSectionMap Λ S).Flat)

/-- The ambient category uses ordinary derived tensor and the degree-zero coefficient unit.
Source: HRS Definition 3.3 (blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev LisseAmbient (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))

/-- Zariski locally finite irreducible components, with no quasi-compactness requirement.
Source: HRS Theorem 6.2(2) (blueprint: def-zl-t-admissible-coefficient-models). -/
def HasLocallyFiniteIrreducibleComponents (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (irreducibleComponents U).Finite

/-- The full subcategory consists of objects with evaluation and coevaluation satisfying
both triangle identities for ordinary derived tensor: the existing `IsDualizable`
(a right dual with an exact pairing), packaged as an object property.
Source: HRS Definition 3.3(1) (blueprint: def-zl-t-admissible-coefficient-models). -/
def dualizableProperty (X : Scheme.{u}) : ObjectProperty (LisseAmbient Λ X) :=
  fun K ↦ IsDualizable K

/-- Scalar local models: the existing finite constant local models on some pro-etale cover,
`M|_{U_i} ≅ Λ_{U_i} ⊗_{Λ(*)} P_i` with P_i finitely presented over Λ(*), extended along the
canonical constant-section map. The module P_i may vary with the member of the cover.
Source: HRS Theorem 6.2(2); blueprint det-def-sfb-constructible-local-model
(blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev HasScalarLocalModels (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, HasFiniteConstantLocalModelOnCover Λ.X M U

/-- The restricted t-structure has exactly the ambient nonpositive and nonnegative objects.
Its triangulation and shifts are the inherited ones on the full subcategory.
Source: HRS Theorem 6.2(2) (blueprint: def-zl-t-admissible-coefficient-models). -/
def HasRestrictedStandardTStructure (X : Scheme.{u})
    (h : (dualizableProperty Λ X).IsTriangulated) : Prop :=
  letI := h
  ∃ t : CategoryTheory.Triangulated.TStructure (dualizableProperty Λ X).FullSubcategory,
    (∀ (n : ℤ) (K : (dualizableProperty Λ X).FullSubcategory),
      t.le n K ↔ DerivedCategory.TStructure.t.le n K.obj) ∧
    (∀ (n : ℤ) (K : (dualizableProperty Λ X).FullSubcategory),
      t.ge n K ↔ DerivedCategory.TStructure.t.ge n K.obj)

end AlgebraicGeometry.ProEtale.CondensedRing

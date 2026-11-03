/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariantAllCoefficients
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SmoothPurity.PurityBaseField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible

/-!
# The section invariant over a general purity base field and coefficient

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/`def-pur-section-invariant.md`
and the coefficient convention of `def-pur-conventions.md`
(blueprint: def-pur-section-invariant).

General version of the landed interface `Sheaf.SmoothPurity.SectionInvariantAllCoefficients`
(`sectionInvariantAll`, with its proved `sectionInvariantAll_admissible` and
`sectionInvariantAllUnit_mem`), which is kept unchanged. The base is any
`K : PurityBaseField ell` (characteristic a prime different from `ell`, finite or
algebraically closed). The coefficient is any condensed ring `Λ` with
`IsLocalizingAdmissibleCoefficient ell Λ`; for the four-branch coefficient certificate of
`sectionInvariantAll` (arbitrary finite discrete `ell`-primary rings, `O_E`, `E`, `Q̄_ell`)
this is `sectionInvariantAll_admissible`. The landed declarations are the case
`K = PurityBaseField.ofDatum D ell hell` (in `Sheaf.Paper.PurityBaseField`):
`sectionInvariantAll_eq_sectionInvariantOver` for `sectionInvariantAll`, and
`sectionInvariantOver_geometric` for the older `A_{E,n}`-only `sectionInvariant`.

## Main declarations
* `purityBaseField_cd`: the cohomological-dimension input from `K.finite_or_closed`.
* `sectionInvariantUnitOver_mem`: the literal unit is ctf over any `K`.
* `sectionInvariantOver`: `Ls^* Rg^! Λ_B` over `K`;
  `sectionInvariantOver_mem_and_tensor_inverse`: its Picard property.
* `sectionInvariantAll_eq_sectionInvariantOver`, `sectionInvariantOver_geometric`:
  the landed declarations as the case `K = ofDatum D ell hell`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite cohomological dimension of a purity base field, from its finite-or-closed
alternative: `cd_ell(K) <= 1` for finite `K` and `cd_ell(K) = 0` for algebraically closed `K`
(det-base-field-cd-finite-field, both clauses).
Source: Wei Yang #1412 item 18 (blueprint: def-pur-section-invariant).
Proof (postponed): `exceptionalCurrentFieldCD` applied to `K.finite_or_closed`. -/
theorem purityBaseField_cd (ell : ℕ) [Fact ell.Prime]
    (K : WeilConjectures.PurityBaseField.{u} ell) : BaseFieldFiniteCD ell K.K := by
  sorry

section Invariant

variable (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ha : IsLocalizingAdmissibleCoefficient ell Λ)

/-- The literal unit lies in `D^b_ctf` over any finite-type separated `K`-scheme.
Source: unit clause of def-pur-section-invariant (blueprint: def-pur-section-invariant).
Proof: the proof of the landed `sectionInvariantAllUnit_mem` (K4), which uses no property of
the base field: `B` is finite type over a field, hence locally Noetherian and quasi-compact;
the degree-zero coefficient object is ctf (`constantCoefficientObject_mem`,
lem-trf-coefficient-unit-ctf) and `DerivedCategory.singleFunctorObjUnitIso` identifies it with
the literal unit; both properties are closed under isomorphisms. -/
theorem sectionInvariantUnitOver_mem (B : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] :
    (constantModelBoundedConstructible Λ B.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (sectionInvariantUnit Λ B.left) := by
  let : IsLocallyNoetherian B.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.hom
  let : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have := (constantModelConstructibleFiniteTor_wellDefined Λ B.left).2.1
  exact (constantModelBoundedConstructible Λ B.left ⊓
    _root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _) (constantCoefficientObject_mem Λ B.left)

/-- The section invariant `Ls^* Rg^! Λ_B` over a general purity base field `K` and an
admissible coefficient `Λ`: the recorded ctf exceptional inverse image of the literal unit,
pulled back along the closed section.
Source: displayed definition of def-pur-section-invariant
(blueprint: def-pur-section-invariant). -/
def sectionInvariantOver
    (B V : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (_hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) :=
  let unit : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨sectionInvariantUnit Λ B.left, sectionInvariantUnitOver_mem ell K Λ B⟩
  (moduleObjectDerivedPullback Λ s.left).obj
    ((ctfExceptionalInverseImage Λ ell K.K (purityBaseField_cd ell K) g ha).obj unit).obj

/-- The general section invariant lies in `D^b_ctf` and has a two-sided relative derived-tensor
inverse. Statement copied from `sectionInvariant_mem_and_tensor_inverse` with `D.k ↦ K.K`.
Source: invertibility clause of def-pur-section-invariant
(blueprint: def-pur-section-invariant).
Proof (postponed): node proof steps 3-6. Over every purity base field `K`: dimension loci,
the etale smooth tensor theorem over the Noetherian base (ell invertible) transported to the
pro-etale site, coefficient change from `Z/ell^N` (`sk-prop-scalar-six`) and the integral
criterion for `O_E`, `E`, `Q̄_ell`, then ctf stability of the section pullback with
`cd_ell(K) <= 1` (finite `K`) or `= 0` (closed `K`). -/
theorem sectionInvariantOver_mem_and_tensor_inverse
    (B V : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    (constantModelBoundedConstructible Λ B.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      (sectionInvariantOver ell K Λ ha B V g s hs) ∧
    ∃ P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
        (condensedRingObj Λ B.left)),
      (constantModelBoundedConstructible Λ B.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _) P ∧
      Nonempty (((derivedTensor Λ B.left).obj
        (sectionInvariantOver ell K Λ ha B V g s hs)).obj P ≅ 𝟙_ _) ∧
      Nonempty (((derivedTensor Λ B.left).obj P).obj
        (sectionInvariantOver ell K Λ ha B V g s hs) ≅ 𝟙_ _) := by
  sorry

end Invariant

/-- The landed interface `sectionInvariantAll` is the case `K = ofDatum D ell hell` of
`sectionInvariantOver`, with the admissibility supplied by the landed
`sectionInvariantAll_admissible`. This covers every coefficient of its four-branch
certificate, in particular arbitrary finite discrete `ell`-primary rings.
Source: def-pur-section-invariant (blueprint: def-pur-section-invariant).
Proof: `rfl`; both sides are the pullback along `s` of
`ctfExceptionalInverseImage Λ ell D.k _ g _` applied to the literal unit; the field instance of
`ofDatum` is that of `D.k`, and the remaining arguments (`Fact` instances,
`BaseFieldFiniteCD`, admissibility, unit membership) are proofs of propositions. -/
theorem sectionInvariantAll_eq_sectionInvariantOver
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    sectionInvariantAll D ell hell E n hn Λ hcoeff B V g s hs =
      sectionInvariantOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariantAll_admissible D ell hell E n hn Λ hcoeff) B V g s hs := by
  rfl

/-- The older `A_{E,n}`-only section invariant `sectionInvariant` is the special case
`K = ofDatum D ell hell`, with the admissibility produced by `sectionInvariant_admissible`.
Source: def-pur-section-invariant (blueprint: def-pur-section-invariant).
Proof (postponed, expected `rfl`): both sides unfold to the same pullback of
`ctfExceptionalInverseImage Λ ell D.k _ g _` applied to the same unit; the field instance of
`ofDatum` is that of `D.k`, and the remaining arguments (`Fact` instances, `BaseFieldFiniteCD`,
admissibility, unit membership) are proofs of propositions. -/
theorem sectionInvariantOver_geometric
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    sectionInvariant D ell hell E n hn Λ hcoeff B V g s hs =
      sectionInvariantOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell E n hn Λ hcoeff) B V g s hs := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

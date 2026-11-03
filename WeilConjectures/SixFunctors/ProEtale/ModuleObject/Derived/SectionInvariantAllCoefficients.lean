/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible

/-!
# Condensed section invariant for arbitrary finite purity coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).

The section invariant is formed in the fixed purity setting from the recorded restricted Brown
exceptional inverse image `ctfExceptionalInverseImage`, applied to the literal coefficient unit,
and then pulled back along the closed section.  The definition uses no ambient right adjoint and
no arbitrary exceptional functor.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
The fixed four-coefficient convention supplies localizing admissibility.  This is a proposition-only
interface used to type the recorded `ctfExceptionalInverseImage`; its coefficient alternatives
are exactly the purity convention.

Proof: each branch of `hcoeff` is a disjunct of
`IsLocalizingAdmissibleCoefficient`. The `O_E`, `E` and `Q̄_ell` branches are its
`padicIntegersRingObj`, `continuousMapRingObj E` and `padicAlgClRingObj` disjuncts verbatim.
The finite branch is exactly its finite discrete ell-primary disjunct, with no DVR quotient
restriction (Wei Yang #1423/#1441). Finite rings have representatives in Type 0.

Source: the coefficient list in literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors/sec-n-change/sk-prop-qlbar-two-colimit/`def-pur-conventions.md` and the
localizing coefficient interface in `Sheaf.Paper.LocalizingAdmissibleCoefficients`
(blueprint: def-pur-section-invariant).
-/
theorem sectionInvariantAll_admissible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    IsLocalizingAdmissibleCoefficient ell Λ := by
  rcases hcoeff with hA | hO | hE | hQ
  · exact Or.inl hA
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hO⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ))))

/--
The literal unit is an object of the bounded constructible finite-Tor category in the fixed
purity setting.  This named proposition is the input used to form the restricted exceptional
inverse image on the unit.

Proof: `B` is finite type over a field, hence locally Noetherian and quasi-compact, so qcqs.
The degree-zero coefficient object `Λ_B = p_B^* Λ` is bounded constructible with finite Tor
amplitude (lem-trf-coefficient-unit-ctf, `constantCoefficientObject_mem`), and
`DerivedCategory.singleFunctorObjUnitIso` identifies it with the literal unit; both properties are
closed under isomorphisms (det-def-sfb-constructible-tor-amplitude).

Source: the unit clause of `def-pur-section-invariant.md` in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/, together with the Dctf
convention of literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-constructible/sk-def-sfb-constructible/`_section.md`
(blueprint: def-pur-section-invariant).
-/
theorem sectionInvariantAllUnit_mem
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B : Over (Spec (.of D.k)))
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


/--
The section invariant is `Ls^* Rg^! Lambda_B`, with `Rg^!` the recorded ctf Brown adjoint: apply
`ctfExceptionalInverseImage` to the literal unit and then apply the total derived module pullback
along the closed section. The finite branch allows every finite commutative ell-primary ring,
as required by Wei Yang #1423/#1441. The finite-field datum and section equation are retained.

Source: the displayed definition in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).
-/
noncomputable def sectionInvariantAll
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
    (_hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let hΛ := sectionInvariantAll_admissible D ell hell E n hn Λ hcoeff
  let unit : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨sectionInvariantUnit Λ B.left,
      sectionInvariantAllUnit_mem D ell hell E n hn Λ hcoeff B⟩
  (moduleObjectDerivedPullback Λ s.left).obj
    ((ctfExceptionalInverseImage Λ ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g hΛ).obj unit).obj

end AlgebraicGeometry.ProEtale.CondensedRing

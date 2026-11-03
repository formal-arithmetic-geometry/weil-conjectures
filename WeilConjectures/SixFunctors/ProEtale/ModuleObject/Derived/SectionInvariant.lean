/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-!
# Condensed pro-etale section invariant

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
The literal coefficient unit in the pro-etale module-object derived category.

Source: the displayed unit `Lambda_B` in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).
-/
noncomputable def sectionInvariantUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (B : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B)) := 𝟙_ _

/--
The fixed four-coefficient convention supplies localizing admissibility.  This is a proposition-only
interface used to type the recorded `ctfExceptionalInverseImage`; its proof is postponed, while
its coefficient alternatives are exactly the purity convention.

Proof (postponed): each branch of `hcoeff` is a disjunct of
`IsLocalizingAdmissibleCoefficient`. The `O_E`, `E` and `Q̄_ell` branches are its
`padicIntegersRingObj`, `continuousMapRingObj E` and `padicAlgClRingObj` disjuncts verbatim.
For `A_{E,n}` with `n ≥ 1`, the ring is finite, killed by `ell ^ n`, and discrete (the ideal
`π_E^n O_E` is open); shrink it to `Type 0` and transport continuous functions along the ring
equivalence, as in the proved node lem-sf-finite-point-coefficient-admissibility.

Source: the coefficient list in literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors/sec-n-change/sk-prop-qlbar-two-colimit/`def-pur-conventions.md` and the
localizing coefficient interface in `Sheaf.Paper.LocalizingAdmissibleCoefficients`
(blueprint: def-pur-section-invariant).
-/
theorem sectionInvariant_admissible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    IsLocalizingAdmissibleCoefficient ell Λ := by
  rcases hcoeff with hA | hO | hE | hQ
  · let A := Padic.coefficientExtensionRing ell E n
    let : Finite A := Padic.finite_coefficientExtensionRing ell E n _hn
    have hmetric : (inferInstance : PseudoMetricSpace E) =
        (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField.toPseudoMetricSpace := by
      apply PseudoMetricSpace.ext
      ext x y
      change dist x y = spectralNorm (Padic ell) E (-x + y)
      rw [dist_eq_norm_neg_add]
      exact NormedAlgebra.norm_eq_spectralNorm (Padic ell) _
    have htop := congrArg (fun m : PseudoMetricSpace E ↦
      m.toUniformSpace.toTopologicalSpace) hmetric
    have hdiscrete := DerivedNakayama.quotientDiscrete ell E n
    change @DiscreteTopology A (TopologicalSpace.coinduced _
      (TopologicalSpace.induced _ _)) at hdiscrete
    rw [← htop] at hdiscrete
    let := hdiscrete
    refine Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨n, ?_⟩, hA⟩
    have h := (Padic.extension_integers_dvr ell E
      (Padic.coefficientExtensionAbsoluteValue ell E)
      (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
        Set (Padic.coefficientExtensionIntegers ell E)) =
        Padic.coefficientExtensionMaximalIdeal ell E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hval : Padic.coefficientExtensionAbsoluteValue ell E (ell : E) < 1 := by
      have hext := spectralNorm_extends (K := Padic ell) (L := E) (ell : Padic ell)
      change spectralNorm (Padic ell) E (ell : E) < 1
      simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := ell))
    have hl : (ell : Padic.coefficientExtensionIntegers ell E) ∈
        Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
          Set (Padic.coefficientExtensionIntegers ell E)) := by
      rw [hgen]
      exact (h.2.1 _).mpr hval
    have hp := Ideal.pow_mem_pow hl n
    have hz : (ell ^ n : A) = 0 := by
      simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hp
    intro a
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hO⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ))))

/--
The literal unit is an object of the bounded constructible finite-Tor category in the fixed
purity setting.  This named proposition is the only postponed input used to form the restricted
exceptional inverse image on the unit.

Proof (postponed): the unit is the pulled-back coefficient `Λ_B = p_B^* Λ`, a constant local
model on the one-stratum stratification of `B`, hence bounded constructible
(det-def-sfb-constructible-tor-amplitude); it is flat over itself, so its Tor amplitude is `[0,0]`.

Source: the unit clause of `def-pur-section-invariant.md` in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/, together with the Dctf
convention of literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-n-change/sk-prop-qlbar-two-colimit/`det-def-sf-operations.md`
(blueprint: def-pur-section-invariant).
-/
theorem sectionInvariantUnit_mem
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] :
    (constantModelBoundedConstructible Λ B.left ⊓
      DerivedCategory.finiteTorAmplitude _) (sectionInvariantUnit Λ B.left) := by
  let : IsLocallyNoetherian B.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.hom
  let : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have := (constantModelConstructibleFiniteTor_wellDefined Λ B.left).2.1
  exact (constantModelBoundedConstructible Λ B.left ⊓
    DerivedCategory.finiteTorAmplitude _).prop_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _) (constantCoefficientObject_mem Λ B.left)

/--
The section invariant is `Ls^* Rg^! Lambda_B`, with `Rg^!` the recorded ctf Brown adjoint: apply
`ctfExceptionalInverseImage` to the literal unit and then apply the total derived module pullback
along the closed section.  The four coefficient alternatives and the finite-field datum are the
fixed conventions, and the section equation is retained.

Source: the displayed definition in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).
-/
noncomputable def sectionInvariant
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
  let hΛ := sectionInvariant_admissible D ell hell E n hn Λ hcoeff
  let unit : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨sectionInvariantUnit Λ B.left,
      sectionInvariantUnit_mem D ell hell E n hn Λ hcoeff B⟩
  (moduleObjectDerivedPullback Λ s.left).obj
    ((ctfExceptionalInverseImage Λ ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g hΛ).obj unit).obj

/--
The section invariant belongs to `D^b_ctf` and has a two-sided relative derived-tensor inverse.
The proof is postponed; the statement follows the four blueprint steps:

1. Define `omega_g = Rg^! Lambda_B` using the recorded ctf exceptional inverse image and the
   literal unit; the coefficient convention supplies its Dctf representative.
2. Partition the smooth morphism by its finite clopen relative-dimension loci.  Compact-support
   composition and the exact open-and-closed adjunction identify each exceptional restriction with
   the constant-dimension exceptional inverse image, whose two-sided Dctf inverse is supplied
   by clause 2 of the theorem thm-pur-cohomological-smoothness (not the finite-coefficient
   definition `def-pur-co-smoothness`).
3. Assemble the finitely many component inverses by the exact product decomposition for a finite
   clopen partition; tensor and unit comparisons assemble componentwise and give a two-sided
   inverse in the source Dctf category.
4. Apply the finite-field ctf pullback stability to the closed section and compose its monoidal
   pullback comparison with both evaluation maps.  This yields the two displayed tensor
   isomorphisms to the literal unit.

Source: the definition and invertibility assertion in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).
-/
theorem sectionInvariant_mem_and_tensor_inverse
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
    (constantModelBoundedConstructible Λ B.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      (sectionInvariant D ell hell E n hn Λ hcoeff B V g s hs) ∧
      ∃ P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
          (condensedRingObj Λ B.left)),
        (constantModelBoundedConstructible Λ B.left ⊓
            DerivedCategory.finiteTorAmplitude _) P ∧
        Nonempty (((derivedTensor Λ B.left).obj
          (sectionInvariant D ell hell E n hn Λ hcoeff B V g s hs)).obj P ≅ 𝟙_ _) ∧
        Nonempty (((derivedTensor Λ B.left).obj P).obj
          (sectionInvariant D ell hell E n hn Λ hcoeff B V g s hs) ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

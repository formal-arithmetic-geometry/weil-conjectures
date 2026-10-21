/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.ZetaSeries

import Sheaf.AlgebraicGeometry.StrictLocalRationalChart
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.SixFunctors.ProEtale.GenericPoint
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Coefficient field over a generic polynomial chart

Source: Stacks Project, Tags 0F0U and 0F0X, coefficient-field construction
(blueprint: lem-kun-strict-local-coefficient-chart).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra
private theorem lift_separable_field_embedding
    (F L B : Type u) [Field F] [Field L] [CommRing B] [HenselianLocalRing B]
    [Algebra F L] [Algebra F B] [Algebra.IsSeparable F L]
    (τ : L →+* (IsLocalRing.maximalIdeal B).ResidueField)
    (hτF : τ.comp (algebraMap F L) = algebraMap F (IsLocalRing.maximalIdeal B).ResidueField) :
    Nonempty (L →ₐ[F] B) := by
  classical
  let m := IsLocalRing.maximalIdeal B
  let p : Ideal F := ⊥
  let q : Ideal L := ⊥
  let eL : L ≃+* q.ResidueField := RingEquiv.ofBijective (algebraMap L q.ResidueField)
    ⟨(algebraMap L q.ResidueField).injective, q.algebraMap_residueField_surjective⟩
  let τ' : q.ResidueField →+* m.ResidueField := τ.comp eL.symm.toRingHom
  have hp : p = q.comap (algebraMap F L) := by
    ext x
    change x = 0 ↔ algebraMap F L x = 0
    simp
  have hm : p = m.comap (algebraMap F B) := by
    ext x
    change x = 0 ↔ algebraMap F B x ∈ m
    rw [← Ideal.algebraMap_residueField_eq_zero]
    rw [← IsScalarTower.algebraMap_apply F B m.ResidueField, map_eq_zero]
  have hτ : τ'.comp (Ideal.ResidueField.map p q (algebraMap F L) hp) =
      Ideal.ResidueField.map p m (algebraMap F B) hm := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    change τ (eL.symm (eL (algebraMap F L x))) =
      algebraMap B m.ResidueField (algebraMap F B x)
    rw [eL.symm_apply_apply, ← IsScalarTower.algebraMap_apply F B m.ResidueField]
    exact DFunLike.congr_fun hτF x
  let : IndEtale F L := IndEtale.of_isSeparable F L
  obtain ⟨I, hI, hFilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := F) (S := L)
  let := hI
  let := hFilt
  let := P.hasColimit
  obtain ⟨j, hj, -⟩ := map_into_henselian_colimit F B L I P.diag
    ⟨(colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit⟩ hP q p hp hm τ' hτ
  exact ⟨j⟩

private theorem coefficient_field_of_rational_chart
    (K R B : Type u) [Field K] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra K R] [IsStrictlyHenselianLocalRing B]
    [Algebra (FractionRing R) B] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
      Algebra.trdeg K L = Algebra.trdeg K (FractionRing R) ∧
      ∃ (_ : Algebra R L) (_ : Algebra (FractionRing R) L)
        (_ : IsScalarTower R (FractionRing R) L)
        (_ : Algebra.IsAlgebraic (FractionRing R) L)
        (h : L →+* B),
        h.comp (algebraMap R L) =
          (algebraMap (FractionRing R) B).comp (algebraMap R (FractionRing R)) ∧
        h.comp (algebraMap K L) =
          (algebraMap (FractionRing R) B).comp (algebraMap K (FractionRing R)) := by
  classical
  let F := FractionRing R
  let m := IsLocalRing.maximalIdeal B
  let e : IsLocalRing.ResidueField B ≃+* m.ResidueField :=
    RingEquiv.ofBijective (algebraMap (B ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  let : IsSepClosed m.ResidueField := IsSepClosed.of_ringEquiv e
  let L := separableClosure F m.ResidueField
  let : IsSepClosed L := IsSepClosure.sep_closed F
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hτ : (IntermediateField.val L).toRingHom.comp (algebraMap F L) =
      algebraMap F m.ResidueField := by ext; rfl
  obtain ⟨j⟩ := lift_separable_field_embedding F L B
    (IntermediateField.val L).toRingHom hτ
  have hdeg : Algebra.trdeg K L = Algebra.trdeg K F := by
    have ht := trdeg_add_eq K F (A := L)
    simpa only [trdeg_eq_zero, add_zero] using ht.symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, hdeg,
    inferInstance, inferInstance, inferInstance, inferInstance, j.toRingHom, ?_, ?_⟩
  · ext x
    change j (algebraMap F L (algebraMap R F x)) = _
    exact j.commutes _
  · ext x
    change j (algebraMap F L (algebraMap K F x)) = _
    exact j.commutes _
end Algebra

namespace AlgebraicGeometry.Scheme

/-- Choose a generic polynomial chart and embed its separable coefficient field in the
strict localization, compatibly with both scalar maps.

Source: Stacks Project, Tag 0F0U, proof before the compatible-model footnote, and Tag 0F0X,
second paragraph (blueprint: lem-kun-strict-local-coefficient-chart).

Proof: the rational-chart theorem lifts a finite transcendence basis and constructs
its rational function field F inside the strict-local ring B, compatibly with R and K.
The maximal-ideal residue field of the strictly henselian ring B is separably closed.
Let L be the relative separable closure of F in that field. It is separably closed and
algebraic over F. As a separable field extension, L is ind-etale over F. The henselian
lifting theorem applied to its residue embedding lifts it to an F-algebra map into B.
Its F-linearity gives both scalar equations. The transcendence-degree tower formula
and algebraicity of L/F give the claimed equality. No choice of a coefficient field
enters any definition: all these witnesses are eliminated in the proof.
-/
theorem exists_strictLocal_coefficient_chart
    {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧
      ∃ hU : IsAffineOpen U,
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
        Algebra.trdeg K L =
          @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
            (((Y ↘ Spec (.of K)).residueFieldAlgebraMap
              (s (IsLocalRing.closedPoint Ω))).toAlgebra) ∧
        ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
          (_ : Algebra R L) (_ : Algebra (FractionRing R) L)
          (_ : IsScalarTower R (FractionRing R) L)
          (_ : Algebra.IsAlgebraic (FractionRing R) L)
          (r : CommRingCat.of R ⟶ Γ(U.toScheme, ⊤))
          (a : Γ(U.toScheme, ⊤) ⟶ strictHenselizationRing s)
          (h : L →+* strictHenselizationRing s),
          Nontrivial (strictHenselizationRing s) ∧
          Spec.map a ≫ (@Scheme.isoSpec U.toScheme hU).inv ≫ U.ι =
            strictHenselizationStructuralMap s ∧
          r ≫ a = CommRingCat.ofHom (algebraMap R L) ≫ CommRingCat.ofHom h ∧
          (ΓSpecIso (.of K)).inv ≫ (U.ι ≫ (Y ↘ Spec (.of K))).appTop ≫ a =
            CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom h := by
  classical
  obtain ⟨U, hy, hU, R, hR, hdR, hKR, r, a, hFB, hB, ha, hr, hk, hd⟩ :=
    exists_strictLocal_rational_chart (K := K) Y s
  let := hU
  let := hR
  let := hdR
  let := hKR
  let := hFB
  let := hB
  obtain ⟨hl, hs⟩ := AlgebraicGeometry.strictHenselizationLocalStructure s
  let := hl
  let := hs
  obtain ⟨L, hL, hKL, hsep, hdeg, hRL, hFL, ht, halg, h, hRmap, hKmap⟩ :=
    Algebra.coefficient_field_of_rational_chart K R (strictHenselizationRing s)
  let := hL
  let := hKL
  let := hsep
  let := hRL
  let := hFL
  let := ht
  let := halg
  refine ⟨U, hy, hU, L, hL, hKL, hsep, hdeg.trans hd,
    R, hR, hdR, hRL, hFL, ht, halg, r, a, h, hB, ha, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    exact hr.trans hRmap.symm
  · apply CommRingCat.hom_ext
    exact hk.trans hKmap.symm

end AlgebraicGeometry.Scheme

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Curve

import Sheaf.AlgebraicGeometry.Curve.FrobeniusSeparableFactorization
import Sheaf.AlgebraicGeometry.CurveRiemannHurwitzNumerical
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-! # Genus comparison for nonconstant maps of smooth proper curves

Source: Stacks Project, Algebraic Curves, Tags 0C1B, 0CD2 and 0CD0
(blueprint: lem-sfb-finite-curve-genus-monotonicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Genus invariance under field extension, from coherent base change and genus comparison. -/
private theorem genus_pullback_field
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 s] [IsProper s] :
    (Limits.pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap k K)))).genus = s.genus := by
  let : X.Over (Spec (.of k)) := ⟨s⟩
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 s)
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper s)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : (Limits.pullback s b).Over (Spec (.of K)) := ⟨Limits.pullback.snd s b⟩
  have : SmoothOfRelativeDimension 1 (Limits.pullback s b ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback s b) inferInstance
  have : IsProper (Limits.pullback s b ↘ Spec (.of K)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd s b))
  change (Limits.pullback s b ↘ Spec (.of K)).genus = (X ↘ Spec (.of k)).genus
  rw [Scheme.genus_eq_arithmeticGenus, Scheme.genus_eq_arithmeticGenus]
  exact Scheme.arithmeticGenus_pullback (k := k) (X := X) K

/-- A nonconstant morphism between smooth proper geometrically integral curves over an
algebraically closed field cannot increase genus from source to target. Genus is the
cohomological genus `Scheme.arithmeticGenus`, namely `dim H¹(O)`, not a separability invariant.
Nonconstancy means precisely that the morphism does not factor through a rational point.

Source: Stacks Project, Algebraic Curves, Tags 0C1B (Riemann--Hurwitz), 0CD2 (Frobenius
factorization), and 0CD0 (genus of a purely inseparable smooth cover).
(blueprint: lem-sfb-finite-curve-genus-monotonicity)

Proof:
1. If the target genus is zero, nonnegativity of the source genus proves the claim
   (def-sc-genus). Otherwise the target genus is at least one.
2. Apply lem-sfb-curve-frobenius-separable-factorization to obtain a relative Frobenius
   followed by a nonconstant separable map from a smooth proper geometrically integral
   curve C'. In characteristic zero take the identity as the Frobenius factor.
3. The genus of C' equals that of C: apply lem-sc-flat-base-change-coherent in degree one
   to the Frobenius field self-embedding (def-pc-field-extension). Retain the second
   projection as the structure map on the Frobenius twist; in characteristic zero use
   the identity case. The embedding is injective since the ground ring is a field.
4. Apply lem-sfb-curve-riemann-hurwitz-numerical to the separable factor. It gives
   2g(C')-2 = d(2g(D)-2)+r with d at least one and r nonnegative, including wild ramification.
5. Since 2g(D)-2 is nonnegative, the right side is at least 2g(D)-2. Cancel and divide by
   two to obtain g(D) at most g(C'). Substitute the equality from step 3.
-/
theorem genus_le_of_nonconstant_smooth_proper_curve
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (C D : Scheme.{u}) [C.Over (Spec (.of Ω))] [D.Over (Spec (.of Ω))]
    [Smooth (C ↘ Spec (.of Ω))] [Smooth (D ↘ Spec (.of Ω))]
    [IsProper (C ↘ Spec (.of Ω))] [IsProper (D ↘ Spec (.of Ω))]
    [GeometricallyIntegral (C ↘ Spec (.of Ω))]
    [GeometricallyIntegral (D ↘ Spec (.of Ω))]
    (hC : C.IsPureDimension 1) (hD : D.IsPureDimension 1)
    (f : C ⟶ D) (hf : f ≫ (D ↘ Spec (.of Ω)) = C ↘ Spec (.of Ω))
    (hnonconstant : ¬ ∃ p : Spec (.of Ω) ⟶ D,
      p ≫ (D ↘ Spec (.of Ω)) = 𝟙 (Spec (.of Ω)) ∧ (C ↘ Spec (.of Ω)) ≫ p = f) :
    Scheme.arithmeticGenus Ω D ≤ Scheme.arithmeticGenus Ω C := by
  classical
  have : IsIntegral C :=
    GeometricallyIntegral.isIntegral_of_subsingleton (C ↘ Spec (.of Ω))
  have : IsIntegral D :=
    GeometricallyIntegral.isIntegral_of_subsingleton (D ↘ Spec (.of Ω))
  have dimC : topologicalKrullDim C = 1 := by
    have h := hC Set.univ (by simp [irreducibleComponents_eq_singleton])
    exact ((Homeomorph.Set.univ C).isHomeomorph.topologicalKrullDim_eq _).symm.trans h
  have dimD : topologicalKrullDim D = 1 := by
    have h := hD Set.univ (by simp [irreducibleComponents_eq_singleton])
    exact ((Homeomorph.Set.univ D).isHomeomorph.topologicalKrullDim_eq _).symm.trans h
  have : IsCurve (C ↘ Spec (.of Ω)) := ⟨dimC.le⟩
  have : IsCurve (D ↘ Spec (.of Ω)) := ⟨dimD.le⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of Ω)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ 1).mpr dimC
  have : SmoothOfRelativeDimension 1 (D ↘ Spec (.of Ω)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ 1).mpr dimD
  rw [← Scheme.genus_eq_arithmeticGenus, ← Scheme.genus_eq_arithmeticGenus]
  by_cases hzero : (D ↘ Spec (.of Ω)).genus = 0
  · rw [hzero]
    exact Nat.zero_le _
  obtain ⟨C', s', hInt, F, v, hCurve, hSmooth, hProper, hGeom, hdim,
    _hF, hv, _hcomp, hnon, ⟨i, hi, hfin, hsep⟩, hchar0, hcharp⟩ :=
    exists_curve_frobenius_separable_factorization Ω C D
      (C ↘ Spec (.of Ω)) (D ↘ Spec (.of Ω)) dimC dimD f hf hnonconstant
  let : C'.Over (Spec (.of Ω)) := ⟨s'⟩
  have : IsIntegral C' := hInt
  have : IsCurve (C' ↘ Spec (.of Ω)) := hCurve
  have : Smooth (C' ↘ Spec (.of Ω)) := hSmooth
  have : IsProper (C' ↘ Spec (.of Ω)) := hProper
  have : GeometricallyIntegral (C' ↘ Spec (.of Ω)) := hGeom
  have : SmoothOfRelativeDimension 1 s' :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq s' 1).mpr hdim
  have hgenus : s'.genus = (C ↘ Spec (.of Ω)).genus := by
    rcases CharP.exists' Ω with hzero | ⟨p, hp, hchar⟩
    · obtain ⟨e, hs, -, -⟩ := hchar0 hzero
      subst C'
      cases hs
      rfl
    · obtain ⟨n, _hCchar, e, hs, -⟩ := hcharp p hp.out (CharP.cast_eq_zero Ω p)
      subst C'
      simp only [eqToHom_refl, Category.id_comp] at hs
      rw [hs]
      let : Algebra Ω Ω := (iterateFrobeniusOfPrime Ω hp.out
        (CharP.cast_eq_zero Ω p) n).toAlgebra
      exact genus_pullback_field (K := Ω) (C ↘ Spec (.of Ω))
  let : Algebra D.functionField C'.functionField := i.toAlgebra
  have : Module.Finite D.functionField C'.functionField := hfin
  have : Algebra.IsSeparable D.functionField C'.functionField := hsep
  obtain ⟨hd, r, hr, heq⟩ := curve_riemannHurwitz_numerical Ω C' D hdim dimD v hv hnon hi
  change 2 * (s'.genus : ℤ) - 2 = _ at heq
  have hpos : (1 : ℤ) ≤ (Module.finrank D.functionField C'.functionField : ℤ) := by
    exact_mod_cast hd
  have htarget : 0 ≤ 2 * ((D ↘ Spec (.of Ω)).genus : ℤ) - 2 := by omega
  have hmul := mul_le_mul_of_nonneg_right hpos htarget
  rw [hgenus] at heq
  omega

end AlgebraicGeometry

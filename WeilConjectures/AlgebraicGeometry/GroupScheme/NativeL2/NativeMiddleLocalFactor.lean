/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeConstructibleFibreFinite
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-! # Determinant factors of the actual middle-image operator

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
paragraphs 5--6: the factor 1-alpha*T^d for each boundary eigenvalue.
(blueprint: lem-wf-native-middle-local-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)

omit [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
  [IsOpenImmersion j₀.left] [IsDominant j₀.left] in
/-- A closed residue field has positive degree and cardinality q to that degree. -/
theorem closedPoint_cardinality :
    0 < localClosedPointDegree D X₀ x ∧
      Nat.card (X₀.left.residueField x.val) = D.q ^ localClosedPointDegree D X₀ x := by
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x.val).2.1.mp x.prop
  have : Finite (X₀.left.residueField x.val) := Module.finite_of_finite D.k₀
  refine ⟨Module.finrank_pos, ?_⟩
  simpa only [localClosedPointDegree, D.card_base] using
    (Module.natCard_eq_pow_finrank (K := D.k₀) (V := X₀.left.residueField x.val))

include hl hM in
private theorem middleCarrier_constructible :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (middleWeilImage D l j₀ M).carrier := by
  unfold middleWeilImage
  exact middleImage_constructible D l j₀ hl M.carrier hM

include hl hM in
/-- Constructibility of ordinary direct image gives finite dimensionality of its actual fibre.
Source: latest blueprint, ordinary middle-image constructibility and boundary factors
(blueprint: lem-wf-native-middle-local-factor). -/
theorem middleClosedFiber_finiteDimensional :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D (middleWeilImage D l j₀ M).carrier (localClosedPoint D X₀ x i hi)) := by
  have : IsNoetherian (D.geometricFiber X₀).left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (CategoryTheory.Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      toCompactSpace := by
        change CompactSpace (CategoryTheory.Limits.pullback X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme)
        infer_instance }
  exact constructible_fibre_finiteDimensional D l _
    (middleCarrier_constructible D l hl j₀ M hM) (localClosedPoint D X₀ x i hi)

/-- The canonical reverse characteristic polynomial, embedded in C and with T replaced by T^d.
Source: latest blueprint, sk-p-real-semi.proof.md, boundary polynomial
(blueprint: lem-wf-native-middle-local-factor). -/
def middleLocalFactor (ι : PadicAlgCl l →+* ℂ) : Polynomial ℂ :=
  letI := middleClosedFiber_finiteDimensional D l hl j₀ M hM x i hi
  ((closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom.charpolyRev.map
    (ι.comp ULift.ringEquiv.toRingHom)).comp
      (Polynomial.X ^ localClosedPointDegree D X₀ x)

omit [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
  [IsOpenImmersion j₀.left] [IsDominant j₀.left] in
/-- The actual local operator is an isomorphism, so none of its eigenvalues is zero.
Source: latest blueprint, local Frobenius and its determinant factors
(blueprint: lem-wf-native-middle-local-factor). -/
theorem eigenvalue_ne_zero (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom α) : α ≠ 0 := by
  let F := closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi
  obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
  intro h
  have hz : F.hom v = 0 := by simpa [h] using (Module.End.mem_eigenspace_iff.mp hv)
  apply hv0
  have hF : IsIso F := by
    dsimp [F]
    unfold closedOperator operator
    infer_instance
  apply (asIso F).toLinearEquiv.injective
  simpa using hz

/-- Factor the split characteristic polynomial, reverse its factors, map coefficients,
and substitute T^d. Each eigenvalue supplies the stated divisor of the local factor.
Source: latest blueprint, sk-p-real-semi.proof.md, paragraph 6
(blueprint: lem-wf-native-middle-local-factor). -/
theorem middleLocalFactor_factor (ι : PadicAlgCl l →+* ℂ)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom α) :
    1 - Polynomial.C (ι α.down) * Polynomial.X ^ localClosedPointDegree D X₀ x ∣
      middleLocalFactor D l hl j₀ M hM x i hi ι := by
  let := middleClosedFiber_finiteDimensional D l hl j₀ M hM x i hi
  let : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    ⟨fun P ↦ Polynomial.Splits.of_splits_map ULift.ringEquiv.toRingHom
      (IsAlgClosed.splits _) (fun a _ ↦ ⟨ULift.up a, rfl⟩)⟩
  let F := (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom
  have hroot : α ∈ F.charpoly.roots := by
    exact (Polynomial.mem_roots F.charpoly_monic.ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly F α).mp hα)
  have hdvd : 1 - Polynomial.C α * Polynomial.X ∣ F.charpolyRev := by
    rw [LinearMap.charpolyRev_eq_prod_roots]
    exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨α, hroot, rfl⟩)
  have hmap := Polynomial.map_dvd (ι.comp ULift.ringEquiv.toRingHom) hdvd
  obtain ⟨R, hR⟩ := hmap
  refine ⟨R.comp (Polynomial.X ^ localClosedPointDegree D X₀ x), ?_⟩
  simpa [middleLocalFactor, F, ULift.ringEquiv] using
    congrArg (fun P : Polynomial ℂ ↦ P.comp (Polynomial.X ^ localClosedPointDegree D X₀ x)) hR

end WeilConjectures.NativeL2

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.Equiv
/-! # Scalar traces through the canonical constant-section presentation
Source: current Euler-product proof Steps 0 and 3, ordinary matrix traces over Lambda.
(blueprint: lem-condensed-weil-euler-scalar-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory
namespace WeilConjectures.CondensedWeilEuler
private theorem trace_scalarEquiv {R : Type u} {S : Type v} [Field R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{w} S) [Module.Free S M] [Module.Finite S M]
    (f : End M) :
    e (LinearMap.trace R ((ModuleCat.restrictScalars e.toRingHom).obj M)
      ((ModuleCat.restrictScalars e.toRingHom).map f).hom) = LinearMap.trace S M f.hom := by
  classical
  let : Module R M := Module.compHom M e.toRingHom
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let b := Module.Free.chooseBasis S M
  let b' : Module.Basis (Module.Free.ChooseBasisIndex S M) R N :=
    b.mapCoeffs e.symm (fun c x ↦ by change e (e.symm c) • x = c • x; rw [e.apply_symm_apply])
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex S M)
  rw [LinearMap.trace_eq_matrix_trace R b', LinearMap.trace_eq_matrix_trace S b]
  rw [Matrix.trace, Matrix.trace, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h (x : M) : e (b'.repr x i) = b.repr x i := by
    change e (e.symm ((b.repr x) i)) = (b.repr x) i
    exact e.apply_symm_apply _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change e (b'.repr (f.hom (b' i)) i) = (b.repr (f.hom (b i))) i
  rw [show b' i = b i from Module.Basis.mapCoeffs_apply b e.symm _ i]
  exact h (f.hom (b i))
private theorem constants_injective (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] : Function.Injective (Profinite.continuousMapConstRingHom.{u} T) := by
  intro x y h
  have hs := congrArg (fun z : MonObj.Γ (Profinite.continuousMapRingObj.{u} T) =>
    Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map z.hom) h
  dsimp only [Profinite.continuousMapConstRingHom] at hs
  simp only [Sheaf.ε_comp_ringHomΓSheafCompose_hom
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheaf T)
    (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl)] at hs
  have hh := congrArg (fun f =>
    f.app (Opposite.op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) hs
  change ((1 : ℤ) : ULift.{u + 1} C(PUnit.{u + 1}, T)) *
    ULift.up (ContinuousMap.const PUnit.{u + 1} x) =
      ((1 : ℤ) : ULift.{u + 1} C(PUnit.{u + 1}, T)) *
        ULift.up (ContinuousMap.const PUnit.{u + 1} y) at hh
  simp only [Int.cast_one, one_mul] at hh
  exact congrArg (fun f => f.down PUnit.unit) hh

/-- Constant coefficients identify the coefficient field with its global sections.
Source: the scalar convention in the Euler-product statement.
Proof: for a finite coefficient field evaluate constant sections at the terminal point
for injectivity, and use the constant-section surjectivity theorem. For Qbar the
regular module has distinct zero and identity maps, so its scalar ring is nontrivial;
the field homomorphism is injective and the published theorem makes it surjective.
(blueprint: lem-condensed-weil-euler-scalar-trace). -/
theorem scalarMap_bijective {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    Function.Bijective (scalarMap.{u} c) := by
  cases c with
  | finite E => exact ⟨constants_injective E,
      Profinite.continuousMapConstRingHom_surjective E⟩
  | qbar =>
    have hne : (1 : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell)) ≠ 0 := by
      intro h
      apply Profinite.PadicAlgCl.one_ne_zero_end_regular ell
      exact (map_one Mod.regularEndRingHom).symm.trans
        ((congrArg Mod.regularEndRingHom h).trans (map_zero Mod.regularEndRingHom))
    let : Nontrivial (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell)) :=
      nontrivial_of_ne 1 0 hne
    exact ⟨(Profinite.PadicAlgCl.constRingHom ell).injective,
      Profinite.PadicAlgCl.constRingHom_surjective ell⟩

/-- Finite generation is invariant under the scalar presentation.
Source: Euler-product proof Step 1, finite-dimensional scalar stalks.
Proof: the identity on the underlying group is a bijective semilinear map for the
surjective constant-section homomorphism. Finite generation is invariant under such
a map in both directions.
(blueprint: lem-condensed-weil-euler-scalar-trace). -/
theorem scalarFinite_iff {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell)
    (M : ModuleCat.{u + 1} (MonObj.Γ (WeilCoefficient.ab c))) :
    Module.Finite (Scalar c) ((ModuleCat.restrictScalars (scalarMap c)).obj M) ↔
      Module.Finite (MonObj.Γ (WeilCoefficient.ab c)) M := by
  let : RingHomSurjective (scalarMap c) := ⟨(scalarMap_bijective c).2⟩
  let f : ((ModuleCat.restrictScalars (scalarMap c)).obj M) →ₛₗ[scalarMap c] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact f.finite_iff_of_bijective Function.bijective_id

/-- The ordinary trace is unchanged under the constant-section ring identification.
Source: Euler-product proof Step 3, traces over the specified coefficient field.
Proof: choose a finite basis over the global-section ring. Transport its coordinates
through the inverse ring isomorphism. The two operator matrices have corresponding
entries, and the ring map preserves their finite diagonal sums. This includes the
zero-dimensional case.
(blueprint: lem-condensed-weil-euler-scalar-trace). -/
theorem scalarTrace_restrict {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell)
    (M : ModuleCat.{u + 1} (MonObj.Γ (WeilCoefficient.ab c)))
    [Module.Finite (MonObj.Γ (WeilCoefficient.ab c)) M] (f : End M) :
    scalarMap c (LinearMap.trace (Scalar c) ((ModuleCat.restrictScalars (scalarMap c)).obj M)
      ((ModuleCat.restrictScalars (scalarMap c)).map f).hom) =
        LinearMap.trace (MonObj.Γ (WeilCoefficient.ab c)) M f.hom := by
  let e := RingEquiv.ofBijective (scalarMap c) (scalarMap_bijective c)
  let : Field (MonObj.Γ (WeilCoefficient.ab c)) :=
    (e.symm.toMulEquiv.isField (Field.toIsField (Scalar c))).toField
  exact trace_scalarEquiv e M f
/-- Scalar identification preserves the traces of all powers.
Source: Euler-product proof Step 3, the traces of Frobenius iterates.
Proof: apply scalar trace compatibility to the powered endomorphism; functors and the
endomorphism-to-linear-map ring isomorphism both preserve powers.
(blueprint: lem-condensed-weil-euler-scalar-trace). -/
theorem scalarTrace_restrict_pow {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell)
    (M : ModuleCat.{u + 1} (MonObj.Γ (WeilCoefficient.ab c)))
    [Module.Finite (MonObj.Γ (WeilCoefficient.ab c)) M] (f : End M) (n : ℕ) :
    scalarMap c (LinearMap.trace (Scalar c) ((ModuleCat.restrictScalars (scalarMap c)).obj M)
      (((ModuleCat.restrictScalars (scalarMap c)).map f).hom ^ n)) =
        LinearMap.trace (MonObj.Γ (WeilCoefficient.ab c)) M (f.hom ^ n) := by
  have h := scalarTrace_restrict c M (f ^ n)
  let N := (ModuleCat.restrictScalars (scalarMap c)).obj M
  let g : End N := End.of ((ModuleCat.restrictScalars (scalarMap c)).map f)
  have hmap := map_pow (Functor.mapEnd M (ModuleCat.restrictScalars (scalarMap c))) f n
  have hp : ((ModuleCat.restrictScalars (scalarMap c)).map (f ^ n)).hom = g.hom ^ n := by
    change (ModuleCat.endRingEquiv N)
      ((Functor.mapEnd M (ModuleCat.restrictScalars (scalarMap c))) (f ^ n)) = _
    rw [hmap]
    exact map_pow (ModuleCat.endRingEquiv N).toMonoidHom g n
  rw [hp, show (f ^ n).hom = f.hom ^ n from
    map_pow (ModuleCat.endRingEquiv M).toMonoidHom f n] at h
  exact h

end WeilConjectures.CondensedWeilEuler

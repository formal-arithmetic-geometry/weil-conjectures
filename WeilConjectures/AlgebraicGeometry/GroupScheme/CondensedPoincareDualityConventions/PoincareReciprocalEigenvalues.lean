/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDegreewiseField
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualTateDatum
import WeilConjectures.ZetaLinearAlgebra.Pairing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.Z8.Z8GeometricFieldPoint
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! # Reciprocal eigenvalues of geometric Frobenius

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-frobenius/sec-purity-duality-and-frobenius/sk-thm-frobenius/
cor-pod-reciprocal-eigenvalues.md and its proof
(blueprint: cor-pod-reciprocal-eigenvalues).

The operators below use the same point insertion and the same direct/open exchange
maps as the recorded global Frobenius, in the exact terminal-evaluation coordinates
used by the degreewise pairing. The adjoint is that of the specified Poincare pairing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedPoincareDualityConventions

variable (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)

/- The section-ring reconstruction preserves the original ring-sheaf multiplication.
This is the same explicit construction used in the Z8 point calculation. -/
private def scalarSectionCoordinates
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] :
    condensedScalarRing ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) ≃+*
      R.obj.obj (Opposite.op (⊤_ Profinite.{u})) := by
  let T := coherentTopology Profinite.{u}
  let A := (sheafCompose T (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hm : (sheafToPresheaf T Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  refine { toEquiv := Equiv.refl _
           map_add' := fun _ _ ↦ rfl
           map_mul' := ?_ }
  intro a b
  change (((sheafToPresheaf T Ab.{u + 1}).monObjObj A).mul.app
      (Opposite.op (⊤_ Profinite.{u}))).hom (a ⊗ₜ[ℤ] b) =
    (show R.obj.obj (Opposite.op (⊤_ Profinite.{u})) from a) *
      (show R.obj.obj (Opposite.op (⊤_ Profinite.{u})) from b)
  have h := congrArg (fun m : MonObj A.obj ↦ m.mul) hm
  rw [h]
  rfl

/-- Exact terminal evaluation, in the scalar coordinates of the degreewise pairing.
Source: the ordinary/compact section convention (blueprint: cor-pod-reciprocal-eigenvalues). -/
abbrev pairingSections :=
  (CohomologyTransport.sections ((P.presentation c).obj P.ell) P.s).mapDerivedCategory

/-- The canonical point insertion: restriction along geometric field Frobenius,
using the specified exact inverse-image comparison and the point-equivalence unit.
Source: Frobenius convention and proof step 2 (blueprint: cor-pod-reciprocal-eigenvalues). -/
def pairingInsertion : P.pairingSections c ≅
    moduleObjectDerivedPullback ((P.presentation c).obj P.ell)
      (CondensedFrobeniusTransport.pointFrobenius P.datum).hom ⋙ P.pairingSections c :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory ((P.presentation c).obj P.ell)
        (CondensedFrobeniusTransport.pointFrobenius P.datum).hom ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarIsoIdOfIsSepClosed ((P.presentation c).obj P.ell)
          (CondensedFrobeniusTransport.pointFrobenius P.datum).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- Postcomposition by a shifted scalar endomorphism is its action on cohomology.
Source: the induced F-operators (blueprint: cor-pod-reciprocal-eigenvalues). -/
def pairingCohomologyAction (C : DerivedCategory
    (ModuleCat.{u + 1} (P.pairingScalar c))) (F : End C) (i : ℤ) :
    Module.End (P.pairingScalar c) (𝟙_ _ ⟶ C ⟦i⟧) where
  toFun x := x ≫ (shiftFunctor _ i).map F
  map_add' x y := by simp
  map_smul' a x := by simp

/-- Compact Frobenius on H_c^i(X,K) of the given strict Weil pair.
Source: proof step 2, A=F_c,K (blueprint: cor-pod-reciprocal-eigenvalues). -/
def reciprocalCompactOperator (K : P.strictWeil c) (i : ℤ) :
    Module.End (P.pairingScalar c) (P.pairingHc c K.carrier.obj i) :=
  P.pairingCohomologyAction c _
    (P.pairingFrobenius c K.carrier.obj ((ObjectProperty.ι _).mapIso K.str)).2 i

/-- Ordinary Frobenius on H^(2d-i)(X,K^vee) with the recorded contragredient datum.
Source: proof step 2, B=F_K^vee (blueprint: cor-pod-reciprocal-eigenvalues). -/
def reciprocalDualOperator (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) : Module.End (P.pairingScalar c)
      (P.pairingH c (P.coefficientDual c K.carrier) (2 * (P.dimension : ℤ) - i)) :=
  P.pairingCohomologyAction c _
    (P.pairingFrobenius c (P.coefficientDual c K.carrier)
      (P.perfectDualDatum c K hK)).1 (2 * (P.dimension : ℤ) - i)

/-- The adjoint is the one determined by the actual line-valued Poincare form.
Source: proof step 1 (blueprint: cor-pod-reciprocal-eigenvalues). -/
def reciprocalAdjoint (hc : c = .rational ∨ c = .qbar) (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) (t : P.pairingLinv c ≃ₗ[P.pairingScalar c] P.pairingScalar c) :
    P.pairingH c (P.coefficientDual c K.carrier) (2 * (P.dimension : ℤ) - i) ≃ₗ[
      P.pairingScalar c] Module.Dual (P.pairingScalar c) (P.pairingHc c K.carrier.obj i) := by
  let b := (P.fieldPairingData c K.carrier hK i).untwisted.compr₂ t.toLinearMap
  letI : b.IsPerfPair := (P.degreewiseFieldPerfect c hc K.carrier hK i).2.2.2.2.2.2.2.2 t
  exact b.flip.toPerfPair

/-- The compact characteristic polynomial in the finite free coordinates supplied
by degreewise duality. Source: characteristic roots
(blueprint: cor-pod-reciprocal-eigenvalues). -/
def reciprocalCompactCharpoly (hc : c = .rational ∨ c = .qbar) (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) : Polynomial (P.pairingScalar c) := by
  let hp := P.degreewiseFieldPerfect c hc K.carrier hK i
  letI := hp.1
  letI := hp.2.1
  exact (P.reciprocalCompactOperator c K i).charpoly

/-- The dual characteristic polynomial in the same degreewise-duality coordinates.
Source: characteristic roots (blueprint: cor-pod-reciprocal-eigenvalues). -/
def reciprocalDualCharpoly (hc : c = .rational ∨ c = .qbar) (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) : Polynomial (P.pairingScalar c) := by
  let hp := P.degreewiseFieldPerfect c hc K.carrier hK i
  letI := hp.2.2.1
  letI := hp.2.2.2.1
  exact (P.reciprocalDualOperator c K hK i).charpoly

/-- Conjugacy by the actual perfect-pairing adjoint. Every trivialization of the
negative point Tate line gives the same conjugacy. No invertibility, trace
compatibility or similitude is assumed as additional input.
Source: first display and proof steps 1--2 (blueprint: cor-pod-reciprocal-eigenvalues).
Proof: degreewiseFieldPerfect gives finite spaces and a perfect line-valued form.
Choose a frame t of its rank-one value line, and let b=t composed with that form.
The untwisted Frobenius similitude is b(Ax,By)=q^d b(x,y). The scalar is nonzero
because q>0 and the coefficient field has characteristic zero. Nondegeneracy
makes both A and B injective, and finite-dimensionality makes them bijective.
Substituting A^-1 x into the similitude gives Phi B Phi^-1=q^d(A^-1)^t,
where Phi(y)(x)=b(x,y). Ring.inverse is this genuine inverse on the dual.
Changing t scales Phi by a unit, which cancels in the conjugacy. -/
theorem poincareReciprocalConjugacy (hc : c = .rational ∨ c = .qbar)
    (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) (t : P.pairingLinv c ≃ₗ[P.pairingScalar c] P.pairingScalar c) :
    IsUnit (P.reciprocalCompactOperator c K i) ∧
      (P.reciprocalAdjoint c hc K hK i t).conj (P.reciprocalDualOperator c K hK i) =
        (P.datum.q : P.pairingScalar c) ^ P.dimension •
          Ring.inverse (P.reciprocalCompactOperator c K i).dualMap := by
  sorry

set_option maxHeartbeats 2000000 in
/-- Reciprocal characteristic roots, including every algebraic multiplicity,
computed in any algebraically closed extension of the coefficient field. In
particular the fixed E-in-Qbar inclusion and the identity at Qbar are allowed.
Source: the eigenvalue sentence and proof step 3 (blueprint: cor-pod-reciprocal-eigenvalues).
Proof: trivialize the point line and apply the perfect-similitude spectrum lemma
to the specified operators with scalar q^d. The compact operator is invertible,
so none of its characteristic roots is zero. Mapping alpha to q^d/alpha is an
involution on nonzero roots. The resulting equality of root multisets therefore
identifies the multiplicity of alpha with that of q^d/alpha. For a nonzero monic
characteristic polynomial this multiset count is Polynomial.rootMultiplicity.
This includes repeated eigenvalues, nonsplit E-polynomials and zero-dimensional
cohomology spaces; no diagonalizability assumption is used. -/
theorem poincareReciprocalRoots (hc : c = .rational ∨ c = .qbar)
    (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) (M : Type v) [Field M] [IsAlgClosed M] (ι : P.pairingScalar c →+* M) :
    ((P.reciprocalDualCharpoly c hc K hK i).map ι).roots =
      ((P.reciprocalCompactCharpoly c hc K hK i).map ι).roots.map
      (fun α ↦ ι ((P.datum.q : P.pairingScalar c) ^ P.dimension) / α) ∧
    ∀ α : M, α ≠ 0 →
      Polynomial.rootMultiplicity
          (ι ((P.datum.q : P.pairingScalar c) ^ P.dimension) / α)
          ((P.reciprocalDualCharpoly c hc K hK i).map ι) =
        Polynomial.rootMultiplicity α ((P.reciprocalCompactCharpoly c hc K hK i).map ι) := by
  classical
  have hscalar : IsField (P.pairingScalar c) ∧ CharZero (P.pairingScalar c) := by
    rcases hc with rfl | rfl
    · let := PadicAlgCl.normedFieldOfAlgebra P.ell P.extension
      have hf := (CondensedGeometricPoint.Z8.continuousField_direct_coefficient_point
        P.extension P.datum.k).1
      let : Nonempty (⊤_ Profinite.{u}) :=
        ⟨(terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit⟩
      let e := scalarSectionCoordinates (Profinite.continuousMapRingSheaf.{u} P.extension)
      let f : P.extension →+* ULift.{u + 1} C((⊤_ Profinite.{u}), P.extension) :=
        ULift.ringEquiv.symm.toRingHom.comp ContinuousMap.C
      have hi : Function.Injective f := by
        intro a b h
        exact congrArg (fun z ↦ z.down (Classical.choice inferInstance)) h
      exact ⟨hf, charZero_of_injective_ringHom
        (f := e.symm.toRingHom.comp f) (e.symm.injective.comp hi)⟩
    · have hf := (CondensedGeometricPoint.Z8.padicAlgCl_direct_coefficient_point
        P.ell P.datum.k).1
      let : Nonempty (⊤_ Profinite.{u}) :=
        ⟨(terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit⟩
      let e := scalarSectionCoordinates (Profinite.padicAlgClCondensedRing.{u} P.ell)
      let f := Profinite.PadicAlgCl.constSectionRingHom P.ell
        (Opposite.op (⊤_ Profinite.{u}))
      have hi : Function.Injective f := by
        intro a b h
        exact congrArg (fun z ↦ z.down.val (Classical.choice inferInstance)) h
      exact ⟨hf, charZero_of_injective_ringHom
        (f := e.symm.toRingHom.comp f) (e.symm.injective.comp hi)⟩
  let := hscalar.1.toField
  let := hscalar.2
  let hp := P.degreewiseFieldPerfect c hc K.carrier hK i
  let := hp.1
  let := hp.2.1
  let := hp.2.2.1
  let := hp.2.2.2.1
  obtain ⟨t⟩ := hp.2.2.2.2.2.2.2.1
  let b := (P.fieldPairingData c K.carrier hK i).untwisted.compr₂ t.toLinearMap
  let : b.IsPerfPair := hp.2.2.2.2.2.2.2.2 t
  let F := P.reciprocalCompactOperator c K i
  let G := P.reciprocalDualOperator c K hK i
  let a := (P.datum.q : P.pairingScalar c) ^ P.dimension
  have ha : a ≠ 0 := by
    apply pow_ne_zero
    apply Nat.cast_ne_zero.mpr
    rw [P.datum.cardinality_eq]
    exact pow_ne_zero _ P.datum.prime.ne_zero
  obtain ⟨hF, hconj⟩ := P.poincareReciprocalConjugacy c hc K hK i t
  change IsUnit F at hF
  change b.flip.toPerfPair.conj G = a • Ring.inverse F.dualMap at hconj
  have hFd : IsUnit F.dualMap := by
    apply (LinearMap.isUnit_iff_ker_eq_bot _).2
    apply LinearMap.ker_eq_bot.mpr
    apply LinearMap.dualMap_injective_of_surjective
    exact LinearMap.range_eq_top.mp ((LinearMap.isUnit_iff_range_eq_top F).mp hF)
  have hFG : ∀ x y, b (F x) (G y) = a * b x y := by
    intro x y
    have hh := LinearMap.congr_fun hconj (b.flip.toPerfPair y)
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at hh
    have hh' := congrArg (fun f : Module.Dual (P.pairingScalar c)
      (P.pairingHc c K.carrier.obj i) ↦ f (F x)) hh
    have hinv := congrArg (fun T ↦ T (b.flip.toPerfPair y) x)
      (Ring.mul_inverse_cancel F.dualMap hFd)
    change (Ring.inverse F.dualMap (b.flip.toPerfPair y)) (F x) = b x y at hinv
    change b (F x) (G y) = a *
      (Ring.inverse F.dualMap (b.flip.toPerfPair y)) (F x) at hh'
    exact hh'.trans (congrArg (a * ·) hinv)
  have hroots := LinearMap.roots_map_charpoly_of_similitude ha hFG ι
  change ((G.charpoly).map ι).roots =
    ((F.charpoly).map ι).roots.map (fun α ↦ ι a / α) ∧ _
  refine ⟨hroots, ?_⟩
  intro α _hα
  change Polynomial.rootMultiplicity (ι a / α) (G.charpoly.map ι) =
    Polynomial.rootMultiplicity α (F.charpoly.map ι)
  have hai : ι a ≠ 0 := fun h ↦ ha (ι.injective (by simpa using h))
  have hinj : Function.Injective (fun z : M ↦ ι a / z) := by
    intro x y hxy
    apply inv_injective
    apply mul_left_cancel₀ hai
    simpa only [div_eq_mul_inv] using hxy
  rw [← Polynomial.count_roots, hroots,
    Multiset.count_map_eq_count' _ _ hinj, Polynomial.count_roots]


/-- In the proper case the first space identifies with ordinary cohomology,
intertwining the actual ordinary and compact geometric Frobenius operators.
Source: final sentence and proof step 4 (blueprint: cor-pod-reciprocal-eigenvalues).
Proof: proper Poincare duality supplies the canonical compact-to-ordinary
comparison of derived sections. Its construction is the identity-open
compactification comparison, transported from the chosen compactification by
proper refinement. Apply Hom from the scalar unit into the i-th shift. The
comparison is natural for geometric Frobenius and the Weil structure, so it
intertwines the two operators. Thus the conjugacy and root assertions above
apply with H^i(X,K) as their first space. -/
theorem poincareReciprocalProper (_hc : c = .rational ∨ c = .qbar)
    (K : P.strictWeil c)
    (_hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj)
    (i : ℤ) [IsProper P.X₀.hom] :
    ∃ e : P.pairingHc c K.carrier.obj i ≃ₗ[P.pairingScalar c]
        P.pairingH c K.carrier.obj i,
      ∀ x, e (P.reciprocalCompactOperator c K i x) =
        P.pairingCohomologyAction c _
          (P.pairingFrobenius c K.carrier.obj ((ObjectProperty.ι _).mapIso K.str)).1 i
            (e x) := by
  sorry

end WeilConjectures.CondensedPoincareDualityConventions

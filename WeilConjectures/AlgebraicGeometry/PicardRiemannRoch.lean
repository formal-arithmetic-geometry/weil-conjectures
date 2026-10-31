/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.RegularCurveDivisorCalculus
public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace
public import WeilConjectures.AlgebraicGeometry.Cohomology.CupProduct
public import WeilConjectures.AlgebraicGeometry.Curve.AdelicStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.ZetaSeries
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
public import WeilConjectures.AlgebraicGeometry.Modules.Torsion
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.Curve.PicardRRDuality
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRochCoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.ExteriorSheafComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.EulerCharZeroDimSupport

/-! # Riemann–Roch and coherent Serre duality

Source: blueprint, sec-picard-framework/sk-thm-picard-rr/_section.md, including
sk-thm-picard-rr-duality.md, clause (4) (blueprint: sk-thm-picard-rr).

The field-extension clause uses the existing canonical cohomology comparison.
Its differential isomorphism is specified on universal differentials, and the
residue trace commutes with this comparison. Together with functoriality of cup
product and evaluation this says that the displayed duality isomorphism extends
by scalars, rather than merely that its two sides have the same dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The canonical residue trace with the scalar structure induced by the given
structure morphism, rather than an additional algebra hypothesis.
Source: blueprint sk-thm-picard-rr-duality.md, clause (1)
(blueprint: sk-thm-picard-rr). This is exactly `residueTrace`, specialized to the
canonical `functionFieldAlgebra`; no trace data is chosen. -/
noncomputable def picardRRResidueTrace (k : Type u) [Field k] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1) :=
  letI := functionFieldAlgebra k X
  letI := isFunctionFieldAlgebra_functionFieldAlgebra k X
  residueTrace k X

/-- The canonical comparison between tensor pullback and the existing pullback
used by the cohomology base-change API. It uses the uniquely section-normalized
`tensorPullbackSectionAdjunction` owned by `def-pc-module-pullback`, and compares
left adjoints compatibly with their units.
Source: Stacks Project, Tags 0095 and 02KH (blueprint: sk-thm-picard-rr). -/
noncomputable def picardRRPullbackIso {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Modules.tensorPullback p ≅ Modules.pullback p :=
  (Modules.tensorPullbackSectionAdjunction p).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction p)

/-- Canonical scalar extension on cohomology, transported to tensor pullback.
Source: Stacks Project, Tag 02KH (blueprint: sk-thm-picard-rr).
The two pullbacks are compared by their adjunction units, so this is exactly
`H.baseChange`, with its output expressed using the tensor construction. -/
noncomputable def picardRRBaseChange (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] (K : Type u) [Field K] [Algebra k K]
    (M : C.Modules) (q : ℕ) :
    TensorProduct k K (M.H q) →ₗ[K]
      Modules.HOver (Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k)))
        ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
          (C ↘ Spec (.of k)))).obj M) q :=
  letI : (Modules.baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over
      (Spec (.of K)) := ⟨Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
  Modules.H.mapLinearMap K
    ((picardRRPullbackIso (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).inv.app M) q ∘ₗ
    Modules.H.baseChange (S := K) (C ↘ Spec (.of k)) M q

/-- The field-extension clause of Riemann–Roch and Serre duality.
Source: blueprint sk-thm-picard-rr-duality.md, clause (4)
(blueprint: sk-thm-picard-rr).

`picardRRBaseChange` transports the existing `H.baseChange` to tensor pullback
using the adjunction comparison pinned to its sectionwise unit. The differential
isomorphism sends the pullback of da to d(a). The last equation preserves the residue trace on every
cohomology class, so the induced trace-duality maps commute with extension of
scalars. Smoothness and geometric connectedness give geometric integrality by
the existing theorem; the instance below only supplies that derived fact. -/
def picardRRFieldExtension (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))]
    (K : Type u) [Field K] [Algebra k K] : Prop :=
  letI : GeometricallyIntegral (C ↘ Spec (.of k)) :=
    GeometricallyIntegral.of_smooth_of_geometricallyConnected (C ↘ Spec (.of k))
  letI : (Modules.baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over
      (Spec (.of K)) := ⟨Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
  IsSmoothProjectiveCurve (C.baseChangeField k K ↘ Spec (.of K)) ∧
  GeometricallyConnected (C.baseChangeField k K ↘ Spec (.of K)) ∧
  arithmeticGenus K (C.baseChangeField k K) = arithmeticGenus k C ∧
  (∀ (L : C.Modules) [L.IsInvertible],
    ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj L).degree K = L.degree k ∧
    ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj L).eulerChar K = L.eulerChar k ∧
    ∀ q : ℕ, Function.Bijective (picardRRBaseChange k C K L q)) ∧
  ∃ e : (Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj (C ↘ Spec (.of k)).relativeDifferentials ≅
        (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentials,
    (∀ (W : C.Opens) (a : Γ(C, W)),
      e.hom.val.app (op (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
        (Hom.relativeDifferentialsPullbackGenerator (C ↘ Spec (.of k))
          (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k))) W a) =
      (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentialsDerivation.d
        (X := op (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
        ((Modules.baseChangeFst (S := K) (C ↘ Spec (.of k))).app W a)) ∧
    (∀ z : (C ↘ Spec (.of k)).relativeDifferentials.H 1,
      picardRRResidueTrace K (C.baseChangeField k K)
        (Modules.H.map e.hom 1
          (picardRRBaseChange k C K (C ↘ Spec (.of k)).relativeDifferentials 1
            (1 ⊗ₜ[k] z))) =
        algebraMap k K (picardRRResidueTrace k C z))

/-- The clauses of Riemann–Roch and coherent Serre duality.
Source: blueprint sk-thm-picard-rr/_section.md (blueprint: sk-thm-picard-rr).
Noetherianity and regularity are derived from smooth projectivity inside this
predicate; they are not additional hypotheses. All its clauses are displayed
explicitly, including arbitrary-dimensional proper schemes in complement (H). -/
def picardRRConclusions (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] : Prop :=
  letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType (C ↘ Spec (.of k))
  letI : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  (∀ (L : C.Modules) [L.IsInvertible],
    L.eulerChar k = L.degree k + 1 - (arithmeticGenus k C : ℤ) ∧
    L.eulerChar k = (L.finrankH k 0 : ℤ) - (L.finrankH k 1 : ℤ) ∧
    Function.Bijective (Modules.cupPairing (picardRRResidueTrace k C) L) ∧
    (2 * (arithmeticGenus k C : ℤ) - 2 < L.degree k →
      Subsingleton (L.H 1) ∧
      (L.finrankH k 0 : ℤ) = L.degree k + 1 - (arithmeticGenus k C : ℤ)) ∧
    (0 < L.degree k → IsAmple (C ↘ Spec (.of k)) L) ∧
    ∀ D : C.Divisor, Nonempty (D.associatedModule C ≅ L) →
      L.degree k = D.sum (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val)) ∧
  (∀ f : C.functionFieldˣ,
    (C.div (Additive.ofMul f)).sum
      (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val) = 0) ∧
  (C ↘ Spec (.of k)).relativeDifferentials.degree k =
    2 * (arithmeticGenus k C : ℤ) - 2 ∧
  (∀ (F : C.Modules), F.IsQuasiCoherentFiniteType →
    F.eulerChar k = (Modules.torsion F).finrankH k 0 +
      (Modules.exteriorSheaf (Modules.torsionQuotient F) F.rank).degree k +
      (F.rank : ℤ) * (1 - (arithmeticGenus k C : ℤ))) ∧
  (∀ (K : Type u) [Field K] [Algebra k K], picardRRFieldExtension k C K) ∧
  (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (J : X.IdealSheafData), J.IsInvertible →
    IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ → IsAffine (Scheme.Opens.toScheme J.support.compl))

open TopologicalSpace in
private theorem picardRR_skyscraper_support (C : Scheme.{u}) (x : closedPoints C)
    (V : ModuleCat.{u} (C.presheaf.stalk x.val)) :
    let F : C.Modules := SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val V
    topologicalKrullDim {y : C | ¬ Subsingleton (F.presheaf.stalk y)} ≤ 0 := by
  let F : C.Modules := SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val V
  have hz (y : C) (hy : y ≠ x.val) : Subsingleton (F.presheaf.stalk y) := by
    let U : C.Opens := ⟨{x.val}ᶜ, x.property.isOpen_compl⟩
    have hyU : y ∈ U := hy
    have hzero (a : F.presheaf.stalk y) : a = 0 := by
      obtain ⟨W, hyW, s, rfl⟩ := F.presheaf.exists_germ_eq a
      have hs : F.presheaf.map (homOfLE inf_le_left : W ⊓ U ⟶ W).op s = 0 := by
        funext h
        exact False.elim (h.down.2 rfl)
      rw [← F.presheaf.germ_res_apply (homOfLE inf_le_left : W ⊓ U ⟶ W)
        y ⟨hyW, hyU⟩ s, hs, map_zero]
    exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩
  have : Subsingleton {y : C | ¬ Subsingleton (F.presheaf.stalk y)} := by
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    have ha : a.val = x.val := by_contra fun h ↦ a.property (hz a.val h)
    have hb : b.val = x.val := by_contra fun h ↦ b.property (hz b.val h)
    exact ha.trans hb.symm
  exact topologicalKrullDim_zero_of_discreteTopology _

private theorem picardRR_skyscraper_euler (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsProper (C ↘ Spec (.of k))] (x : closedPoints C)
    (hF : RingedSpace.IsCoherent C.toRingedSpace
      (SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj
          (ModuleCat.of (C.residueField x.val) (C.residueField x.val))))) :
    Modules.eulerChar k (show C.Modules from
      SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj
          (ModuleCat.of (C.residueField x.val) (C.residueField x.val)))) =
      ((C ↘ Spec (.of k)).degreeOver x.val : ℤ) := by
  let V := (ModuleCat.restrictScalars (C.residue x.val).hom).obj
    (ModuleCat.of (C.residueField x.val) (C.residueField x.val))
  let F : C.Modules := SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val V
  have hχ := (Modules.eulerChar_zero_dim_support k C F hF
    (picardRR_skyscraper_support C x V)).2.1
  let := ((C ↘ Spec (.of k)).residueFieldAlgebraMap x.val).toAlgebra
  let e : F.H 0 ≃ₗ[k] C.residueField x.val :=
    { toFun := fun z ↦ (Modules.H.zeroLinearEquiv F z) ⟨trivial⟩
      invFun := fun a ↦ (Modules.H.zeroLinearEquiv F).symm (fun _ ↦ a)
      left_inv := by
        intro z
        apply (Modules.H.zeroLinearEquiv F).injective
        simp only [LinearEquiv.apply_symm_apply]
        funext h
        rfl
      right_inv := by intro a; simp
      map_add' := by
        intro a b
        exact congrFun ((Modules.H.zeroLinearEquiv F).map_add a b) ⟨trivial⟩
      map_smul' := by
        intro c z
        rw [Modules.smul_H_eq_globalSectionsRingHom_smul, LinearEquiv.map_smul]
        change C.residue x.val (C.presheaf.germ ⊤ x.val trivial
          (globalSectionsRingHom k c)) * _ =
          (C ↘ Spec (.of k)).residueFieldAlgebraMap x.val c * _
        rw [Hom.residueFieldAlgebraMap_apply] }
  exact hχ.trans (congrArg (fun n : ℕ ↦ (n : ℤ)) e.finrank_eq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem picardRR_divisor_degree (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) :
    (D.associatedModule C).degree k =
      D.sum (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val) := by
  classical
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType (C ↘ Spec (.of k))
  let : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  let : GeometricallyReduced (C ↘ Spec (.of k)) :=
    GeometricallyReduced.of_smooth (C ↘ Spec (.of k))
  let : GlobalSectionsBijective k C := inferInstance
  obtain ⟨_, hinv, ⟨e0, _⟩, hmul, _, _, hmod⟩ := regular_curve_divisor_calculus C
    ((C.dim_eq_topologicalKrullDim).trans
      (IsIntegralCurve.topologicalKrullDim_eq_one (f := C ↘ Spec (.of k))))
  let (E : C.Divisor) : (E.associatedModule C).IsInvertible := hinv E
  let d : C.Divisor →+ ℤ :=
    { toFun := fun E ↦ (E.associatedModule C).degree k
      map_zero' := (Modules.degree_congr k e0).trans (Modules.degree_unit k)
      map_add' := by
        intro E F
        obtain ⟨e, _⟩ := hmul E F
        exact (Modules.degree_congr k e).symm.trans (Modules.degree_tensorObj _ _) }
  let w : C.Divisor →+ ℤ :=
    { toFun := fun E ↦ E.sum (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val)
      map_zero' := by simp
      map_add' := by
        intro E F
        exact Finsupp.sum_add_index' (by intros; simp) (by intros; ring) }
  have hs (x : closedPoints C) : d (Finsupp.single x 1) = w (Finsupp.single x 1) := by
    obtain ⟨V, _, i, q, _, ⟨wzero, hex⟩, ⟨eV⟩⟩ := hmod (Finsupp.single x 1) x
    have := Modules.IsInvertible.sheafOfModules_isInvertible
      (Divisor.associatedModule C ((Finsupp.single x 1 : C.Divisor) - Finsupp.single x 1))
    have := Modules.IsInvertible.sheafOfModules_isInvertible
      (Divisor.associatedModule C (Finsupp.single x 1 : C.Divisor))
    have : (cokernel i).IsFinitePresentation := Modules.isFinitePresentation_cokernel i
    let eQ : cokernel i ≅ SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj V) :=
      (cokernelIsCokernel i).coconePointUniqueUpToIso hex.gIsCokernel
    have : (SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj V)).IsFinitePresentation :=
      Modules.isFinitePresentation_of_iso eQ
    have : (SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj
          (ModuleCat.of (C.residueField x.val) (C.residueField x.val)))).IsFinitePresentation :=
      Modules.isFinitePresentation_of_iso eV
    have hcoh := (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType C
      (SheafOfModules.ringedModuleSkyscraper C.toRingedSpace x.val
        ((ModuleCat.restrictScalars (C.residue x.val).hom).obj
          (ModuleCat.of (C.residueField x.val) (C.residueField x.val))))).mpr
            ⟨inferInstance, inferInstance⟩
    have hχ := Modules.eulerChar_eq_add_of_shortExact_of_isCoherent k hex
    have hv := (Modules.eulerChar_congr k eV).trans (picardRR_skyscraper_euler k C x hcoh)
    dsimp only at hχ
    rw [hv, sub_self] at hχ
    have hz := Modules.eulerChar_congr k e0
    change (Divisor.associatedModule C (Finsupp.single x 1 : C.Divisor)).degree k = _
    dsimp [Modules.degree, w]
    rw [Finsupp.sum_single_index (by simp)]
    linarith
  have hdw : d = w := by
    apply Finsupp.addHom_ext'
    intro x
    ext
    exact hs x
  exact DFunLike.congr_fun hdw D

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Riemann–Roch, coherent Serre duality, field extension and the ample complements.
Source: blueprint sk-thm-picard-rr/_section.md and its duality detail
(blueprint: sk-thm-picard-rr).

Proof, following the ten steps of the node:
1. Smooth projectivity gives a regular integral proper curve. Coherent cohomology
   is finite and vanishes above degree one. Geometric connectedness and smoothness
   give H0(O)=k, hence chi(O)=1-g; proper smooth curves are projective by Tag 0A26.
2. regular_curve_divisor_calculus gives the modification sequence at each closed
   point x. Euler additivity and zero-dimensional support give the increment
   [kappa(x):k]. Induction on the sum of absolute coefficients gives divisor RR.
3. Every line bundle is O(D). Principal divisors represent O, hence have degree
   zero. Tensor multiplication identifies divisor degree with Modules.degree.
4. Take the torsion subsheaf T of a coherent F. Its support is zero-dimensional,
   so chi(T)=h0(T); the torsion-free quotient E is a vector bundle of generic rank.
5. Induct on the rank of E using a saturated line subbundle, vector-bundle quotient,
   determinant multiplicativity and Euler additivity. Rank zero has determinant O.
   This proves the stated coherent formula with exactly the torsion determinant degree.
6. Smooth differentials have rank one. Serre duality with the residue trace gives
   the perfect cup pairing. Apply duality to O in both degrees to obtain
   h0(omega)=g, h1(omega)=1, and RR gives deg(omega)=2g-2.
7. If deg(L)>2g-2, omega tensor L-dual has negative degree. A nonzero section
   would give an effective zero divisor of nonnegative degree. Duality therefore
   kills H1(L), and RR gives the formula for h0(L).
8. Flat cohomology base change preserves the finite dimensions, Euler characteristic,
   genus and degree. The universal differential comparison identifies omega after
   base change, and residue trace compatibility gives scalar extension of duality.
9. For positive degree, extend to an algebraic closure and choose m with
   m deg(L)>=2g+1. The vanishing formula for twists by P and P+Q (also P=Q)
   gives point and tangent separation. Very ampleness descends, hence L is ample.
10. For any proper k-scheme and effective Cartier ideal J, apply
    isAffine_compl_of_isAmple_dual_toModules to the open complement of J.support.
    This includes the empty divisor whenever its dual ideal module is ample. -/
theorem picard_riemannRoch (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] : picardRRConclusions k C := by
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType (C ↘ Spec (.of k))
  let : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  let : GeometricallyReduced (C ↘ Spec (.of k)) :=
    GeometricallyReduced.of_smooth (C ↘ Spec (.of k))
  let : GlobalSectionsBijective k C := inferInstance
  unfold picardRRConclusions
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    have := Modules.IsInvertible.sheafOfModules_isInvertible L
    refine ⟨Modules.eulerChar_eq_degree_add L,
      Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one L, ?_, ?_, ?_, ?_⟩
    · let := functionFieldAlgebra k C
      let := isFunctionFieldAlgebra_functionFieldAlgebra k C
      exact (serreDuality_residueTrace k C L
        (SheafOfModules.IsInvertible.isFiniteLocallyFree L)).1
    · intro hd
      have hdim := Modules.finrankH_one_eq_zero_of_degree (k := k) L (by omega)
      have : FiniteDimensional k (L.H 1) := Modules.finiteDimensional_H_of_isProper L 1
      exact ⟨Module.finrank_zero_iff.mp hdim, finrankH_zero_eq (k := k) L (by omega)⟩
    · exact isAmple_of_degree_pos L
    · intro D hD
      obtain ⟨e⟩ := hD
      exact (Modules.degree_congr k e).symm.trans (picardRR_divisor_degree k C D)
  · intro f
    obtain ⟨_, _, _, _, _, hprincipal, _⟩ := regular_curve_divisor_calculus C
      ((C.dim_eq_topologicalKrullDim).trans
        (IsIntegralCurve.topologicalKrullDim_eq_one (f := C ↘ Spec (.of k))))
    obtain ⟨e, _⟩ := hprincipal f
    exact (picardRR_divisor_degree k C _).symm.trans
      ((Modules.degree_congr k e).trans (Modules.degree_unit k))
  · exact degree_relativeDifferentials
  · intro F hF
    have := hF.1
    have := hF.2
    have : F.IsFinitePresentation := by
      have hfin (U : C.affineOpens) : (F.over U.1).IsFinitePresentation := by
        have : IsNoetherianRing Γ(C, U.1) := IsLocallyNoetherian.component_noetherian U
        have : Module.Finite Γ(C, U.1) Γ(F, U.1) :=
          Modules.finite_sections_of_finiteType F U.2
        exact (((Modules.quasicoherent_finite_type_affine.{u, u} C).2 F
          inferInstance).1 U.1 U.2).2.mpr
          (Module.finitePresentation_of_finite Γ(C, U.1) Γ(F, U.1))
      exact SheafOfModules.IsFinitePresentation.of_coversTop F
        (fun U : C.affineOpens ↦ U.1) (by
          rw [Opens.coversTop_iff]
          exact iSup_affineOpens_eq_top C)
    have h := Modules.eulerChar_eq_coherentDegree_add k F
    unfold Modules.coherentDegree at h
    rw [← Modules.degree_congr k
      (Modules.exteriorSheafIsoExteriorPower (Modules.torsionQuotient F) F.rank)] at h
    exact h
  · intro K _ _
    let : GeometricallyIntegral (C ↘ Spec (.of k)) :=
      GeometricallyIntegral.of_smooth_of_geometricallyConnected (C ↘ Spec (.of k))
    let : (Modules.baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over
        (Spec (.of K)) := ⟨Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
    have := Hom.isInvertible_relativeDifferentials (C ↘ Spec (.of k))
    have := Modules.IsInvertible.of_sheafOfModules (C ↘ Spec (.of k)).relativeDifferentials
    obtain ⟨hC, hgeo, hg, _, e, he, _, ht⟩ :=
      (picard_rr_duality k C (C ↘ Spec (.of k)).relativeDifferentials).2.2.2.2.2 K
    let := hC
    refine ⟨hC, hgeo, hg, ?_, e, he, ?_⟩
    · intro L _
      have := Modules.IsInvertible.sheafOfModules_isInvertible L
      refine ⟨?_, ?_, ?_⟩
      · exact (Modules.degree_congr K
          ((picardRRPullbackIso _).app L)).trans (Modules.degree_pullback k K L)
      · exact (Modules.eulerChar_congr K
          ((picardRRPullbackIso _).app L)).trans (Modules.eulerChar_pullback K L)
      · intro q
        exact (Modules.H.mapLinearEquiv
          ((picardRRPullbackIso _).symm.app L) q).bijective.comp
            (Modules.H.baseChange_bijective_of_isSeparated (C ↘ Spec (.of k)) L q)
    · intro z
      let := functionFieldAlgebra k C
      let := isFunctionFieldAlgebra_functionFieldAlgebra k C
      let := functionFieldAlgebra K (C.baseChangeField k K)
      let := isFunctionFieldAlgebra_functionFieldAlgebra K (C.baseChangeField k K)
      have h := ht (𝟙 _) ((Modules.moduleCohomologyExtResolutionEquiv C _ 1).symm z) 1 1
      simp only [one_smul, one_mul] at h
      have hφ : (Modules.tensorPullback (Modules.baseChangeFst (S := K)
          (C ↘ Spec (.of k)))).map (𝟙 (C ↘ Spec (.of k)).relativeDifferentials) ≫
            e.hom = e.hom := by
        rw [CategoryTheory.Functor.map_id, Category.id_comp]
      have hid (a : Modules.scalarCohomology (C ↘ Spec (.of k))
          (C ↘ Spec (.of k)).relativeDifferentials 1) :
          Modules.scalarCohomologyMap (C ↘ Spec (.of k)) (𝟙 _) 1 a = a := by
        change ((RingedSpace.moduleCohomology C.toRingedSpace 1).map (𝟙 _)).hom a = a
        rw [CategoryTheory.Functor.map_id]
        rfl
      rw [hφ, hid] at h
      unfold picardRRModuleTrace at h
      change residueTrace K (C.baseChangeField k K)
        (Modules.moduleCohomologyExtResolutionEquiv (C.baseChangeField k K) _ 1
          (((RingedSpace.moduleCohomology (C.baseChangeField k K).toRingedSpace 1).map
            e.hom).hom _)) = _ at h
      rw [Modules.moduleCohomologyExtResolutionEquiv_naturality] at h
      simp only [picardRRModuleBaseChangeValue] at h
      simp only [AddEquiv.apply_symm_apply] at h
      unfold picardRRResidueTrace picardRRBaseChange
      rw [LinearMap.comp_apply]
      erw [Modules.H.mapLinearMap_apply K]
      exact h
  · intro X _ _ J hJ hA
    exact isAffine_compl_of_isAmple_dual_toModules (X ↘ Spec (.of k)) hJ hA
      (Scheme.Opens.ι J.support.compl) (Scheme.Opens.range_ι _)

end AlgebraicGeometry.Scheme

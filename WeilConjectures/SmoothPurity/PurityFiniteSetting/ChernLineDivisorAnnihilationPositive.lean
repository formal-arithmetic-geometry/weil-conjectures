/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialRestriction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernCartierRootAnnihilation
import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisor
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern

/-! # The relative hyperplane divisor annihilates the lower Chern polynomial

Source: Stacks Project, Tag 0FI5, proposition-chern-class, invertible-submodule paragraph.
(blueprint: lem-pur-chern-line-divisor-annihilation-positive).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace WeilConjectures.PurityFiniteSetting

private theorem kummer_one (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) :
    Etale.kummerFirstChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) 1 = 0 := by
  have h := kummer_mul P a 1 1
  rw [one_mul] at h
  apply add_left_cancel
  exact h.symm.trans (add_zero _).symm

private theorem kummer_inv (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (M : T.Pic) :
    Etale.kummerFirstChern P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) M⁻¹ =
      -Etale.kummerFirstChern P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) M := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm, ← kummer_mul P a, mul_inv_cancel, kummer_one P a]

private theorem pic_tensorPullback {S T : Scheme.{u}} (f : T ⟶ S)
    (L : S.Modules) [L.IsInvertible]
    [((Scheme.Modules.tensorPullback f).obj L).IsInvertible] :
    Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.tensorPullback f).obj L) := by
  have hp : Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) := by
    apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
    exact ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Scheme.Modules.pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso L)⟩
  exact hp.trans (Scheme.Pic.ofIsInvertible_eq_of_iso
    ((projectiveBundleTensorPullbackIso f).app L).symm)

private theorem divisor_root (P : PurityFiniteSetting.{u}) {S Z : Scheme.{u}}
    (a : S ⟶ Spec (.of P.field.k)) (L F : S.Modules) [L.IsInvertible]
    (D : ProjectiveBundleRealization S F) (hD : D.L.IsInvertible)
    (i : Z ⟶ D.A.data.relProj) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (δ : i.ker.toModulesᵛ ≅
      D.L ⊗ (Scheme.Modules.tensorPullback D.A.data.relProjHom).obj Lᵛ) :
    P.ordinaryFiniteFlagRoot (D.A.data.relProjHom ≫ a) i.ker.toModulesᵛ
        hI.isInvertible_dual_toModules = P.ordinaryFiniteLineDivisorRoot a L D hD := by
  let f := D.A.data.relProjHom
  let := hD
  let := hI.isInvertible_dual_toModules
  let hTL : ((Scheme.Modules.tensorPullback f).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso f).app L).symm
  let := hTL
  let hTD : ((Scheme.Modules.tensorPullback f).obj Lᵛ).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso f).app Lᵛ).symm
  let := hTD
  have hp : Scheme.Pic.ofIsInvertible i.ker.toModulesᵛ =
      Scheme.Pic.ofIsInvertible D.L *
        (Scheme.Pic.ofIsInvertible ((Scheme.Modules.tensorPullback f).obj L))⁻¹ := by
    rw [Scheme.Pic.ofIsInvertible_eq_of_iso δ, Scheme.Pic.ofIsInvertible_tensorObj,
      ← pic_tensorPullback f Lᵛ, Scheme.Pic.ofIsInvertible_dual]
    change _ * (Scheme.Pic.mapHom f) _ = _
    rw [map_inv]
    exact congrArg (fun z ↦ Scheme.Pic.ofIsInvertible D.L * z⁻¹) (pic_tensorPullback f L)
  simp only [ordinaryFiniteLineDivisorRoot, ordinaryFiniteFlagRoot,
    projectiveBundleChern, sub_eq_add_neg]
  rw [hp, kummer_mul P (D.A.data.relProjHom ≫ a),
    kummer_inv P (D.A.data.relProjHom ≫ a)]


/-- The geometric vanishing equation before any candidate coefficient is considered.
The lower polynomial is evaluated on P(F), not on P(G).

Source: Stacks Project, Tag 0FI5, proposition-chern-class, restriction-zero argument;
Cohomology Tags 0G75, 0G76, 0G77 for the supported cup action.
(blueprint: lem-pur-chern-line-divisor-annihilation-positive).

Proof: since n>0, the normalized quotient bundle Q=P(G) is a Cartier divisor of
D=P(F) by the line-subbundle divisor theorem. Its tautological line is the
restriction of D.L, and its projection is the restriction of D's projection.
Consequently the lower signed polynomial value restricts to its own defining
projective relation on Q, hence to zero. Pullback naturality of the Kummer map
and the normalized Tate power comparisons identify every term, including its
natural-number degree transport. The divisor line is O_D(1) tensor p*(L dual).
Kummer additivity and duality make its ordinary class h-p*x, exactly
ordinaryFiniteLineDivisorRoot. The Cartier Kummer arrow supplies a supported
class with that ordinary image. Apply closed-supported cup vanishing to the
restriction-zero polynomial and this supported divisor class. After forgetting
support and identifying the full-support unit and Tate coordinates, its ordinary
cup is the displayed ordinaryFiniteHyperplaneStep, so it is zero.

Here n is positive, so Q=P(G) has a normalized projective-bundle realization.
No rank-zero quotient or projective-bundle edge case is part of this statement. -/
theorem lineSubbundleChernPolynomial_annihilation_positive (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : 0 < n) (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank (n + 1)] [G.IsFiniteLocallyFreeOfRank n]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (D : ProjectiveBundleRealization S F) (hD : D.L.IsInvertible)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.ordinaryFiniteHyperplaneStep D.A.data.relProj
      (P.ordinaryFiniteLineDivisorRoot a L D hD) n
      (P.ordinaryFiniteProjectivePolynomialValue t a D hD n
        (P.ordinaryFiniteChernClasses a G n)) = 0 := by
  classical
  have hGpred : G.IsFiniteLocallyFreeOfRank ((n - 1) + 1) := by
    convert (inferInstance : G.IsFiniteLocallyFreeOfRank n) using 1
    omega
  let := hGpred
  obtain ⟨geometry⟩ := exists_projectiveBundleTautologicalGeometry S (n - 1) G
  let Q := geometry.realization
  have hGminus : G.IsFiniteLocallyFreeOfRank ((n + 1) - 1) := by
    simpa using (inferInstance : G.IsFiniteLocallyFreeOfRank n)
  let := hGminus
  obtain ⟨hD', hQ, i, hi, θ, hclosed, hquot, hker, hreg, heff, hδ, hfinite⟩ :=
    lineSubbundle_projective_divisor S (n + 1) (by omega) L F G ι π w hexact D Q
  let := hclosed
  have hI : i.ker.IsInvertible := by
    rw [hker]
    exact hreg
  obtain ⟨δ, hδ⟩ := hδ
  obtain ⟨hsep, hft, hqc, hqsep, hqft, hqqc⟩ :=
    hfinite P.field.k a inferInstance inferInstance inferInstance
  let := hsep
  let := hft
  let := hqc
  have hr := ordinaryFiniteProjectivePolynomialValue_restrict_eq_zero P a n hn G
    D hD Q hQ i hi θ t
  have hz := ordinaryFiniteCartierRoot_annihilates P (D.A.data.relProjHom ≫ a)
    i hI n (P.ordinaryFiniteProjectivePolynomialValue t a D hD n
      (P.ordinaryFiniteChernClasses a G n)) t hr
  rw [divisor_root P a L F D hD i hI δ] at hz
  exact hz

end WeilConjectures.PurityFiniteSetting

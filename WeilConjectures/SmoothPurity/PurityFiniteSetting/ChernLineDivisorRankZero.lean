/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProjectiveLineQuotientIso
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # The rank-one edge of the line-divisor equation

Source: Stacks Project, Tag 0FI5, the invertible case of the Chern construction.
(blueprint: lem-pur-chern-line-divisor-rank-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem rank_zero_isZero {X : Scheme.{u}} (M : X.Modules)
    [M.IsFiniteLocallyFreeOfRank 0] : IsZero M := by
  have hz (Y : Scheme.{u}) : IsZero
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin 0))) :=
    (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun i ↦ isEmptyElim i)
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := 0)
  exact Scheme.Modules.isZero_of_iSup_eq_top M U hU (fun i ↦ (hz (U i).toScheme).of_iso (e i).some)

private theorem zero_root_step (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (i : ℕ) (α : P.ordinaryFiniteCohomology T i) :
    P.ordinaryFiniteHyperplaneStep T 0 i α = 0 := by
  simp [ordinaryFiniteHyperplaneStep, ordinaryFiniteHyperplaneStepRaw, ProEtale.derivedTensor]

/-- With a rank-zero quotient, the relative divisor root is zero and annihilates the
lower polynomial; no projective bundle of the quotient is formed.

Source: Stacks Project, Tag 0FI5, invertible case of proposition-chern-class.
(blueprint: lem-pur-chern-line-divisor-rank-zero).

Proof: rank-zero local frames make G zero, so short exactness makes L→F an
isomorphism. The tautological quotient for the rank-one bundle F is an isomorphism
between line bundles. Composing these two isomorphisms identifies D.L with p*L.
Picard invariance identifies their Kummer arrows, so the relative divisor root
h-c_1(p*L) is zero. The tensor construction is additive in the root and sends the
zero root to zero on every class, hence in particular on the lower polynomial.
The argument includes the empty base and uses no purity or Cartier construction. -/
theorem lineSubbundleChernPolynomial_annihilation_rankZero (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (a : S ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank 1] [G.IsFiniteLocallyFreeOfRank 0]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (D : ProjectiveBundleRealization S F) (hD : D.L.IsInvertible)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.ordinaryFiniteHyperplaneStep D.A.data.relProj
      (P.ordinaryFiniteLineDivisorRoot a L D hD) 0
      (P.ordinaryFiniteProjectivePolynomialValue t a D hD 0
        (P.ordinaryFiniteChernClasses a G 0)) = 0 := by
  have hι : IsIso ι := hexact.isIso_f_iff.mpr (rank_zero_isZero G)
  have hq : IsIso D.quotient := Scheme.Modules.projectiveLineQuotient_isIso D hD
  let p := D.A.data.relProjHom
  have hpL : ((Scheme.Modules.tensorPullback p).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso p).app L).symm
  let e : D.L ≅ (Scheme.Modules.tensorPullback p).obj L :=
    (asIso D.quotient).symm ≪≫
      ((Scheme.Modules.tensorPullback p).mapIso (asIso ι)).symm
  have hr : P.ordinaryFiniteLineDivisorRoot a L D hD = 0 := by
    let := hD
    let := hpL
    unfold ordinaryFiniteLineDivisorRoot projectiveBundleChern ordinaryFiniteFlagRoot
    rw [Scheme.Pic.ofIsInvertible_eq_of_iso e]
    exact sub_self _
  rw [hr]
  exact zero_root_step P _ 0 _

end WeilConjectures.PurityFiniteSetting

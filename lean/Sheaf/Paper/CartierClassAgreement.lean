/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.PurityDivisorClass
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.PurityRelativeCone
import Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.SupportedHomPullback
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology

/-! # Agreement of the two relative Cartier Kummer constructions

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-localized-top-chern.proof.md, Step 4 (L1)
(blueprint: lem-pur-cartier-class-agreement).

The Cartier map is expressed in its published etale-origin root chart. Its witness is
literally the etale component of cartier_kummer_map, at quotient index n-1 and Kummer
index n-1; a successor split makes this indexing definitionally exact. CartierKummerRealization
identifies its site-comparison image with c_D by the supported-source and root-projection
comparisons. Thus no new Kummer class, twist, or arbitrary comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The published Cartier map's etale witness at the actual positive coefficient level.
Source: lem-amb-cartier-kummer-map, CartierEtaleKummerFamily and realization,
and def-pur-frame-class, N=ell^n (blueprint: lem-pur-cartier-class-agreement). -/
def agreementCartierEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2 := by
  cases P with
  | @mk F C E hE level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n =>
      letI : FiniteDimensional (Padic C.l) E := hE
      let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
      have hT : IsUnit (C.l : Γ(T, ⊤)) :=
        (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
          (by simpa only [diagonalExponent, Nat.cast_pow] using Q.diagonalExponent_isUnit a)
      exact (Etale.cartier_kummer_map C.l E).2.exists.choose.1
        n n Q.diagonalExponent_annihilates i hI hT

/-- c_D in the canonical finite-root chart of A(1), with the supported source
normalized by the constant quotient. CartierKummerRealization supplies exactly these
comparisons; functorialCupCompare is their published supported-Hom presentation.
Source: lem-amb-cartier-kummer-map, realization and def-pur-frame-class, theta
(blueprint: lem-pur-cartier-class-agreement). -/
def agreementCartierMap (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : P.FunctorialCupH true i 2 1 :=
  P.functorialCupCompare i 2 1 (P.agreementCartierEtale a i hI).hom

/-- The general relative divisor class is the canonical supported Cartier map,
and it pulls back along every Cartier-preserving morphism of separated finite-type
k-schemes, in the supported-Hom model of supported_cohomology_hom.

Source: blueprint thm-pur-localized-top-chern.proof.md, Step 4 (L1)
(blueprint: lem-pur-cartier-class-agreement).

Proof, following the seven DAG steps:
1. Both constructions use I_D dual and its canonical section, hence the same frame
   torsor with its specified frame on T minus D (lem-sc-line-bundle-torsor,
   lem-amb-relative-torsor-cohomology, lem-pur-divisor-class).
2. Apply the relative Kummer boundary at N=ell^n. N is invertible and kills A
   at every positive level, without ramification divisibility. The coefficient
   map on roots is sigma rho of def-pur-frame-class. This gives cl(D).
3. The module/abelian derived comparison respects restriction, hence the signed
   relative cone (lem-weil-pbc-derived-module-underlying-comparison,
   lem-pur-divisor-relative-cone). ClosedSupportHom realizes this as b_D over Z/N.
4. A closed immersion is finite, so its etale direct image is exact
   (lemma-weil-pbc-finite-direct-image-exact). The normalized derived scalar unit
   sends x to x tensor 1 (lem-pur-sheaf-ring-derived-coefficient-adjunction).
   The finite root line is flat and its degree-zero complex is K-flat
   (lem-asd-finite-etale-twist-line, lem-pc-bounded-above-flat-kflat-site).
   Thus the extended arrow represents the same coefficient image globally,
   by lem-asd-ordinary-supported-kummer, without flatness of A over Z/N.
5. The roots-projection target comparison sends v tensor a to a sigma rho(v),
   so its composite with the scalar unit is sigma rho. Supported-Hom naturality
   and site comparison identify the whole relative class, including its lift
   and sign (lem-pur-supported-hom, lem-pur-supported-hom-pullback).
6. This is precisely the normalized CartierEtaleKummerFamily realization of c_D
   in lem-amb-cartier-kummer-map, proving the first equality.
7. That map pulls back when the new divisor is Cartier. Supported-Hom pullback
   commutes with the same source and twist comparisons. The canonical pullback
   is functorialCupPullback of lem-pur-supported-cup-functoriality; injectivity
   of the supported-Hom identification gives the second equality. -/
theorem cartier_class_agreement (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    P.generalDivisorClass a i hI = P.agreementCartierMap a i hI ∧
    ∀ {T' D' : Scheme.{u}} (a' : T' ⟶ Spec (.of P.field.k))
      [IsSeparated a'] [LocallyOfFiniteType a'] [QuasiCompact a']
      (h : T' ⟶ T) (_ha : h ≫ a = a') (i' : D' ⟶ T') [IsClosedImmersion i']
      (w : D' ⟶ D) (sq : ChosenCartesianSquare w i' i h) (hI' : i'.ker.IsInvertible),
      P.functorialCupPullback true i i' h w sq a 2 1 (P.generalDivisorClass a i hI) =
        P.generalDivisorClass a' i' hI' := by
  sorry

end WeilConjectures.PurityFiniteSetting

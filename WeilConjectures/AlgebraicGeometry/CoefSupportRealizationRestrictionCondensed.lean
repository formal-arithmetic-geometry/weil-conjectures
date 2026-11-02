/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.ProperRestrictionSiteSquareStatement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory

/-! # Finite coefficient compact-support realization and restriction

Source: the final paragraph of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/
sk-thm-sf-package/lem-coef-finite-exceptional.md`,
with Stacks Tags 09AF and 099R (blueprint: lem-coef-support-realization-restriction).

All categories are the ordinary constant-coefficient (fixed-ring) presentation, as the
node permits through the finite condensed/ordinary identification of
`sk-prop-sf-rf-shriek-preservation`.  `δ_T`, `b_p`, `c_p^p` and `c_p^e` are exactly the recorded
declarations of `lem-sf-proper-restriction-site-square` (`properRestrictionComparisonPlus`,
`properRestrictionBoundaryPlus`, `properRestrictionScalarPlus`,
`Etale.derivedLowerStarRestrictScalarsIso`).  The open factors are the canonical maps that
`lem-sf-open-restriction-site-square` specifies, written in the same presentation: `b_j` is the
inverse canonical extension-by-zero adjunction comparison (`properOpenSiteExtensionIso`), and
`c_j^s` is the inverse mate of the restriction/inverse-image identification, i.e. the map that
is the identity on underlying abelian extensions by zero and is normalized by the open-adjunction
unit equation.  The recorded Lean of the open square (`OpenRestrictionSiteComparisons`,
`canonicalOpenScalarProetale`) is stated in the condensed module-object presentation; its
identification with these maps is step 1 of the proof (the coefficient identification), not a
statement of this module.  The compact-support comparison is the composite `Rp_*(b_j); b_p`, and
the compact-support scalar comparison the composite `Rp_*(c_j); c_p`; no endpoint isomorphism
is chosen.

Proof plan (the proof is intentionally postponed at this stage): (1) use the exact
finite condensed/ordinary coefficient identification and the specified restriction
maps; (2) apply the open square to `c.i` and the proper square to `c.g` after
extension by zero, using exactness of open extension and qcqs compactification maps;
(3) expand the two composites, use naturality to move `c_p` across `b_j`, apply the
open and proper square equalities, and cancel the adjacent comparison isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- The coefficient ring `A_{r+1} = R / ϖ^(r+1)` in the fixed-ring presentation (lifted to
universe `u + 1`).  The index is shifted so that every `r : ℕ` gives a level `≥ 1`; the node's
`A_r` with `r ≥ 1` is `supportCoeff l E (r - 1)`.
Source: `def-weil-l-adic-coefficient-extension`, clause 4
(blueprint: lem-coef-support-realization-restriction). -/
abbrev supportCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (r : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (r + 1))

/-- The quotient map `A_{m+1} → A_{n+1}` for `n ≤ m`, induced by the identity of `R` and the
inclusion of powers of the uniformizer ideal (the transition homomorphism of
`def-weil-l-adic-coefficient-extension`, clause 4)
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportCoeffQuotientBase (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {m n : ℕ} (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The quotient map at the lifted coefficient universe
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportCoeffQuotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {m n : ℕ} (h : n ≤ m) :
    supportCoeff l E m →+* supportCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1} (supportCoeffQuotientBase l E h)

/-- The positive-level coefficient rings are finite (`def-weil-l-adic-coefficient-extension`,
clause 4, via `Padic.finite_coefficientExtensionRing`)
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable instance supportCoeffFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (r : ℕ) :
    Finite (supportCoeff l E r) := by
  let _ : Finite (Padic.coefficientExtensionRing l E (r + 1)) :=
    Padic.finite_coefficientExtensionRing l E (r + 1) (Nat.succ_pos r)
  infer_instance

/-- Open site boundary `b_{j,C} : j^p_! ν_X^* ≅ ν_Z^* j^e_!`, in the fixed-ring D+ presentation:
the inverse of the canonical extension-by-zero adjunction comparison, extended termwise
(`lem-sf-open-restriction-site-square`, the map `b_R`; Stacks 09AF)
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportOpenBoundaryPlus (C : Type (u + 1)) [CommRing C]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (siteComparisonDerivedPullbackPlus X C) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategoryPlus ⋙
        siteComparisonDerivedPullbackPlus Z C :=
  (properOpenSiteExtensionIso C j).symm

/-- Proper site boundary `b_p`: exactly the recorded `properRestrictionBoundaryPlus` of
`lem-sf-proper-restriction-site-square` (the inverse of the canonical direct-image mate)
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportProperBoundaryPlus (C : Type (u + 1)) [CommRing C] [Finite C]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p] :
    (siteComparisonDerivedPullbackPlus Z C) ⋙
        (lowerStar (ModuleCat.{u + 1} C) p).rightDerivedFunctorPlus ≅
      (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} C) p) ⋙
        siteComparisonDerivedPullbackPlus Y C :=
  properRestrictionBoundaryPlus C p

/-- The support realization `χ_C : F_C^p ν_{X,C}^* ≅ ν_{Y,C}^* F_C^e`, defined as
`Rp_*(b_j); b_p` with all D+ associators made explicit
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportSiteRealizationPlus (C : Type (u + 1)) [CommRing C] [Finite C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    siteComparisonDerivedPullbackPlus X C ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} C) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} C) c ⋙
        siteComparisonDerivedPullbackPlus Y C := by
  let bj := supportOpenBoundaryPlus C c.i
  let bp := supportProperBoundaryPlus C c.g
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight bj _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ bp ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical pro-etale open scalar map `c_j^p : j^A_! U_X ⟶ U_Z j^B_!`: the inverse mate,
for the open adjunctions `j_! ⊣ j^*`, of the restriction/inverse-image identification
`upperStarRestrictScalarsIso` (itself conjugate to the identity).  It is the identity on
underlying abelian extensions by zero, normalized by the open-adjunction unit equation, as
`lem-sf-open-restriction-site-square` specifies for `c^p`
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportOpenScalarProMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ :=
  (mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (TwoSquare.mk _ _ _ _
        (AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso φ j).inv)

/-- The open scalar mate `c_j^p` is invertible: this is the isomorphism clause for `c^p` in
`lem-sf-open-restriction-site-square` (via `def-sfb-comap-open-immersion-shriek-iso`), in the
fixed-ring presentation (blueprint: lem-coef-support-realization-restriction).

Proof: (1) by the unit equation of the inverse mate, `j^*` of the mate composed with the
open unit is the inverse of `upperStarRestrictScalarsIso` composed with the unit, hence
`j^*` of the mate is an isomorphism; (2) off the open, both `j^A_! U_X F` and
`U_Z j^B_! F` vanish; (3) isomorphisms are detected on the open and on its complement
(stalks / points of the pro-etale site), so the mate is an isomorphism, exactly as in the
etale case `Etale.coefficientRestrictionOpenMap_isIso`. -/
theorem supportOpenScalarProMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (supportOpenScalarProMap φ j) := by
  sorry

/-- The D+ form of `c_j^p`, obtained termwise from the canonical open scalar mate
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportOpenScalarProPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategoryPlus := by
  letI := supportOpenScalarProMap_isIso φ j
  exact (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (supportOpenScalarProMap φ j)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _

/-- The support restriction `c_f^p : F_A^p U_X^p ≅ U_Y^p F_B^p`, defined as `Rp_*(c_j^p); c_p^p`,
with `c_p^p` the recorded `properRestrictionScalarPlus`
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportRestrictionProPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (supportOpenScalarProPlus φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properRestrictionScalarPlus φ c.g) ≪≫
    (Functor.associator _ _ _).symm

/-- The D+ form of the etale open scalar map `c_j^e`: termwise the existing canonical inverse
mate `Etale.coefficientRestrictionOpenMap` of the etale restriction/inverse-image
identification (identity on underlying extensions by zero, unit-normalized), with its proved
`IsIso` (blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportOpenScalarEtalePlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus ⋙
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus := by
  letI := Etale.coefficientRestrictionOpenMap_isIso φ j
  exact (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (Etale.coefficientRestrictionOpenMap φ j)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _

/-- The etale support restriction `c_f^e : F_A^e U_X^e ≅ U_Y^e F_B^e`, defined as
`Rp_*(c_j^e); c_p^e`, where `c_p^e` is the inverse of `Etale.derivedLowerStarRestrictScalarsIso`,
exactly the map of the recorded proper square
(blueprint: lem-coef-support-realization-restriction). -/
noncomputable def supportRestrictionEtalePlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (supportOpenScalarEtalePlus φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.derivedLowerStarRestrictScalarsIso φ c.g).symm ≪≫
    (Functor.associator _ _ _).symm

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The finite support realization/restriction square: for `n ≤ m` and every
`K ∈ D⁺(X_et, A_{n+1})`,
`F_A^p(δ_{X,K}); c^p_{f,ν_X^* K}; U_Y^p(χ_{B,K})
  = χ_{A,U_X^e K}; ν_{Y,A}^*(c^e_{f,K}); δ_{Y,F_B^e K}`.
Source: the final paragraph of the proof of `lem-coef-finite-exceptional`
(`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
lem-coef-finite-exceptional.md`), Stacks 09AF and 099R
(blueprint: lem-coef-support-realization-restriction).

The levels are `A = A_{m+1}`, `B = A_{n+1}` (see `supportCoeff`), covering all `1 ≤ n ≤ m` of
the node.  The node's standing hypotheses (`k = F̄_q`, separated finite-type schemes) are not
used: the statement holds for any compactification of any morphism of schemes, since only the
open immersion `c.i` and the proper (hence qcqs) `c.g` enter.  No finite-Tor, constructibility
or flatness hypothesis on `K`.

Proof (node steps):
(1) use the exact termwise finite condensed/ordinary equivalence of
`sk-prop-sf-rf-shriek-preservation`; under it both restrictions keep the abelian sheaf and act
through `A_m → A_n` (`def-pc-sheaf-restrict-scalars`, `sk-def-sfb-coefficient-change`), so the
maps of the open square are those of this fixed-ring presentation.
(2) apply `lem-sf-open-restriction-site-square` to `c.i`, `A → B` and `K` (square with
`b_j, c_j, δ_X, δ_Z`), and `properRestrictionSiteSquare_statement`
(`lem-sf-proper-restriction-site-square`) to `c.g`, `A → B` and `j^e_{!,B} K`, which is bounded
below by exactness of extension by zero (`lem-weil-pbc-extension-by-zero-exact`).
(3) expand `c_f^p` and `χ_B` on the left; naturality of `c_p^p` at `b_{j,B,K}` moves the open site
comparison past the proper scalar comparison; apply `Rp_{*,A}^p` to the open square; the middle
three factors become `Rp_{*,A}^p(δ_Z); c_p^p; U_Y^p(b_{p,B})`, replaced by the proper square with
`b_{p,A}; ν_{Y,A}^*(c_p^e); δ_Y`; naturality of `b_{p,A}` at `c^e_{j,K}` moves the open scalar map
to the etale side; the first two factors are `χ_A` and the next two `ν_{Y,A}^*(c_f^e)`.  The
associators are inserted identically on both sides. -/
theorem finiteSupportRealization_restriction_statement
    {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (supportCoeff l E n)))) :
    (rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (supportCoeff l E m)) c).map
        ((properRestrictionComparisonPlus X (supportCoeffQuotient l E h)).hom.app K) ≫
      (supportRestrictionProPlus (supportCoeffQuotient l E h) c).hom.app
        ((siteComparisonDerivedPullbackPlus X (supportCoeff l E n)).obj K) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology Y)
        (supportCoeffQuotient l E h)).mapDerivedCategoryPlus.map
        ((supportSiteRealizationPlus (supportCoeff l E n) c).hom.app K) =
    (supportSiteRealizationPlus (supportCoeff l E m) c).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology
          (supportCoeffQuotient l E h)).mapDerivedCategoryPlus.obj K) ≫
      (siteComparisonDerivedPullbackPlus Y (supportCoeff l E m)).map
        ((supportRestrictionEtalePlus (supportCoeffQuotient l E h) c).hom.app K) ≫
      (properRestrictionComparisonPlus Y (supportCoeffQuotient l E h)).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (supportCoeff l E n)) c).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale

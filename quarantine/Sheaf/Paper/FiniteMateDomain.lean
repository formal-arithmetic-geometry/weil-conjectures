/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!
# Finite ordinary exchange and its specified site comparisons

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (4); Stacks Tags 0DDE, 0F09, 0D6J, 07A7 and 09A6
(blueprint: lem-sf-bc-finite-mate-domain).

The ambient finite-coefficient map is `ProEtale.derivedBaseChangeMap`, the actual
unit--square--counit mate in fixed-scalar module coordinates used by the finite
operations of `SixFunctorOperationDatum.finiteExchangeProjection`. All comparisons
below are the existing canonical maps, not additional choices of exchange data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.FiniteMateDomain

/-- The existing quotient coefficient ring, lifted to the small-site module universe.
Source: the coefficient datum in clause (4)
(blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev Coefficient {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (n : ℕ)

/-- The specified etale module mate, with no change of its construction.
Source: Stacks 07A7 and clause (4) (blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev etaleMate {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :=
  Etale.baseChange (ModuleCat.{u + 1} (Coefficient C E n)) sq.toCommSq

/-- The actual ambient finite-coefficient adjunction mate used by the operation datum.
Source: def-exchange-projection and Stacks 07A7
(blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev ambientMate {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :=
  ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (Coefficient C E n)) sq.toCommSq

/-- The canonical derived comparison inverse image, without a chosen antecedent.
Source: Stacks 09A6 and clause (4) (blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev comparison (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coefficient C E n)) T).mapDerivedCategory

/-- The specified comparison S of the sources of the two exchange maps.
Source: Stacks 09A6 and clause (4) (blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev sourceIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :=
  ProEtale.baseChangeSourceComparisonIso f g (Coefficient C E n)

/-- The specified comparison T of the targets of the two exchange maps.
Source: Stacks 09A6 and clause (4) (blueprint: lem-sf-bc-finite-mate-domain). -/
abbrev targetIso {X' X Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [QuasiCompact f'] [QuasiSeparated f'] :=
  ProEtale.baseChangeTargetComparisonIso g' f' (Coefficient C E n)

private theorem coefficient_annihilator : ((C.l ^ n : ℕ) : Coefficient C E n) = 0 := by
  apply ULift.down_injective
  change ((C.l ^ n : ℕ) : Padic.coefficientExtensionRing C.l E n) = 0
  let h := (Padic.extension_integers_dvr C.l E
    (Padic.coefficientExtensionAbsoluteValue C.l E)
    (spectralNorm_extends (K := Padic C.l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue C.l E (C.l : E) < 1 := by
    change spectralNorm (Padic C.l) E (C.l : E) < 1
    rw [show (C.l : E) = algebraMap (Padic C.l) E (C.l : Padic C.l) by simp]
    rw [spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hlm : (C.l : Padic.coefficientExtensionIntegers C.l E) ∈
      Padic.coefficientExtensionMaximalIdeal C.l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer C.l E} :
      Set (Padic.coefficientExtensionIntegers C.l E)) =
      Padic.coefficientExtensionMaximalIdeal C.l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change ((C.l ^ n : ℕ) : Padic.coefficientExtensionIntegers C.l E ⧸
    Padic.coefficientExtensionIdeal C.l E n) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal C.l E n)),
    Ideal.Quotient.eq_zero_iff_mem]
  rw [Nat.cast_pow]
  change (C.l : Padic.coefficientExtensionIntegers C.l E) ^ n ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer C.l E} :
      Set (Padic.coefficientExtensionIntegers C.l E)) ^ n
  rw [hgen]
  exact Ideal.pow_mem_pow hlm n

private theorem prime_unit (T : SixFunctorSpace D) :
    IsUnit (C.l : Γ(T.obj.left, ⊤)) := by
  classical
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hu : IsUnit (C.l : D.k) :=
    (CharP.isUnit_natCast_iff (R := D.k) D.prime).2 fun h ↦
      C.different ((Nat.prime_dvd_prime_iff_eq D.prime
        (Fact.out : C.l.Prime)).1 h).symm
  let φ : D.k →+* Γ(T.obj.left, ⊤) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ T.obj.hom.appTop).hom
  simpa only [map_natCast] using hu.map φ

private theorem conjugate_exchange
    {B H : Type*} [Category B] [Category H] {F G : B ⥤ H}
    (τ : F ⟶ G) {x y : B} (e : x ≅ y) {s t : H}
    (i : s ≅ F.obj x) (j : t ≅ G.obj x) (m : s ⟶ t) [IsIso m]
    (h : m ≫ j.hom = i.hom ≫ τ.app x) :
    IsIso (τ.app y) ∧
      τ.app y = F.map e.inv ≫ i.inv ≫ m ≫ j.hom ≫ G.map e.hom := by
  have hx : τ.app x = i.inv ≫ m ≫ j.hom := by
    apply (cancel_epi i.hom).1
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h.symm
  have hxiso : IsIso (τ.app x) := by
    rw [hx]
    infer_instance
  refine ⟨(NatTrans.isIso_app_iff_of_iso τ e).1 hxiso, ?_⟩
  calc
    τ.app y = F.map e.inv ≫ τ.app x ≫ G.map e.hom := (τ.naturality_1 e).symm
    _ = _ := by rw [hx]; simp only [Category.assoc]

/-- Finite ordinary exchange, coefficient forgetting, site comparison, and retained-witness
conjugation. In the smooth case constructibility is required of the retained antecedent;
the endpoint objects of the conclusion remain in the ambient derived category.

Source: blueprint main-20261015, prop-functor-package.proof.md, clause (4);
Stacks 0DDE, 0F09, 0D6J, 07A7 and 09A6 (blueprint: lem-sf-bc-finite-mate-domain).

Proof:
1. The extending spectral norm sends ell to a value less than one, so ell belongs
   to the recorded maximal ideal. The chosen uniformizer generates that ideal;
   hence ell^n lies in its nth power and vanishes in the coefficient quotient.
   This gives additive torsion directly, without needing finiteness of the quotient.
2. The base field has characteristic p. Since ell is prime and differs from p,
   ell is a unit in that field, and therefore in global sections on each scheme.
   Thus ell^n is a nonzero annihilator invertible on the base Y.
3. Apply the existing module-valued proper base-change theorem to the torsion ring,
   or the module-valued bounded-below smooth base-change theorem to cohomology
   sheaves killed by ell^n. Separatedness supplies quasi-separatedness, and
   quasi-compactness of both vertical edges is already among the hypotheses.
4. The coefficient-forgetting exchange theorem supplies the exact displayed abelian
   comparison equation. The canonical site-comparison theorem supplies the displayed
   S,T equation for the actual ambient mate, so its value on the comparison image is
   the composite of the inverse source comparison, the image of the etale mate, and
   the target comparison.
5. Naturality at the retained witness isomorphism and cancellation give the five-factor
   conjugation formula. Every factor is invertible, which proves the required assertion.
   The smooth argument already works for every bounded-below antecedent; in particular
   it applies to the supplied bounded constructible ones. No endpoint constructibility
   is used or asserted. -/
theorem finiteMateDomain
    (hn : 1 ≤ n)
    {X X' Y Y' : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated X'.obj.hom]
    [IsSeparated Y.obj.hom] [IsSeparated Y'.obj.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated g'.hom.left] [LocallyOfFiniteType g'.hom.left] [QuasiCompact g'.hom.left]
    [IsSeparated f'.hom.left] [LocallyOfFiniteType f'.hom.left] [QuasiCompact f'.hom.left]
    (sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (hgeom : IsProper f.hom.left ∨ Smooth g.hom.left) :
    (∀ L : DerivedCategory.Plus
        (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (Coefficient C E n))),
      IsIso ((etaleMate C E n sq).app L) ∧
      (D+(Etale.moduleAbelianForget (Coefficient C E n) Y'.obj.left).map
          ((etaleMate C E n sq).app L) ≫
        (Etale.moduleAbelianDerivedExchangeTargetIso (Coefficient C E n)
          g'.hom.left f'.hom.left L).hom =
      (Etale.moduleAbelianDerivedExchangeSourceIso (Coefficient C E n)
          f.hom.left g.hom.left L).hom ≫
        (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D+(Etale.moduleAbelianForget (Coefficient C E n) X.obj.left).obj L)) ∧
      ((comparison C E n Y'.obj.left).map
          (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app L)) ≫
        (targetIso C E n g'.hom.left f'.hom.left).hom.app L =
      (sourceIso C E n f.hom.left g.hom.left).hom.app L ≫
        (ambientMate C E n sq).app ((comparison C E n X.obj.left).obj L.obj))) ∧
    (∀ K : DerivedCategory.Plus
        (Sheaf (ProEt.topology X.obj.left) (ModuleCat.{u + 1} (Coefficient C E n))),
      ∀ W : FixedEtaleOriginWitness X.obj.left (Coefficient C E n) K,
      (IsProper f.hom.left ∨
        (Smooth g.hom.left ∧ Etale.DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} (Coefficient C E n)) X.obj.left W.complex.obj)) →
      IsIso ((ambientMate C E n sq).app K.obj) ∧
      (ambientMate C E n sq).app K.obj =
        (R(ProEtale.lowerStar (ModuleCat.{u + 1} (Coefficient C E n)) f.hom.left) ⋙
          L(ProEtale.upperStar (ModuleCat.{u + 1} (Coefficient C E n)) g.hom.left)).map
            W.iso.inv ≫
        (sourceIso C E n f.hom.left g.hom.left).inv.app W.complex ≫
        (comparison C E n Y'.obj.left).map
          (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app W.complex)) ≫
        (targetIso C E n g'.hom.left f'.hom.left).hom.app W.complex ≫
        (L(ProEtale.upperStar (ModuleCat.{u + 1} (Coefficient C E n)) g'.hom.left) ⋙
          R(ProEtale.lowerStar (ModuleCat.{u + 1} (Coefficient C E n)) f'.hom.left)).map
            W.iso.hom) := by
  have _ := hn
  let A := Coefficient C E n
  have hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hkill := coefficient_annihilator C E n
  have hnonzero : C.l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : C.l.Prime).ne_zero
  have htorsion : IsAddTorsion A := fun x ↦
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨C.l ^ n, Nat.pos_of_ne_zero hnonzero, by
      rw [nsmul_eq_mul, hkill, zero_mul]⟩
  have he (L : DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      IsIso ((etaleMate C E n sq).app L) := by
    rcases hgeom with hp | hs
    · let := hp
      have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring A
        htorsion hsq
      infer_instance
    · let := hs
      exact Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder A
        g.hom.left hsq L fun j ↦
          IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero A (C.l ^ n)
            hnonzero hkill
            (by simpa only [Nat.cast_pow] using (prime_unit C Y).pow n) _
  have hc (L : DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      (comparison C E n Y'.obj.left).map
          (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app L)) ≫
        (targetIso C E n g'.hom.left f'.hom.left).hom.app L =
      (sourceIso C E n f.hom.left g.hom.left).hom.app L ≫
        (ambientMate C E n sq).app ((comparison C E n X.obj.left).obj L.obj) :=
    ProEtale.comparison_derivedBaseChangeMap A hsq L
  constructor
  · intro L
    refine ⟨he L, ?_, hc L⟩
    simp only [etaleMate, Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact (Etale.exchange_forget_coefficients A sq L).2.2.2.2.2.2.2.2.1
  · intro K W _
    have hw := hc W.complex
    have hi := he W.complex
    have hmap : IsIso ((comparison C E n Y'.obj.left).map
        (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app W.complex))) := by
      have : IsIso (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app W.complex)) :=
        Functor.map_isIso DerivedCategory.Plus.ι _
      exact Functor.map_isIso (comparison C E n Y'.obj.left) _
    exact conjugate_exchange (ambientMate C E n sq) W.iso
      ((sourceIso C E n f.hom.left g.hom.left).app W.complex)
      ((targetIso C E n g'.hom.left f'.hom.left).app W.complex)
      ((comparison C E n Y'.obj.left).map
        (DerivedCategory.Plus.ι.map ((etaleMate C E n sq).app W.complex))) hw

end WeilConjectures.FiniteMateDomain
